/-!
# A tiny toy version of the i.MX 93 platform

A massively simplified Lean rendering of the Sockeye model of the i.MX 93 in
`sockeye/specs/nxp/imx93/src`. It follows the structure of the Sockeye code: requests travel from an
initiator through an interconnect, which implements the memory map, and through a checker of the
TRDC (Trusted Resource Domain Controller) to a sink.

What is modeled:
* one CPU core and one USB controller as initiators, both sending arbitrary memory requests,
* DRAM as the only real sink,
* a TRDC that consists of a single MRC (Memory Region Checker) in front of the DRAM.

Simplifications compared to the Sockeye model:
* Sockeye modules with `State`/`Array` instances become structures, and `mut fn`s become functions
  in the state monad. A `callee` becomes a function argument.
* `any` becomes a function argument: the arbitrary request that an initiator sends is an input of
  its `step` function.
* No MDACs (the components that attach a domain ID to each request): `System.step` attaches the
  domain ID of the initiator itself.
* No TRDC manager with memory-mapped registers: the configuration of the MRC is a plain value. No
  secure/privileged distinction and no `GLBAC` indirection either: each region directly says which
  access modes it allows.
* No MBCs, no other power domains, no other devices.

There is no connection to `ISA.lean` yet. Nothing outside of core Lean is used.
-/

namespace ToySys.Platform

/-! ## Types (`types.soc`) -/

abbrev PhysAddr := BitVec 32
abbrev Byte := BitVec 8
abbrev DomainID := BitVec 4

inductive AccessMode
  | read | write | execute
  deriving DecidableEq, Repr

structure Request where
  address : PhysAddr
  value : BitVec 32
  mode : AccessMode
  /-- Not under the control of the initiator: overwritten by `System.step`. -/
  domainId : DomainID
  deriving DecidableEq, Repr

structure Reply where
  value : BitVec 32
  ok : Bool
  deriving DecidableEq, Repr

/-- The reply to a request that was not served. Sockeye leaves the value unspecified. -/
def Reply.denied : Reply := { value := 0, ok := false }

/-- Something that serves requests and has state of type `σ` (the Sockeye interface `Handler`). -/
abbrev Handler (σ : Type) := Request → StateM σ Reply

/-! ## DRAM (`system.soc`) -/

/-- 2GB of DRAM, as bytes. -/
structure Dram where
  backing : BitVec 31 → Byte

def Dram.store (d : Dram) (a : BitVec 31) (b : Byte) : Dram :=
  { backing := fun a' => if a' = a then b else d.backing a' }

/-- The little-endian 32-bit word at byte offset `a`. -/
def Dram.loadWord (d : Dram) (a : BitVec 31) : BitVec 32 :=
  d.backing (a + 3) ++ d.backing (a + 2) ++ d.backing (a + 1) ++ d.backing a

def Dram.storeWord (d : Dram) (a : BitVec 31) (v : BitVec 32) : Dram :=
  (((d.store a (v.extractLsb' 0 8)).store (a + 1) (v.extractLsb' 8 8)).store (a + 2)
    (v.extractLsb' 16 8)).store (a + 3) (v.extractLsb' 24 8)

def Dram.request : Handler Dram := fun r => do
  let byteOff := r.address.setWidth 31
  if r.mode = .write then
    modify (·.storeWord byteOff r.value)
    return { ok := true, value := 0 }
  else
    return { ok := true, value := (← get).loadWord byteOff }

/-! ## TRDC memory region checker (`trdc_mrc.soc`) -/

/-- A region descriptor of the MRC, for one domain. `first` and `last` are both inclusive. -/
structure Region where
  first : PhysAddr
  last : PhysAddr
  valid : Bool := true
  read : Bool
  write : Bool
  execute : Bool
  deriving Repr

/-- A region is hit if it is valid and contains the address of the request. -/
def Region.isHit (g : Region) (r : Request) : Bool :=
  g.valid && g.first ≤ r.address && r.address ≤ g.last

def Region.allows (g : Region) (r : Request) : Bool :=
  match r.mode with
  | .read => g.read
  | .write => g.write
  | .execute => g.execute

/-- A Memory Region Checker: for each domain, a few region descriptors. -/
structure Mrc where
  regions : DomainID → List Region

/-- A request is allowed if it hits at least one region of its domain, and all regions that it hits
allow its access mode. -/
def Mrc.isAccessAllowed (m : Mrc) (r : Request) : Bool :=
  let hits := (m.regions r.domainId).filter (·.isHit r)
  !hits.isEmpty && hits.all (·.allows r)

/-- Forwards the requests that are allowed to `target` and denies the others. -/
def Mrc.request {σ : Type} (m : Mrc) (target : Handler σ) : Handler σ := fun r =>
  if m.isAccessAllowed r then target r else return .denied

/-! ## TRDC (`trdc.soc`) -/

/-- The whole TRDC: just one MRC, the one that sits in front of the DRAM (`mrc_n0` in Sockeye). -/
structure Trdc where
  mrc : Mrc

/-! ## Initiators (`initiators.soc`) -/

/-- The domain of the Cortex-A55 cores in the default domain assignment of the i.MX 93. -/
def Cpu.domainId : DomainID := 3

/-- One step of the CPU core: it sends the request `r`, which can be anything. -/
def Cpu.step {σ : Type} (downstream : Handler σ) (r : Request) : StateM σ Unit := do
  let _ ← downstream r

/-- The domain of USB1 in the default domain assignment of the i.MX 93. -/
def Usb.domainId : DomainID := 11

/-- One step of the USB controller: it sends the request `r`, which can be anything. -/
def Usb.step {σ : Type} (downstream : Handler σ) (r : Request) : StateM σ Unit := do
  let _ ← downstream r

/-- The memory-mapped registers of the USB controller are not modeled. -/
def Usb.request {σ : Type} : Handler σ := fun _ => return .denied

/-! ## System state (`system.soc`) -/

structure System where
  trdc : Trdc
  dram : Dram

/-- The DRAM as a handler on the whole system state. -/
def System.dramRequest : Handler System := fun r => do
  let s ← get
  let (reply, dram) := Dram.request r s.dram
  set { s with dram }
  return reply

/-! ## Interconnect (`interconnect.soc`) -/

/-- The memory map. Requests to the DRAM pass through the MRC. -/
def Interconnect.request : Handler System := fun r => do
  let a := r.address
  if 0x80000000 ≤ a then
    -- 0x80000000..0xFFFFFFFF: DRAM
    (← get).trdc.mrc.request System.dramRequest r
  else if 0x4C100000 ≤ a && a ≤ 0x4C1FFFFF then
    -- 0x4C100000..0x4C1FFFFF: USB1 Controller
    Usb.request r
  else
    -- everything else is reserved
    return .denied

/-! ## System steps (`system.soc`) -/

/-- Which initiator takes a step, and the arbitrary request that it sends. -/
inductive Step
  | cpu (r : Request)
  | usb (r : Request)

/-- One step of the system. In the absence of MDACs, this is where the domain ID of the initiator
gets attached to the request, whatever the initiator put there. -/
def System.step : Step → StateM System Unit
  | .cpu r => Cpu.step Interconnect.request { r with domainId := Cpu.domainId }
  | .usb r => Usb.step Interconnect.request { r with domainId := Usb.domainId }

def System.run (steps : List Step) (s : System) : System :=
  (steps.forM System.step s).2

/-! ## Tests (`tests/trdc_dram_protection.soc`)

Linux owns the first 256MB of DRAM, except that the 16MB after that are set aside for DMA by
devices. A USB controller that has gone rogue tries to overwrite Linux's memory. -/

def linuxFirst : PhysAddr := 0x80000000
def linuxLast : PhysAddr := 0x8FFFFFFF
def dmaFirst : PhysAddr := 0x90000000
def dmaLast : PhysAddr := 0x90FFFFFF

/-- The CPU may do anything in all of DRAM. -/
def cpuRegions : List Region :=
  [{ first := 0x80000000, last := 0xFFFFFFFF, read := true, write := true, execute := true }]

/-- A configuration that confines the USB controller to the DMA region. -/
def goodMrc : Mrc where
  regions d :=
    if d = Cpu.domainId then cpuRegions
    else if d = Usb.domainId then
      [{ first := dmaFirst, last := dmaLast, read := true, write := true, execute := false }]
    else []

/-- A configuration that lets the USB controller read and write all of DRAM. -/
def badMrc : Mrc where
  regions d :=
    if d = Cpu.domainId then cpuRegions
    else if d = Usb.domainId then
      [{ first := 0x80000000, last := 0xFFFFFFFF, read := true, write := true, execute := false }]
    else []

/-- A system with the given MRC configuration and zeroed DRAM. -/
def systemWith (mrc : Mrc) : System :=
  { trdc := { mrc }, dram := { backing := fun _ => 0 } }

/-- The USB controller writes `0xDEADBEEF` to address `a`, pretending to be in the CPU's domain. -/
def rogueUsbWrite (a : PhysAddr) : Step :=
  .usb { address := a, value := 0xDEADBEEF, mode := .write, domainId := Cpu.domainId }

def readAt (s : System) (a : PhysAddr) : BitVec 32 :=
  s.dram.loadWord (a.setWidth 31)

/-- Some addresses in Linux's memory: at both ends and in the middle. -/
def linuxProbes : List PhysAddr := [linuxFirst, 0x80001000, 0x88000000, linuxLast - 3]

/-- Whether the words at `linuxProbes` survive a rogue USB write to each of them. -/
def protectsLinux (mrc : Mrc) : Bool :=
  let s := systemWith mrc
  let s' := s.run (linuxProbes.map rogueUsbWrite)
  linuxProbes.all fun a => readAt s' a == readAt s a

/-- info: 0xdeadbeef#32 -/
#guard_msgs in
#eval readAt ((systemWith badMrc).run [rogueUsbWrite 0x80001000]) 0x80001000

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval readAt ((systemWith goodMrc).run [rogueUsbWrite 0x80001000]) 0x80001000

/-- With the good configuration, the TRDC protects Linux's memory from the rogue USB controller. -/
theorem goodMrc_protects_linux : protectsLinux goodMrc = true := by native_decide

/-- With the bad configuration, it does not. -/
theorem badMrc_does_not_protect_linux : protectsLinux badMrc = false := by native_decide

/-- The good configuration still lets the USB controller do DMA in the region set aside for it. -/
theorem goodMrc_allows_dma :
    readAt ((systemWith goodMrc).run [rogueUsbWrite dmaFirst]) dmaFirst = 0xDEADBEEF := by
  native_decide

/-- The good configuration does not get in the way of the CPU. -/
theorem goodMrc_allows_cpu :
    readAt ((systemWith goodMrc).run
      [.cpu { address := linuxFirst, value := 42, mode := .write, domainId := 0 }]) linuxFirst
      = 42 := by
  native_decide

/-- A USB write just past the end of the DMA region is blocked. -/
theorem goodMrc_blocks_past_dma :
    readAt ((systemWith goodMrc).run [rogueUsbWrite (dmaLast + 1)]) (dmaLast + 1) = 0 := by
  native_decide

end ToySys.Platform
