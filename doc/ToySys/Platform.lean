/-!
# A tiny toy version of the i.MX 93 platform

A massively simplified Lean rendering of the Sockeye model of the i.MX 93 in
`sockeye/specs/nxp/imx93/src`. It follows the structure of the Sockeye code: requests travel from an
initiator through an interconnect, which implements the memory map, and through a checker of the
TRDC (Trusted Resource Domain Controller) to a sink.

What is modeled:
* one CPU core and one USB controller as initiators, both sending arbitrary memory requests,
* DRAM as the only real sink,
* a TRDC that consists of a manager, which holds the memory-mapped configuration registers, and a
  single MRC (Memory Region Checker) in front of the DRAM.

Simplifications compared to the Sockeye model:
* Sockeye modules with `State`/`Array` instances become structures, and `mut fn`s become functions
  in the state monad. A `callee` becomes a function argument.
* `any` becomes a function argument: the arbitrary request that an initiator sends is an input of
  its `step` function.
* No MDACs (the components that attach a domain ID to each request): `System.step` attaches the
  domain ID of the initiator itself.
* The TRDC manager has only the registers that the MRC needs: `TRDC_CR`, `MRC0_GLBACn` and
  `MRC0_DOMd_RGDr_Ww`, at the offsets and with the layout that they have in the NICMIX TRDC, but
  without lock bits and read-only registers.
* No secure/privileged distinction: of each `GLBAC` register, only the three bits for nonsecure user
  access are used, and the `NSE` bit of a region is ignored.
* No MBCs. The one thing that an MBC is needed for here, keeping devices away from the registers of
  the TRDC manager, is a hard-wired check in the interconnect.
* No other power domains, no other devices.

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

/-! ## TRDC manager (`trdc_mgr.soc`) -/

/-- A byte offset into the 128KB register block of the TRDC manager. -/
abbrev RegisterOffset := BitVec 17

/-- The TRDC manager holds the configuration registers: one 32-bit value per 4 bytes of its
register block. Out of reset, all of them are zero. -/
structure TrdcMgr where
  rawRegs : BitVec 15 → BitVec 32

namespace TrdcMgr

/-- The base address of the TRDC manager of the NICMIX domain. -/
def baseAddress : PhysAddr := 0x49010000

/-- Where the registers of the MRCs start within the register block. -/
def mrcBase : RegisterOffset := 0x18000

/-- `TRDC_CR`, the control register. Its bit 15 is `GVLDR`, the global valid bit of the MRCs. -/
def offset_TRDC_CR : RegisterOffset := 0

/-- `MRC0_GLBACn`, the global access control registers of MRC 0, for `n < 8`. Bits 2, 1 and 0 say
whether nonsecure user read, write and execute accesses are allowed. -/
def offset_MRC0_GLBACn (n : RegisterOffset) : RegisterOffset :=
  mrcBase + 0x20 + n * 4

/-- `MRC0_DOMd_RGDr_Ww`, word `w < 2` of region descriptor `r < 16` of domain `d < 16` of MRC 0.
* Word 0: bits 31-14 are the upper bits of the start address, bits 2-0 are `MRACSEL`, the index of
  the `GLBAC` register that applies.
* Word 1: bits 31-14 are the upper bits of the end address, bit 0 is the valid bit. -/
def offset_MRC0_DOMd_RGDr_Ww (d r w : RegisterOffset) : RegisterOffset :=
  mrcBase + 0x40 + d * 0x100 + r * 8 + w * 4

/-- Whether there is a register at this offset. -/
def isRegister (o : RegisterOffset) : Bool :=
  let rel := o - mrcBase
  let lowByte := rel.extractLsb' 0 8
  o.extractLsb' 0 2 == 0 &&
    (o == offset_TRDC_CR ||
     -- MRC0_GLBACn
     (mrcBase ≤ o && rel < 0x100 && 0x20 ≤ lowByte && lowByte ≤ 0x3F) ||
     -- MRC0_DOMd_RGDr_Ww
     (mrcBase ≤ o && rel < 0x1000 && 0x40 ≤ lowByte && lowByte ≤ 0xBF))

def read32 (g : TrdcMgr) (o : RegisterOffset) : BitVec 32 :=
  g.rawRegs (o.extractLsb' 2 15)

def write32 (g : TrdcMgr) (o : RegisterOffset) (v : BitVec 32) : TrdcMgr :=
  { rawRegs := fun i => if i = o.extractLsb' 2 15 then v else g.rawRegs i }

/-- Reads and writes of the memory-mapped registers. -/
def request : Handler TrdcMgr := fun r => do
  let o : RegisterOffset := (r.address - baseAddress).setWidth 17
  if !isRegister o then
    return .denied
  else if r.mode = .write then
    modify (·.write32 o r.value)
    return { ok := true, value := 0 }
  else
    return { ok := true, value := (← get).read32 o }

end TrdcMgr

/-! ## TRDC memory region checker (`trdc_mrc.soc`) -/

/-- A decoded region descriptor. `first` and `last` are both inclusive. -/
structure Region where
  first : PhysAddr
  last : PhysAddr
  valid : Bool
  /-- The index of the `GLBAC` register that says which accesses are allowed. -/
  mracsel : BitVec 3
  deriving Repr

namespace Mrc

/-- The domain that may access everything while the TRDC is not enabled yet (implementation
defined; on the i.MX 93 it is the domain of the Cortex-A55 cores). -/
def allowedDefaultDid : DomainID := 3

/-- Reads and decodes region descriptor `r` of domain `d` from the registers. Regions are aligned to
16KB: the lower 14 bits of the start address are zeros and those of the end address are ones. -/
def region (g : TrdcMgr) (d : DomainID) (r : Nat) : Region :=
  let w0 := g.read32 (TrdcMgr.offset_MRC0_DOMd_RGDr_Ww (d.setWidth 17) (.ofNat 17 r) 0)
  let w1 := g.read32 (TrdcMgr.offset_MRC0_DOMd_RGDr_Ww (d.setWidth 17) (.ofNat 17 r) 1)
  { first := w0 &&& 0xFFFFC000
    last := w1 ||| 0x00003FFF
    valid := w1.getLsbD 0
    mracsel := w0.extractLsb' 0 3 }

/-- A region is hit if it is valid and contains the address of the request. -/
def isRegionHit (g : Region) (r : Request) : Bool :=
  g.valid && g.first ≤ r.address && r.address ≤ g.last

def isAllowedByGlbac (glbac : BitVec 32) (r : Request) : Bool :=
  match r.mode with
  | .read => glbac.getLsbD 2
  | .write => glbac.getLsbD 1
  | .execute => glbac.getLsbD 0

def isAccessAllowedByRegion (g : TrdcMgr) (rg : Region) (r : Request) : Bool :=
  isAllowedByGlbac (g.read32 (TrdcMgr.offset_MRC0_GLBACn (rg.mracsel.setWidth 17))) r

/-- A request is allowed if it hits at least one of the 16 regions of its domain, and all regions
that it hits allow its access mode. -/
def isAccessAllowed (g : TrdcMgr) (r : Request) : Bool :=
  let hits := ((List.range 16).map (region g r.domainId)).filter (isRegionHit · r)
  !hits.isEmpty && hits.all (isAccessAllowedByRegion g · r)

/-- Forwards the requests that are allowed to `target` and denies the others. As long as `GVLDR` is
not set, the TRDC is in deny-by-default mode, where only one domain is allowed. -/
def request {σ : Type} (g : TrdcMgr) (target : Handler σ) : Handler σ := fun r =>
  let gvldr := (g.read32 TrdcMgr.offset_TRDC_CR).getLsbD 15
  let allowed := if gvldr then isAccessAllowed g r else r.domainId == allowedDefaultDid
  if allowed then target r else return .denied

end Mrc

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
  trdcMgr : TrdcMgr
  dram : Dram

/-- The DRAM as a handler on the whole system state. -/
def System.dramRequest : Handler System := fun r => do
  let s ← get
  let (reply, dram) := Dram.request r s.dram
  set { s with dram }
  return reply

/-- The TRDC manager as a handler on the whole system state. -/
def System.trdcMgrRequest : Handler System := fun r => do
  let s ← get
  let (reply, trdcMgr) := TrdcMgr.request r s.trdcMgr
  set { s with trdcMgr }
  return reply

/-! ## Interconnect (`interconnect.soc`) -/

/-- The memory map. Requests to the DRAM pass through the MRC. -/
def Interconnect.request : Handler System := fun r => do
  let a := r.address
  if 0x80000000 ≤ a then
    -- 0x80000000..0xFFFFFFFF: DRAM
    Mrc.request (← get).trdcMgr System.dramRequest r
  else if 0x4C100000 ≤ a && a ≤ 0x4C1FFFFF then
    -- 0x4C100000..0x4C1FFFFF: USB1 Controller
    Usb.request r
  else if 0x49010000 ≤ a && a ≤ 0x4902FFFF then
    -- 0x49010000..0x4902FFFF: NICMIX TRDC Manager.
    -- On the real chip, an MBC decides who may access it; here, only the CPU may.
    if r.domainId = Cpu.domainId then System.trdcMgrRequest r else return .denied
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
devices. The CPU configures the TRDC by writing to its memory-mapped registers. Then a USB
controller that has gone rogue tries to overwrite Linux's memory. -/

def linuxFirst : PhysAddr := 0x80000000
def linuxLast : PhysAddr := 0x8FFFFFFF
def dmaFirst : PhysAddr := 0x90000000
def dmaLast : PhysAddr := 0x90FFFFFF

/-- The system out of reset: all TRDC registers and all of DRAM are zero. -/
def resetSystem : System :=
  { trdcMgr := { rawRegs := fun _ => 0 }, dram := { backing := fun _ => 0 } }

def cpuWrite (a : PhysAddr) (v : BitVec 32) : Step :=
  .cpu { address := a, value := v, mode := .write, domainId := 0 }

/-- The address of a TRDC register. -/
def regAddr (o : RegisterOffset) : PhysAddr :=
  TrdcMgr.baseAddress + o.setWidth 32

/-- The register writes that set up region `r` of domain `d` to cover `first` to `last` (which have
to be 16KB-aligned), with the access rights in `MRC0_GLBAC<mracsel>`, and mark it valid. -/
def setRegion (d : DomainID) (r : RegisterOffset) (first last : PhysAddr) (mracsel : BitVec 3) :
    List Step :=
  [ cpuWrite (regAddr (TrdcMgr.offset_MRC0_DOMd_RGDr_Ww (d.setWidth 17) r 0))
      ((first &&& 0xFFFFC000) ||| mracsel.setWidth 32),
    cpuWrite (regAddr (TrdcMgr.offset_MRC0_DOMd_RGDr_Ww (d.setWidth 17) r 1))
      ((last &&& 0xFFFFC000) ||| 1) ]

/-- The register writes that are the same in both configurations: `GLBAC0` allows read, write and
execute, `GLBAC1` allows read and write, and the CPU gets all of DRAM with the rights of `GLBAC0`. -/
def commonConfig : List Step :=
  [ cpuWrite (regAddr (TrdcMgr.offset_MRC0_GLBACn 0)) 0b111,
    cpuWrite (regAddr (TrdcMgr.offset_MRC0_GLBACn 1)) 0b110 ] ++
  setRegion Cpu.domainId 0 0x80000000 0xFFFFFFFF 0

/-- Sets `GVLDR` in `TRDC_CR`, which ends deny-by-default mode and makes the regions take effect. -/
def enableTrdc : List Step :=
  [cpuWrite (regAddr TrdcMgr.offset_TRDC_CR) 0x8000]

/-- A configuration that confines the USB controller to the DMA region. -/
def goodConfig : List Step :=
  commonConfig ++ setRegion Usb.domainId 0 dmaFirst dmaLast 1 ++ enableTrdc

/-- A configuration that lets the USB controller read and write all of DRAM. -/
def badConfig : List Step :=
  commonConfig ++ setRegion Usb.domainId 0 0x80000000 0xFFFFFFFF 1 ++ enableTrdc

/-- The USB controller writes `0xDEADBEEF` to address `a`, pretending to be in the CPU's domain. -/
def rogueUsbWrite (a : PhysAddr) : Step :=
  .usb { address := a, value := 0xDEADBEEF, mode := .write, domainId := Cpu.domainId }

/-- The same request, but sent by the USB controller. -/
def asUsb : Step → Step
  | .cpu r => .usb r
  | .usb r => .usb r

def readAt (s : System) (a : PhysAddr) : BitVec 32 :=
  s.dram.loadWord (a.setWidth 31)

/-- Some addresses in Linux's memory: at both ends and in the middle. -/
def linuxProbes : List PhysAddr := [linuxFirst, 0x80001000, 0x88000000, linuxLast - 3]

/-- Whether, after the steps `config`, the words at `linuxProbes` survive the steps `prelude`
followed by a rogue USB write to each of them. -/
def protectsLinux (config : List Step) (prelude : List Step := []) : Bool :=
  let s := resetSystem.run config
  let s' := s.run (prelude ++ linuxProbes.map rogueUsbWrite)
  linuxProbes.all fun a => readAt s' a == readAt s a

/-- info: 0xdeadbeef#32 -/
#guard_msgs in
#eval readAt (resetSystem.run (badConfig ++ [rogueUsbWrite 0x80001000])) 0x80001000

/-- info: 0x00000000#32 -/
#guard_msgs in
#eval readAt (resetSystem.run (goodConfig ++ [rogueUsbWrite 0x80001000])) 0x80001000

/-- The region descriptor that `goodConfig` leaves in the registers for the USB controller. -/
def goodUsbRegion : Region :=
  Mrc.region (resetSystem.run goodConfig).trdcMgr Usb.domainId 0

/--
info: { first := 0x90000000#32, last := 0x90ffffff#32, valid := true, mracsel := 0x1#3 }
-/
#guard_msgs in
#eval goodUsbRegion

/-- With the good configuration, the TRDC protects Linux's memory from the rogue USB controller. -/
theorem goodConfig_protects_linux : protectsLinux goodConfig = true := by native_decide

/-- With the bad configuration, it does not. -/
theorem badConfig_does_not_protect_linux : protectsLinux badConfig = false := by native_decide

/-- Out of reset, before any configuration, deny-by-default mode protects Linux's memory too. -/
theorem reset_protects_linux : protectsLinux [] = true := by native_decide

/-- The USB controller cannot help itself by writing the bad configuration to the TRDC registers. -/
theorem usb_cannot_reconfigure :
    protectsLinux goodConfig (prelude := badConfig.map asUsb) = true := by native_decide

/-- The good configuration still lets the USB controller do DMA in the region set aside for it. -/
theorem goodConfig_allows_dma :
    readAt (resetSystem.run (goodConfig ++ [rogueUsbWrite dmaFirst])) dmaFirst = 0xDEADBEEF := by
  native_decide

/-- The good configuration does not get in the way of the CPU. -/
theorem goodConfig_allows_cpu :
    readAt (resetSystem.run (goodConfig ++ [cpuWrite linuxFirst 42])) linuxFirst = 42 := by
  native_decide

/-- A USB write just past the end of the DMA region is blocked. -/
theorem goodConfig_blocks_past_dma :
    readAt (resetSystem.run (goodConfig ++ [rogueUsbWrite (dmaLast + 1)])) (dmaLast + 1) = 0 := by
  native_decide

end ToySys.Platform
