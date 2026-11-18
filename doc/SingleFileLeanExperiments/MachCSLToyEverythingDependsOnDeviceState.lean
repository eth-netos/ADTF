/-!
# A toy MachCSL: machine state, devices, and general-purpose functions

## Question

MachCSL (`xv6iris/MachCSL`, the RISC-V framework behind the xv6
verification) has ISA state, which is the same on all platforms, and device
state, which differs between platforms. Does it keep the two apart? In
particular, can the files that verify general-purpose (libc-style)
functions avoid importing, even transitively, the files that define the
devices?

## Answer

No. The device models are modular: each one is a `DevSig` over its own
state, and only `Dev/Fabric.lean` knows the board's fixed `DevId`. But
`Lang.lean` imports the fabric and defines the one concrete `MState`, with
`devs : DevStates`. The ghost state in `Resources.lean` (`devName`,
`devInterp`) and the WP in `Wp.lean` are built on that state. Specs avoid
devices only in what they say, not in what they import: `Xv6.SpecMemset`
mentions only registers and memory, yet its import closure reaches
`Dev.Fabric`, `Dev.Uart` and `Dev.Virtio`. The ISA layer also fixes
platform constants (`NCPU`, the DRAM bank, the Sail platform
configuration). Supporting several platforms would need `Lang`, `Resources`
and `Wp` to be generic over a platform interface, as in `Open` below. The
existing device models could be used unchanged as an instance of it.

The question is whether a proof of a general-purpose function (here
`store1`, a one-instruction `*p = v`) can avoid depending, even
transitively, on the board's device models.

* `Closed` follows MachCSL's design: one concrete `MState` with a field
  `devs : DevStates`. `DevStates` is defined over the board's fixed `DevId`
  in the fabric file (`MachCSL/Dev/Fabric.lean`). The step relation
  (`MachCSL/Lang.lean`) and the program logic (`MachCSL/Wp.lean`) are
  stated over this `MState`, so every specification, including the one for
  `memset`, sits on top of the fabric.
* `Open` is the modularization asked about. The program logic and the
  general-purpose proof are generic over a `Platform`, which gives a device
  state type, a bus decode, and one law saying that RAM is not MMIO. The
  board is defined after the proof and instantiates it.

In a single Lean file, a declaration can only depend on earlier ones. So
`Open.store1_ok` cannot depend on `Open.Board`, which comes after it. The
`-- file:` comments name the files that each part stands for.
-/

namespace Toy

abbrev Addr := Nat
abbrev Byte := Nat

/-! ## The ISA, the same on every platform
-- file: the Sail model (`LeanRV64D`), here a 3-instruction toy -/

/-- `sb rs, [rb]` stores register `rs` at the address in register `rb`;
`ret` jumps to register 1. -/
inductive Instr where
  | sb (rs rb : Nat)
  | li (rd k : Nat)
  | ret

structure Regs where
  pc : Nat
  x : Nat → Nat

def Regs.set (r : Regs) (i v : Nat) : Regs :=
  { r with x := fun j => if j = i then v else r.x j }

abbrev Code := Nat → Option Instr

/-! ## Part 1: the closed design of MachCSL -/

namespace Closed

/-! -- file: `MachCSL/Dev/DevIds.lean`: the board's device instances -/
inductive DevId where
  | uart
  | disk
  deriving DecidableEq

/-! -- file: `MachCSL/Dev/DevLang.lean`: what a device model provides.
In MachCSL a `DevSig` also has a `body` program in the device language
`DevM`, tasks, an interrupt level and a reset. -/
structure DevSig where
  S : Type
  read : S → Nat → Option (Byte × S)
  write : S → Nat → Byte → Option S

/-! -- files: `MachCSL/Dev/Uart.lean`, `MachCSL/Dev/Virtio.lean`. Each
device is written against its own state type and does not see the others. -/
structure UartSt where
  wire : List Byte

def uartSig : DevSig where
  S := UartSt
  read s _ := some (0, s)
  write s off b := if off = 0 then some ⟨s.wire ++ [b]⟩ else none

def diskSig : DevSig where
  S := Nat → Byte
  read s off := some (s off, s)
  write _ _ _ := none

/-! -- file: `MachCSL/Dev/Fabric.lean`, the one place that knows every
device -/
def devSig : DevId → DevSig
  | .uart => uartSig
  | .disk => diskSig

structure DevStates where
  st : (d : DevId) → (devSig d).S

def DevStates.set (ds : DevStates) (d : DevId) (s : (devSig d).S) :
    DevStates :=
  ⟨fun d' => if h : d' = d then h ▸ s else ds.st d'⟩

def uartBase : Nat := 0x10000000
def diskBase : Nat := 0x10001000
def devBound : Nat := 0x80000000

def devDecode (a : Addr) : Option (DevId × Nat) :=
  if uartBase ≤ a ∧ a < uartBase + 8 then some (.uart, a - uartBase)
  else if diskBase ≤ a ∧ a < diskBase + 0x1000 then
    some (.disk, a - diskBase)
  else none

def devWrite (ds : DevStates) (a : Addr) (b : Byte) : Option DevStates :=
  match devDecode a with
  | some (d, off) => ((devSig d).write (ds.st d) off b).map (ds.set d)
  | none => none

/-! -- file: `MachCSL/TsoMem.lean`. The DRAM bank is a constant here, and
so is `NCPU := 8` in MachCSL. -/
def ramBase : Nat := 0x80000000

/-! -- file: `MachCSL/Lang.lean`, which imports `Dev.Fabric`. This is the
only machine state, so it fixes the board. -/
structure MState where
  regs : Regs
  /-- A byte has a value only if it is DRAM (`MachCSL.memRam`). -/
  mem : Addr → Option Byte
  devs : DevStates

/-- The bus decode of a store, as in `MachCSL.evStep`'s `memWrite` arms:
an address below `devBound` is MMIO, otherwise the byte must exist in
RAM. -/
def store (σ : MState) (a : Addr) (b : Byte) : Option MState :=
  if a < devBound then
    (devWrite σ.devs a b).map fun ds => { σ with devs := ds }
  else (σ.mem a).map fun _ =>
    { σ with mem := fun a' => if a' = a then some b else σ.mem a' }

def step (code : Code) (σ : MState) : Option MState :=
  match code σ.regs.pc with
  | some (.sb rs rb) =>
      (store σ (σ.regs.x rb) (σ.regs.x rs)).map fun σ' =>
        { σ' with regs := { σ'.regs with pc := σ.regs.pc + 4 } }
  | some (.li rd k) =>
      some { σ with regs := { σ.regs.set rd k with pc := σ.regs.pc + 4 } }
  | some .ret => some { σ with regs := { σ.regs with pc := σ.regs.x 1 } }
  | none => none

/-! -- file: `MachCSL/Wp.lean`. The program logic is stated over the one
`MState`. In MachCSL it is an Iris WP whose state interpretation
`machInterp` includes `devInterp σ.devs`, a ghost variable per `DevId`. -/
inductive Eventually (code : Code) (Q : MState → Prop) : MState → Prop
  | done {σ} : Q σ → Eventually code Q σ
  | step {σ σ'} : _root_.Toy.Closed.step code σ = some σ' →
      Eventually code Q σ' → Eventually code Q σ

/-- The RAM rule: an owned byte is not MMIO. This needs `ramBase ≤
devBound` from the fabric (`MachCSL.not_devBytes_of_ramBytes`). -/
theorem store_ram (σ : MState) (a b old : Byte) (hr : ramBase ≤ a)
    (h : σ.mem a = some old) :
    store σ a b = some { σ with
      mem := fun a' => if a' = a then some b else σ.mem a' } := by
  have : ¬ a < devBound := Nat.not_lt.mpr hr
  simp [store, this, h]

/-! -- files: `Xv6/SpecMemset.lean`, `Xv6/ProofMemset.lean`. The
specification never names a device, but `MState` and `Eventually` come
from `Lang`, which imports the fabric and so every device model. -/
def store1 (f : Nat) : Code := fun pc =>
  if pc = f then some (.sb 2 0) else if pc = f + 4 then some .ret else none

theorem store1_ok (f : Nat) (σ : MState) (old : Byte)
    (hpc : σ.regs.pc = f) (hr : ramBase ≤ σ.regs.x 0)
    (hm : σ.mem (σ.regs.x 0) = some old) :
    Eventually (store1 f) (fun σ' =>
      σ'.regs.pc = σ.regs.x 1 ∧
      σ'.mem (σ.regs.x 0) = some (σ.regs.x 2) ∧
      σ'.devs = σ.devs) σ := by
  let σ1 : MState := { σ with
    mem := fun a' => if a' = σ.regs.x 0 then some (σ.regs.x 2) else σ.mem a'
    regs := { σ.regs with pc := f + 4 } }
  refine .step (σ' := σ1) ?_ (.step (σ' :=
    { σ1 with regs := { σ1.regs with pc := σ.regs.x 1 } }) ?_ (.done ?_))
  · simp [σ1, step, store1, hpc, store_ram σ _ _ old hr hm]
  · simp [σ1, step, store1]
  · simp [σ1]

end Closed

/-! ## Part 2: the open design (not what MachCSL does) -/

namespace Open

/-! -- file: a platform interface, which imports only the ISA -/
class Platform where
  DevState : Type
  /-- Whether an address is answered by a device (MMIO). -/
  isDev : Addr → Bool
  devWrite : DevState → Addr → Byte → Option DevState
  /-- Addresses that may hold RAM bytes. -/
  isRam : Addr → Prop
  /-- RAM is not MMIO; the only fact generic proofs need about devices. -/
  ram_not_dev : ∀ a, isRam a → isDev a = false

/-! -- file: the generic machine state and step relation (cf.
`MachCSL/Lang.lean` without the `Dev.Fabric` import) -/
structure MState (P : Platform) where
  regs : Regs
  mem : Addr → Option Byte
  devs : P.DevState

variable {P : Platform}

def store (σ : MState P) (a : Addr) (b : Byte) : Option (MState P) :=
  if P.isDev a then
    (P.devWrite σ.devs a b).map fun ds => { σ with devs := ds }
  else (σ.mem a).map fun _ =>
    { σ with mem := fun a' => if a' = a then some b else σ.mem a' }

def step (code : Code) (σ : MState P) : Option (MState P) :=
  match code σ.regs.pc with
  | some (.sb rs rb) =>
      (store σ (σ.regs.x rb) (σ.regs.x rs)).map fun σ' =>
        { σ' with regs := { σ'.regs with pc := σ.regs.pc + 4 } }
  | some (.li rd k) =>
      some { σ with regs := { σ.regs.set rd k with pc := σ.regs.pc + 4 } }
  | some .ret => some { σ with regs := { σ.regs with pc := σ.regs.x 1 } }
  | none => none

/-! -- file: the generic program logic (cf. `MachCSL/Wp.lean`) -/
inductive Eventually (code : Code) (Q : MState P → Prop) :
    MState P → Prop
  | done {σ} : Q σ → Eventually code Q σ
  | step {σ σ'} : _root_.Toy.Open.step code σ = some σ' →
      Eventually code Q σ' → Eventually code Q σ

theorem store_ram (σ : MState P) (a b old : Byte) (hr : P.isRam a)
    (h : σ.mem a = some old) :
    store σ a b = some { σ with
      mem := fun a' => if a' = a then some b else σ.mem a' } := by
  simp [store, P.ram_not_dev a hr, h]

/-! -- file: the general-purpose function, which imports the three files
above and no device -/
def store1 (f : Nat) : Code := fun pc =>
  if pc = f then some (.sb 2 0) else if pc = f + 4 then some .ret else none

theorem store1_ok (f : Nat) (σ : MState P) (old : Byte)
    (hpc : σ.regs.pc = f) (hr : P.isRam (σ.regs.x 0))
    (hm : σ.mem (σ.regs.x 0) = some old) :
    Eventually (store1 f) (fun σ' =>
      σ'.regs.pc = σ.regs.x 1 ∧
      σ'.mem (σ.regs.x 0) = some (σ.regs.x 2) ∧
      σ'.devs = σ.devs) σ := by
  let σ1 : MState P := { σ with
    mem := fun a' => if a' = σ.regs.x 0 then some (σ.regs.x 2) else σ.mem a'
    regs := { σ.regs with pc := f + 4 } }
  refine .step (σ' := σ1) ?_ (.step (σ' :=
    { σ1 with regs := { σ1.regs with pc := σ.regs.x 1 } }) ?_ (.done ?_))
  · simp [σ1, step, store1, hpc, store_ram σ _ _ old hr hm]
  · simp [σ1, step, store1]
  · simp [σ1]

/-! -- file: one board. Its device models could be MachCSL's unchanged:
`Closed.devSig`, `Closed.DevStates` and `Closed.devWrite` fit as they are.
Only the step relation and the logic above had to become generic. -/
instance Board : Platform where
  DevState := Closed.DevStates
  isDev a := decide (a < Closed.devBound)
  devWrite := Closed.devWrite
  isRam a := Closed.ramBase ≤ a
  ram_not_dev _ h := decide_eq_false (Nat.not_lt.mpr h)

/-! -- file: the OS on this board uses the generic proof -/
example (f : Nat) (σ : MState Board) (old : Byte) (hpc : σ.regs.pc = f)
    (hr : Closed.ramBase ≤ σ.regs.x 0)
    (hm : σ.mem (σ.regs.x 0) = some old) :
    Eventually (store1 f) (fun σ' =>
      σ'.regs.pc = σ.regs.x 1 ∧
      σ'.mem (σ.regs.x 0) = some (σ.regs.x 2) ∧
      σ'.devs = σ.devs) σ :=
  store1_ok f σ old hpc hr hm

end Open

end Toy
