/-!
# A toy MachCSL: how devices become separation-logic resources

This file gives the Lean gist of Figure 3 of the xv6 verification paper,
"MachCSL's model of system execution (left, §3) and the CSL representation
of it (right, §4 and §5)". Like MachCSL, it is closed-world: the board's
devices are fixed (cf. `MachCSL/Dev/Fabric.lean`).

* Left of the figure, "all of the state": `MState` holds every hart's
  registers, the shared memory and every device's state
  (`MachCSL.MState`). Harts and devices are threads of one language
  (`MachCSL.Expr`: `hart`, `dev`, `power`): `hartSb` is a hart's step,
  `diskDma` is the disk's step, which writes RAM by DMA.
* Right of the figure, "proof over partial state": every piece of state is
  a `Cell`, and an assertion holds of a footprint, the set of cells it owns.
  `regPt`, `memPt` and `devPt` own one register, one byte and one whole
  device, and `∗` splits a footprint into disjoint parts. So a device is a
  resource of the same kind as a memory byte, and the two can be starred.
* In MachCSL, these are Iris ghost resources whose authoritative parts sit
  in the state interpretation, itself a star of all of them:
  `eraInterp E st := regs ∗ genHeapInterp ∗ memModelAt ∗ devInterpAt`.
  Proofs hold the fragments: `regPointsTo`, TSO points-to `pa ↦ H`, and
  `devFrag d s`, a ghost variable over the whole state of device `d`.
  Here an assertion instead reads its cells directly from the state,
  so the fragments agree with the machine by construction.
* A device's resource lives in an invariant, starred with whatever the
  driver protocol needs: `devInvR N d R := inv N (∃ s, devFrag d s ∗ R s)`.
  For the disk, xv6's `R` is `diskProto`, which stars, among ghost state,
  the RAM of the virtio rings (`availLease`, `usedIdxCell`), because the
  device thread reads and writes them by DMA. Here: `diskBody`.
* Every step must preserve the invariant together with an arbitrary frame
  `R` (all other threads' resources and invariants): the device thread
  (`wpDev_localO`) in `disk_dma_ok`, and a hart's MMIO store, which opens
  the invariant (`devWriteAU`, `swp_sail_mem_write_dev`), in
  `hart_notify_ok`. A RAM store needs no invariant: `hart_ram_ok`.
* "CSL soundness" turns resources back into facts about the real state:
  `disk_buf_holds`.

This toy leaves out TSO (MachCSL's memory is a log of writes with per-hart
views), ghost state of the OS (files, processes), fractions, invariant
masks and later modalities, eras and power, and the PLIC wires.
-/

namespace ToySep

abbrev Byte := Nat
abbrev Addr := Nat
abbrev CPU := Fin 2

inductive Reg where
  | pc | a0 | a1
  deriving DecidableEq

/-! ## Left of Figure 3: the whole machine, with the board's devices -/

inductive DevId where
  | uart | disk | plic
  deriving DecidableEq

structure UartSt where
  tx : List Byte
  wire : List Byte

structure DiskSt where
  /-- The driver has notified the disk, so a DMA transfer is due. -/
  pending : Bool
  block : Byte

def DevSt : DevId → Type
  | .uart => UartSt
  | .disk => DiskSt
  | .plic => Nat → Bool

structure MState where
  regs : CPU → Reg → Nat
  mem : Addr → Byte
  devs : (d : DevId) → DevSt d

/-- The UART's transmit holding register. -/
def uartThr : Addr := 0x10000000
def diskNotify : Addr := 0x10001050
def ramBase : Addr := 0x80000000
/-- The RAM buffer that the disk fills by DMA. -/
def diskBuf : Addr := 0x80001000

def devDecode (a : Addr) : Option (DevId × Nat) :=
  if a = uartThr then some (.uart, 0)
  else if a = diskNotify then some (.disk, 0)
  else none

/-- The device models' MMIO stores (`DevSig.write`). -/
def devWrite : (d : DevId) → DevSt d → Nat → Byte → Option (DevSt d)
  | .uart, s, 0, b => some (⟨s.tx ++ [b], s.wire⟩ : UartSt)
  | .disk, s, 0, _ => some (⟨true, s.block⟩ : DiskSt)
  | _, _, _, _ => none

def MState.setDev (st : MState) (d : DevId) (s : DevSt d) : MState :=
  { st with devs := fun e => if h : e = d then h ▸ s else st.devs e }

def MState.setMem (st : MState) (a : Addr) (b : Byte) : MState :=
  { st with mem := fun x => if x = a then b else st.mem x }

def MState.setPc (st : MState) (cpu : CPU) (v : Nat) : MState :=
  { st with regs := fun c r => if c = cpu ∧ r = .pc then v else st.regs c r }

/-- A store on the bus (`MachCSL.evStep`, `memWrite`): MMIO or RAM. -/
def MState.store (st : MState) (a : Addr) (b : Byte) : Option MState :=
  match devDecode a with
  | some (d, off) => (devWrite d (st.devs d) off b).map (st.setDev d)
  | none => if ramBase ≤ a then some (st.setMem a b) else none

/-- Hart `cpu` executes `sb a1, 0(a0)`. -/
def hartSb (st : MState) (cpu : CPU) : Option MState :=
  (st.store (st.regs cpu .a0) (st.regs cpu .a1)).map
    (·.setPc cpu (st.regs cpu .pc + 4))

/-- One step of the disk's thread: copy the block into RAM by DMA. -/
def diskDma (st : MState) : Option MState :=
  let s : DiskSt := st.devs .disk
  if s.pending then
    some ((st.setMem diskBuf s.block).setDev .disk
      (⟨false, s.block⟩ : DiskSt))
  else none

/-! ## Right of Figure 3: resources and the separating star -/

inductive Cell where
  | reg (c : CPU) (r : Reg)
  | mem (a : Addr)
  | dev (d : DevId)
  deriving DecidableEq

def CellVal : Cell → Type
  | .reg .. => Nat
  | .mem _ => Byte
  | .dev d => DevSt d

def MState.val (st : MState) : (c : Cell) → CellVal c
  | .reg c r => st.regs c r
  | .mem a => st.mem a
  | .dev d => st.devs d

/-- A footprint (`Fp`): the cells that a resource owns. -/
abbrev Fp := Cell → Bool

def Fp.only (c : Cell) : Fp := fun e => decide (e = c)
def Fp.union (m n : Fp) : Fp := fun c => m c || n c
/-- Disjointness (`Disj`) of two footprints. -/
def Fp.Disj (m n : Fp) : Prop := ∀ c, m c = true → n c = false

/-- An assertion (`Assn`) holds of a footprint in a machine state. -/
abbrev Assn := Fp → MState → Prop

def star (P Q : Assn) : Assn := fun m st =>
  ∃ m1 m2, m1.Disj m2 ∧ m = m1.union m2 ∧ P m1 st ∧ Q m2 st

infixr:35 " ∗ " => star

/-- `P` reads only the cells of its footprint. Every Iris resource
predicate is local in this sense, so frames are assumed local. -/
def Local (P : Assn) : Prop :=
  ∀ m st1 st2, (∀ c, m c = true → st1.val c = st2.val c) →
    P m st1 → P m st2

def regPt (c : CPU) (r : Reg) (v : Nat) : Assn := fun m st =>
  m = .only (.reg c r) ∧ st.regs c r = v

def memPt (a : Addr) (v : Byte) : Assn := fun m st =>
  m = .only (.mem a) ∧ st.mem a = v

def devPt (d : DevId) (s : DevSt d) : Assn := fun m st =>
  m = .only (.dev d) ∧ st.devs d = s

/-- The registers that `sb a1, 0(a0)` uses, owned by its hart's proof. -/
def hartPt (cpu : CPU) (p x y : Nat) : Assn :=
  regPt cpu .pc p ∗ regPt cpu .a0 x ∗ regPt cpu .a1 y

/-- The frame rule: a step that turns `P` into `Q` on `P`'s cells and
changes no other cell keeps every local frame `R`. -/
theorem star_frame {P Q R : Assn} {m : Fp} {st st2 : MState}
    (hR : Local R) (h : (P ∗ R) m st)
    (hstep : ∀ m1, P m1 st →
      Q m1 st2 ∧ ∀ c, m1 c = false → st2.val c = st.val c) :
    (Q ∗ R) m st2 := by
  obtain ⟨m1, m2, hd, rfl, hp, hr⟩ := h
  obtain ⟨hq, hout⟩ := hstep m1 hp
  refine ⟨m1, m2, hd, rfl, hq, hR m2 st st2 (fun c hc => ?_) hr⟩
  cases h1 : m1 c
  · exact (hout c h1).symm
  · rw [hd c h1] at hc; cases hc

/-! ## The disk invariant: a device starred with memory -/

/-- The body of the disk invariant (cf. xv6's `diskInv`, which is
`devInvR diskN .virtio (diskProto ..)`): the disk and its DMA buffer,
starred together, and a protocol relating them. -/
def diskBody : Assn := fun m st =>
  ∃ (s : DiskSt) (v : Byte),
    (devPt .disk s ∗ memPt diskBuf v) m st ∧
    (s.pending = false → v = s.block)

/-- The disk thread keeps its invariant and every frame. -/
theorem disk_dma_ok {R : Assn} {m : Fp} {st st2 : MState} (hR : Local R)
    (h : (diskBody ∗ R) m st) (hs : diskDma st = some st2) :
    (diskBody ∗ R) m st2 := by
  refine star_frame hR h fun m1 hb => ?_
  obtain ⟨s, v, ⟨md, mb, hd, rfl, ⟨rfl, hds⟩, ⟨rfl, _⟩⟩, _⟩ := hb
  simp only [diskDma, hds] at hs
  split at hs
  · cases hs
    refine ⟨⟨⟨false, s.block⟩, s.block,
      ⟨_, _, hd, rfl, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩, fun _ => rfl⟩, ?_⟩
    · simp [MState.setDev] <;> rfl
    · simp [MState.setDev, MState.setMem] <;> rfl
    · intro c hc
      cases c with
      | reg c r => rfl
      | mem a =>
        simp [Fp.union, Fp.only] at hc
        simp [MState.val, MState.setDev, MState.setMem, hc] <;> rfl
      | dev d =>
        simp [Fp.union, Fp.only] at hc
        simp [MState.val, MState.setDev, hc] <;> rfl
  · cases hs

/-! ## Hart steps -/

/-- An MMIO store to the disk's notify register. The hart's proof opens
the disk invariant, so it owns its registers starred with the device
and the buffer, and must give the invariant back. -/
theorem hart_notify_ok {R : Assn} {m : Fp} {st st2 : MState}
    {cpu : CPU} {p y : Nat} (hR : Local R)
    (h : ((hartPt cpu p diskNotify y ∗ diskBody) ∗ R) m st)
    (hs : hartSb st cpu = some st2) :
    ((hartPt cpu (p + 4) diskNotify y ∗ diskBody) ∗ R) m st2 := by
  refine star_frame hR h fun m1 hb => ?_
  obtain ⟨mh, mb, hhb, rfl, hh, hb⟩ := hb
  obtain ⟨mp, mr, hpr, rfl, ⟨rfl, hpc⟩, ma, my, hay, rfl, ⟨rfl, ha0⟩,
    ⟨rfl, ha1⟩⟩ := hh
  obtain ⟨s, v, ⟨md, mv, hdv, rfl, ⟨rfl, hds⟩, ⟨rfl, hdb⟩⟩, _⟩ := hb
  subst hds
  simp only [hartSb, MState.store, ha0, ha1, hpc, devDecode, diskNotify,
    uartThr] at hs
  cases hs
  refine ⟨⟨_, _, hhb, rfl,
    ⟨_, _, hpr, rfl, ⟨rfl, ?_⟩, _, _, hay, rfl, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩,
    ⟨true, (st.devs .disk : DiskSt).block⟩, v,
    ⟨_, _, hdv, rfl, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩,
    fun h => by cases h⟩, ?_⟩
  · simp [MState.setPc] <;> rfl
  · simp [MState.setPc, MState.setDev, ha0] <;> rfl
  · simp [MState.setPc, MState.setDev, ha1] <;> rfl
  · simp [MState.setPc, MState.setDev] <;> rfl
  · simp [MState.setPc, MState.setDev, hdb] <;> rfl
  · intro c hc
    cases c with
    | reg c r =>
      have : ¬(c = cpu ∧ r = .pc) := fun ⟨e1, e2⟩ => by
        subst e1 e2; simp [Fp.union, Fp.only] at hc
      simp only [MState.val, MState.setPc, MState.setDev, this, ↓reduceIte]
      rfl
    | mem a => rfl
    | dev d =>
      simp [Fp.union, Fp.only] at hc
      simp [MState.val, MState.setPc, MState.setDev, hc] <;> rfl

/-- A RAM store to a byte the hart owns: no invariant is opened, and the
frame `R`, which may hold the disk invariant, is untouched. -/
theorem hart_ram_ok {R : Assn} {m : Fp} {st st2 : MState}
    {cpu : CPU} {p x y v : Nat} (hR : Local R)
    (hx : devDecode x = none) (hram : ramBase ≤ x)
    (h : ((hartPt cpu p x y ∗ memPt x v) ∗ R) m st)
    (hs : hartSb st cpu = some st2) :
    ((hartPt cpu (p + 4) x y ∗ memPt x y) ∗ R) m st2 := by
  refine star_frame hR h fun m1 hb => ?_
  obtain ⟨mh, mx, hhx, rfl, hh, ⟨rfl, hmx⟩⟩ := hb
  obtain ⟨mp, mr, hpr, rfl, ⟨rfl, hpc⟩, ma, my, hay, rfl, ⟨rfl, ha0⟩,
    ⟨rfl, ha1⟩⟩ := hh
  simp only [hartSb, MState.store, ha0, ha1, hpc, hx, hram, ite_true]
    at hs
  cases hs
  refine ⟨⟨_, _, hhx, rfl,
    ⟨_, _, hpr, rfl, ⟨rfl, ?_⟩, _, _, hay, rfl, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩⟩,
    ⟨rfl, ?_⟩⟩, ?_⟩
  · simp [MState.setPc] <;> rfl
  · simp [MState.setPc, MState.setMem, ha0] <;> rfl
  · simp [MState.setPc, MState.setMem, ha1] <;> rfl
  · simp [MState.setPc, MState.setMem] <;> rfl
  · intro c hc
    cases c with
    | reg c r =>
      have : ¬(c = cpu ∧ r = .pc) := fun ⟨e1, e2⟩ => by
        subst e1 e2; simp [Fp.union, Fp.only] at hc
      simp only [MState.val, MState.setPc, MState.setMem, this, ↓reduceIte]
      rfl
    | mem a =>
      simp [Fp.union, Fp.only] at hc
      simp [MState.val, MState.setPc, MState.setMem, hc] <;> rfl
    | dev d => rfl

/-! ## "CSL soundness": a fact about the real state -/

/-- Whoever holds the disk invariant knows that, once no transfer is due,
the buffer in RAM holds the disk's block. -/
theorem disk_buf_holds {R : Assn} {m : Fp} {st : MState}
    (h : (diskBody ∗ R) m st)
    (hp : (st.devs .disk : DiskSt).pending = false) :
    st.mem diskBuf = (st.devs .disk : DiskSt).block := by
  obtain ⟨_, _, _, _, ⟨s, v, ⟨_, _, _, _, ⟨_, hds⟩, ⟨_, hdb⟩⟩, hpr⟩, _⟩ :=
    h
  have e : (st.devs .disk : DiskSt) = s := hds
  rw [e] at hp ⊢
  rw [hdb]; exact hpr hp

end ToySep
