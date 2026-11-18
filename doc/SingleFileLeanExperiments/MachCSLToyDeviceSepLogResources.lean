/-!
# A toy MachCSL: how devices become separation-logic resources

This file gives the Lean gist of Figure 3 of the xv6 verification paper,
"MachCSL's model of system execution (left, §3) and the CSL representation
of it (right, §4 and §5)". Like MachCSL, it is closed-world: the board's
devices are fixed (cf. `MachCSL/Dev/Fabric.lean`).

* Left of the figure, "all of the state": `MState` holds every hart's
  registers, the shared memory and every device's state
  (`MachCSL.MState`). Harts and devices are threads of one language
  (`MachCSL.Expr`: `hart`, `dev`, `power`).
* Right of the figure, "proof over partial state": every piece of state is
  a `Cell`. A `World` says which `Holder` holds each cell: a thread's proof,
  an invariant, or nobody. This stands in for MachCSL's ghost state. The
  register maps (`regPointsTo`), the memory heap (`genHeapInterp`) and the
  device mirrors (`devAuthAt`/`devFragAt`) each have an authoritative part
  in the state interpretation `machInterp σ`, which tracks `σ`, and
  fragments that proofs and invariants hold. Here a holder's `view` reads
  its cells' values from `σ`, so the fragments agree with the machine by
  construction (Iris proves this with `ghost_map`/`ghost_var` agreement).
  Since `holder` is a function, no two holders own the same cell, which is
  separation.
* A device is one `Cell.dev d` (in MachCSL, `devFrag d s`, a ghost
  variable over the whole device state). xv6 keeps it in a per-device
  invariant together with client ghost state (`devInvR`, e.g.
  `Xv6.uartInv`): here `Holder.inv (.dev d)` and `Cell.ghost`.
* An MMIO store opens the device invariant, applies the device model's
  `write`, and must re-establish the invariant body, possibly with a ghost
  update (`devWriteAU`, `swp_sail_mem_write_dev`): `hart_sb_uart_ok`. The
  device thread's own steps must do the same (`wpDev_localO`):
  `uart_step_ok`. A RAM store touches only cells its thread holds, so no
  invariant is involved (the frame rule): `hart_sb_ram_ok`.
* "CSL soundness" (adequacy) turns facts about the resources back into facts
  about the real state: `uart_wire_prefix`.

This toy leaves out TSO (MachCSL's memory is a log of writes with per-hart
views), fractions, persistent resources, later modalities, masks, eras and
power, and the PLIC wires.
-/

namespace ToyRes

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
  /-- Bytes stored into the transmit register and not yet sent. -/
  tx : List Byte
  /-- Bytes that left on the wire (observable, `Obs.dev`). -/
  wire : List Byte

def DevSt : DevId → Type
  | .uart => UartSt
  | .disk => Nat → Byte
  | .plic => Nat → Bool

structure MState where
  regs : CPU → Reg → Nat
  mem : Addr → Byte
  devs : (d : DevId) → DevSt d

/-- The UART's transmit holding register. -/
def uartThr : Addr := 0x10000000
def ramBase : Addr := 0x80000000

def devDecode (a : Addr) : Option (DevId × Nat) :=
  if a = uartThr then some (.uart, 0) else none

/-- The device models' MMIO stores (`DevSig.write`). -/
def devWrite : (d : DevId) → DevSt d → Nat → Byte → Option (DevSt d)
  | .uart, s, 0, b => some { s with tx := s.tx ++ [b] }
  | _, _, _, _ => none

def MState.setDev (σ : MState) (d : DevId) (s : DevSt d) : MState :=
  { σ with devs := fun d' => if h : d' = d then h ▸ s else σ.devs d' }

/-- A store on the bus (`MachCSL.evStep`, `memWrite`): MMIO or RAM. -/
def MState.store (σ : MState) (a : Addr) (b : Byte) : Option MState :=
  match devDecode a with
  | some (d, off) => (devWrite d (σ.devs d) off b).map (σ.setDev d)
  | none =>
    if ramBase ≤ a then
      some { σ with mem := fun a' => if a' = a then b else σ.mem a' }
    else none

/-- Hart `cpu` executes `sb a1, 0(a0)`. -/
def hartSb (σ : MState) (cpu : CPU) : Option MState :=
  (σ.store (σ.regs cpu .a0) (σ.regs cpu .a1)).map fun σ' =>
    { σ' with regs := fun c r =>
        if c = cpu ∧ r = .pc then σ.regs cpu .pc + 4 else σ'.regs c r }

/-- One step of the UART's thread: send the oldest pending byte. -/
def uartSend (s : UartSt) : Option UartSt :=
  match s.tx with
  | b :: tx => some ⟨tx, s.wire ++ [b]⟩
  | [] => none

/-! ## Right of Figure 3: cells, holders and views -/

inductive Cell where
  | reg (c : CPU) (r : Reg)
  | mem (a : Addr)
  | dev (d : DevId)
  /-- Logical state, e.g. files or processes; here byte lists. -/
  | ghost (g : Nat)

def CellVal : Cell → Type
  | .reg .. => Nat
  | .mem _ => Byte
  | .dev d => DevSt d
  | .ghost _ => List Byte

inductive InvName where
  | dev (d : DevId)
  | lock (a : Addr)
  deriving DecidableEq

inductive Holder where
  /-- The proof of a hart's or device's thread. -/
  | thread (i : Nat)
  | inv (n : InvName)
  | nobody
  deriving DecidableEq

structure World where
  σ : MState
  ghost : Nat → List Byte
  holder : Cell → Holder

def World.val (w : World) : (c : Cell) → CellVal c
  | .reg c r => w.σ.regs c r
  | .mem a => w.σ.mem a
  | .dev d => w.σ.devs d
  | .ghost g => w.ghost g

/-- What holder `h` owns: its cells, at their current values. -/
abbrev Res := (c : Cell) → Option (CellVal c)

def World.view (w : World) (h : Holder) : Res := fun c =>
  if w.holder c = h then some (w.val c) else none

/-- Assertions, e.g. a points-to `fun r => r (.mem a) = some v`. -/
abbrev Assn := Res → Prop

/-- Every invariant's body holds of the cells it holds. -/
def WorldOk (body : InvName → Assn) (w : World) : Prop :=
  ∀ n, body n (w.view (.inv n))

/-- A step that changes no cell of any invariant keeps the world valid. -/
theorem frame_ok (body : InvName → Assn) (w w' : World)
    (hh : w'.holder = w.holder)
    (hval : ∀ c n, w.holder c = .inv n → w'.val c = w.val c)
    (hok : WorldOk body w) : WorldOk body w' := by
  intro n
  have : w'.view (.inv n) = w.view (.inv n) := by
    funext c
    simp only [World.view, hh]
    split
    · next hc => rw [hval c n hc]
    · rfl
  rw [this]; exact hok n

/-- A step that changes only cells of thread `i` and of the invariant `n`
it opened keeps the world valid if it re-establishes `n`'s body. The
other invariants see no change. -/
theorem step_ok (body : InvName → Assn) (w w' : World) (i : Nat)
    (n : InvName) (hh : w'.holder = w.holder)
    (hval : ∀ c, w.holder c ≠ .thread i → w.holder c ≠ .inv n →
      w'.val c = w.val c)
    (hok : WorldOk body w) (hn : body n (w'.view (.inv n))) :
    WorldOk body w' := by
  intro m
  by_cases hm : m = n
  · subst hm; exact hn
  · have : w'.view (.inv m) = w.view (.inv m) := by
      funext c
      simp only [World.view, hh]
      split
      · next hc =>
        rw [hval c (by rw [hc]; simp) (by rw [hc]; simp [hm])]
      · rfl
    rw [this]; exact hok m

/-! ## The UART invariant (cf. `Xv6.uartInv`) -/

/-- Ghost cell 0 is the console trace the kernel has written. -/
def uartBody : Assn := fun r =>
  ∃ (s : UartSt) (g : List Byte),
    r (.dev .uart) = some s ∧ r (.ghost 0) = some g ∧ s.wire ++ s.tx = g

/-- The UART invariant holds the UART and the console trace. -/
def Layout (w : World) : Prop :=
  w.holder (.dev .uart) = .inv (.dev .uart) ∧
  w.holder (.ghost 0) = .inv (.dev .uart)

theorem view_inv (w : World) (n : InvName) (c : Cell)
    (h : w.holder c = .inv n) : w.view (.inv n) c = some (w.val c) := by
  simp [World.view, h]

/-! ## Hart steps -/

/-- The new world after an MMIO store of `b` to the UART. -/
def World.logUart (w : World) (σ' : MState) (b : Byte) : World :=
  { w with
    σ := σ'
    ghost := fun g => if g = 0 then w.ghost 0 ++ [b] else w.ghost g }

/-- An MMIO store to the UART: open its invariant, let the device model
take the byte, and extend the console trace (a ghost update). -/
theorem hart_sb_uart_ok (body : InvName → Assn) (w : World) (i : Nat)
    (cpu : CPU) (hl : Layout w) (hbody : body (.dev .uart) = uartBody)
    (hok : WorldOk body w) (hpc : w.holder (.reg cpu .pc) = .thread i)
    (ha : w.σ.regs cpu .a0 = uartThr) :
    ∃ σ', hartSb w.σ cpu = some σ' ∧
      WorldOk body (w.logUart σ' (w.σ.regs cpu .a1)) := by
  obtain ⟨hd, hg⟩ := hl
  have hb := hok (.dev .uart)
  rw [hbody] at hb
  obtain ⟨s, g, hs, hg0, hsg⟩ := hb
  rw [view_inv w _ _ hd] at hs
  rw [view_inv w _ _ hg] at hg0
  cases hs; cases hg0
  let s : UartSt := w.σ.devs .uart
  change s.wire ++ s.tx = w.ghost 0 at hsg
  let u : UartSt := ⟨s.tx ++ [w.σ.regs cpu .a1], s.wire⟩
  refine ⟨{ w.σ.setDev .uart u with regs := fun c r =>
      if c = cpu ∧ r = .pc then w.σ.regs cpu .pc + 4 else w.σ.regs c r },
    by simp only [hartSb, MState.store, devDecode, ha, ↓reduceIte]; rfl,
    step_ok body w _ i (.dev .uart) (by rfl) ?_ hok ?_⟩
  · intro c hc hn
    cases c with
    | reg c r =>
      by_cases e : c = cpu ∧ r = .pc
      · obtain ⟨rfl, rfl⟩ := e; exact absurd hpc hc
      · simp only [World.val, World.logUart, e, ↓reduceIte]; rfl
    | mem a => rfl
    | dev d =>
      cases d with
      | uart => exact absurd hd hn
      | _ => rfl
    | ghost g =>
      by_cases e : g = 0
      · subst e; exact absurd hg hn
      · simp only [World.val, World.logUart, e, ↓reduceIte]; rfl
  · rw [hbody]
    refine ⟨_, _, view_inv _ _ _ hd, view_inv _ _ _ hg, ?_⟩
    simp [World.val, World.logUart, MState.setDev, u, ← hsg]

/-- A RAM store to a byte the thread holds: no invariant is opened. -/
theorem hart_sb_ram_ok (body : InvName → Assn) (w : World) (i : Nat)
    (cpu : CPU) (hok : WorldOk body w)
    (hpc : w.holder (.reg cpu .pc) = .thread i)
    (hm : w.holder (.mem (w.σ.regs cpu .a0)) = .thread i)
    (ha : ramBase ≤ w.σ.regs cpu .a0) (hu : w.σ.regs cpu .a0 ≠ uartThr) :
    ∃ σ', hartSb w.σ cpu = some σ' ∧
      WorldOk body { w with σ := σ' } := by
  refine ⟨_, by simp [hartSb, MState.store, devDecode, hu, ha]; rfl,
    frame_ok body w _ (by rfl) (fun c n hc => ?_) hok⟩
  cases c with
  | reg c r =>
    by_cases e : c = cpu ∧ r = .pc
    · obtain ⟨rfl, rfl⟩ := e; rw [hpc] at hc; cases hc
    · simp [World.val, e]; rfl
  | mem a =>
    by_cases e : a = w.σ.regs cpu .a0
    · subst e; rw [hm] at hc; cases hc
    · simp [World.val, e]; rfl
  | _ => rfl

/-! ## The device thread (cf. `Xv6.wpDev_uart_inv`) -/

theorem uart_step_ok (body : InvName → Assn) (w : World) (j : Nat)
    (hl : Layout w) (hbody : body (.dev .uart) = uartBody)
    (hok : WorldOk body w) (s' : UartSt)
    (hs : uartSend (w.σ.devs .uart) = some s') :
    WorldOk body { w with σ := w.σ.setDev .uart s' } := by
  obtain ⟨hd, hg⟩ := hl
  refine step_ok body w _ j (.dev .uart) (by rfl) ?_ hok ?_
  · intro c _ hn
    cases c with
    | dev d =>
      cases d with
      | uart => exact absurd hd hn
      | _ => rfl
    | _ => rfl
  · have hb := hok (.dev .uart)
    rw [hbody] at hb ⊢
    obtain ⟨s, g, hs0, hg0, hsg⟩ := hb
    rw [view_inv w _ _ hd] at hs0
    rw [view_inv w _ _ hg] at hg0
    cases hs0; cases hg0
    refine ⟨_, _, view_inv _ _ _ hd, view_inv _ _ _ hg, ?_⟩
    change (w.σ.devs .uart : UartSt).wire ++ (w.σ.devs .uart : UartSt).tx
      = w.ghost 0 at hsg
    simp only [World.val, MState.setDev]
    revert hs
    simp only [uartSend]
    split
    · next b tx htx =>
      intro h; cases h
      show _ ++ [b] ++ tx = _
      rw [← hsg, htx]; simp
    · intro h; cases h

/-! ## "CSL soundness": a fact about the real state -/

/-- The bytes on the UART's wire are a prefix of the console trace. -/
theorem uart_wire_prefix (body : InvName → Assn) (w : World)
    (hl : Layout w) (hbody : body (.dev .uart) = uartBody)
    (hok : WorldOk body w) :
    ∃ rest, (w.σ.devs .uart : UartSt).wire ++ rest = w.ghost 0 := by
  have hb := hok (.dev .uart)
  rw [hbody] at hb
  obtain ⟨s, g, hs, hg0, hsg⟩ := hb
  rw [view_inv w _ _ hl.1] at hs
  rw [view_inv w _ _ hl.2] at hg0
  cases hs; cases hg0
  exact ⟨_, hsg⟩

end ToyRes
