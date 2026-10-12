import Std.Tactic.Do
import Std.Internal.Do

/-!
# A toy Arm-like ISA

A massively simplified version of the AArch64 syntax and semantics of Kraken
(`Kraken/AArch64/Syntax.lean` and `Kraken/AArch64/Semantics.lean`).

Simplifications compared to Kraken:
* Only 64-bit registers and 64-bit operations, so nothing is parameterized by a bit width.
* A single flat `Instr` type.
* No stack pointer and no zero register.
* Memory is a partial map from addresses to whole 64-bit words instead of bytes.
* No `Effects` type: the semantics of an instruction is directly a weakest precondition
  (`Instr.wp`), and programs get an instance of the `WP` class of the standard library
  (`Std.Internal.Do.WP`), so that `vcgen` can be used to verify them.

This is closer to machine code than to assembly: there are no labels, the state has a program
counter, a program is a map from addresses to instructions, every instruction occupies 4 bytes, and
branches are relative to the address of the branch instruction.

Only the standard library is used, no Mathlib.
-/

open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

namespace ToySys

/-! ## Syntax -/

abbrev Word := BitVec 64

inductive Reg
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  deriving DecidableEq, Repr

/-- The second operand of most instructions is a register or an immediate. -/
inductive Operand
  | reg (r : Reg)
  | imm (v : Word)
  deriving DecidableEq, Repr

inductive Cond
  /-- Equal: after `cmp a b`, holds if `a = b`. -/
  | EQ
  /-- Not equal: after `cmp a b`, holds if `a ≠ b`. -/
  | NE
  /-- Unsigned higher or same: after `cmp a b`, holds if `a ≥ b` as unsigned numbers. -/
  | HS
  /-- Unsigned lower: after `cmp a b`, holds if `a < b` as unsigned numbers. -/
  | LO
  /-- Unsigned higher: after `cmp a b`, holds if `a > b` as unsigned numbers. -/
  | HI
  /-- Unsigned lower or same: after `cmp a b`, holds if `a ≤ b` as unsigned numbers. -/
  | LS
  /-- Signed greater or equal: after `cmp a b`, holds if `a ≥ b` as signed numbers. -/
  | GE
  /-- Signed less than: after `cmp a b`, holds if `a < b` as signed numbers. -/
  | LT
  /-- Signed greater than: after `cmp a b`, holds if `a > b` as signed numbers. -/
  | GT
  /-- Signed less or equal: after `cmp a b`, holds if `a ≤ b` as signed numbers. -/
  | LE
  deriving DecidableEq, Repr

inductive Instr
  | mov (dst : Reg) (src : Operand)
  | add (dst src1 : Reg) (src2 : Operand)
  | sub (dst src1 : Reg) (src2 : Operand)
  | mul (dst src1 src2 : Reg)
  | and (dst src1 : Reg) (src2 : Operand)
  /-- Sets the flags according to `src1 - src2`. -/
  | cmp (src1 : Reg) (src2 : Operand)
  /-- `dst := if cond then src1 else src2`. -/
  | csel (dst src1 src2 : Reg) (cond : Cond)
  /-- Loads the word at address `base + off`. -/
  | ldr (dst base : Reg) (off : Word)
  /-- Stores a word at address `base + off`. -/
  | str (src base : Reg) (off : Word)
  /-- Branches to the address of this instruction plus `off`. -/
  | b (off : Word)
  /-- Branches by `off` if `cond` holds. -/
  | bcond (cond : Cond) (off : Word)
  /-- Branches by `off` if `r` is zero. -/
  | cbz (r : Reg) (off : Word)
  /-- Branches by `off` if `r` is not zero. -/
  | cbnz (r : Reg) (off : Word)
  /-- Permanently undefined instruction: executing it is always an error. -/
  | udf
  deriving DecidableEq, Repr

/-- A program maps addresses to instructions. Execution ends successfully when the program counter
reaches an address that holds no instruction. -/
abbrev Program := Word → Option Instr

/-- The program that holds the instructions `is` at addresses `base`, `base + 4`, `base + 8`, ...
and nothing elsewhere. -/
def Program.ofList (base : Word) : List Instr → Program
  | [] => fun _ => none
  | i :: is => fun a => if a = base then some i else Program.ofList (base + 4) is a

/-! ## Machine state -/

structure Flags where
  n : Bool := false
  z : Bool := false
  c : Bool := false
  v : Bool := false
  deriving DecidableEq, Repr

/-- Addresses name whole words; unmapped addresses must not be accessed. -/
abbrev Mem := Word → Option Word

structure State where
  regs : Reg → Word
  flags : Flags
  mem : Mem
  /-- The address of the instruction that is executed next. -/
  pc : Word

def State.setReg (s : State) (r : Reg) (v : Word) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

def State.setMem (s : State) (a : Word) (v : Word) : State :=
  { s with mem := fun a' => if a' = a then some v else s.mem a' }

def State.setPc (s : State) (a : Word) : State :=
  { s with pc := a }

/-- Advances the program counter to the following instruction. -/
def State.next (s : State) : State := s.setPc (s.pc + 4)

/-- Moves the program counter by `off`, relative to the current instruction. -/
def State.branch (s : State) (off : Word) : State := s.setPc (s.pc + off)

def Operand.eval (o : Operand) (s : State) : Word := match o with
  | .reg r => s.regs r
  | .imm v => v

/-- The flags set by comparing `a` to `b`, i.e. by computing `a - b`. -/
def Flags.ofSub (a b : Word) : Flags :=
  let res := a - b
  { n := res.msb
    z := res == 0
    c := decide (b ≤ a) -- no unsigned borrow
    v := decide (res.toInt ≠ a.toInt - b.toInt) }

def Cond.holds (c : Cond) (f : Flags) : Bool := match c with
  | .EQ => f.z
  | .NE => !f.z
  | .HS => f.c
  | .LO => !f.c
  | .HI => f.c && !f.z
  | .LS => !f.c || f.z
  | .GE => f.n == f.v
  | .LT => f.n != f.v
  | .GT => !f.z && f.n == f.v
  | .LE => f.z || f.n != f.v

/-! ## Semantics -/

/-- Weakest precondition of a single instruction: `i.wp post s` holds if executing `i` in state `s`
is safe and leads to a state satisfying `post`. `s.pc` is the address of `i`, and the resulting
state's `pc` is the address of the instruction to execute next. -/
def Instr.wp (i : Instr) (post : State → Prop) (s : State) : Prop :=
  match i with
  | .mov dst src => post (s.setReg dst (src.eval s)).next
  | .add dst src1 src2 => post (s.setReg dst (s.regs src1 + src2.eval s)).next
  | .sub dst src1 src2 => post (s.setReg dst (s.regs src1 - src2.eval s)).next
  | .mul dst src1 src2 => post (s.setReg dst (s.regs src1 * s.regs src2)).next
  | .and dst src1 src2 => post (s.setReg dst (s.regs src1 &&& src2.eval s)).next
  | .cmp src1 src2 => post { s with flags := .ofSub (s.regs src1) (src2.eval s) }.next
  | .csel dst src1 src2 cond =>
    post (s.setReg dst (if cond.holds s.flags then s.regs src1 else s.regs src2)).next
  | .ldr dst base off => ∃ v, s.mem (s.regs base + off) = some v ∧ post (s.setReg dst v).next
  | .str src base off =>
    (s.mem (s.regs base + off)).isSome ∧ post (s.setMem (s.regs base + off) (s.regs src)).next
  | .b off => post (s.branch off)
  | .bcond cond off => if cond.holds s.flags then post (s.branch off) else post s.next
  | .cbz r off => if s.regs r = 0 then post (s.branch off) else post s.next
  | .cbnz r off => if s.regs r ≠ 0 then post (s.branch off) else post s.next
  | .udf => False

theorem Instr.wp_mono {i : Instr} {post post' : State → Prop}
    (hpost : ∀ s, post s → post' s) : ∀ s, i.wp post s → i.wp post' s := by
  intro s h
  cases i <;> simp only [Instr.wp] at h ⊢ <;> grind

/-- Weakest precondition of running a program until the program counter leaves it. It is defined
inductively, so it expresses total correctness: loops have to terminate. -/
inductive Exec (prog : Program) (Q : State → Prop) : State → Prop
  | done {s : State} : prog s.pc = none → Q s → Exec prog Q s
  | step {s : State} {i : Instr} (mid : State → Prop) :
      prog s.pc = some i →
      i.wp mid s →
      (∀ s', mid s' → Exec prog Q s') →
      Exec prog Q s

theorem Exec.mono {prog : Program} {Q Q' : State → Prop} {s : State}
    (hQ : ∀ s, Q s → Q' s) (h : Exec prog Q s) : Exec prog Q' s := by
  induction h with
  | done hpc h => exact .done hpc (hQ _ h)
  | step mid hpc hi _ ih => exact .step mid hpc hi ih

/-- One step of `Exec`: fetch the instruction at the program counter and execute it. -/
theorem Exec.iff {prog : Program} {Q : State → Prop} {s : State} :
    Exec prog Q s ↔
      match prog s.pc with
      | none => Q s
      | some i => i.wp (Exec prog Q) s := by
  constructor
  · intro h
    cases h with
    | done hpc h => rw [hpc]; exact h
    | step mid hpc hi hmid => rw [hpc]; exact Instr.wp_mono hmid s hi
  · intro h
    split at h
    · next hpc => exact .done hpc h
    · next i hpc => exact .step _ hpc h (fun _ h => h)

/-! ## `WP` instance -/

/-- The program type that gets a `WP` instance, so that `vcgen` can make progress by matching on it.
It stands for setting the program counter to `pc`, executing `instr` as if it had been fetched from
there (`none` meaning that there is no instruction, so execution ends), and then continuing to run
`prog`. -/
structure Code where
  prog : Program
  pc : Word
  instr : Option Instr

/-- Running `prog` starting at address `a`. -/
def Program.runFrom (prog : Program) (a : Word) : Code := ⟨prog, a, prog a⟩

def Code.wp (c : Code) (Q : State → Prop) (s : State) : Prop :=
  match c.instr with
  | none => Q (s.setPc c.pc)
  | some i => i.wp (Exec c.prog Q) (s.setPc c.pc)

theorem Code.wp_mono {c : Code} {Q Q' : State → Prop} {s : State}
    (hQ : ∀ s, Q s → Q' s) (h : c.wp Q s) : c.wp Q' s := by
  obtain ⟨prog, pc, instr⟩ := c
  cases instr with
  | none => exact hQ _ h
  | some i => exact Instr.wp_mono (fun _ h => h.mono hQ) _ h

abbrev Assn := State → Prop

instance : WP Code Unit Assn EPost.Nil where
  wpTrans c := ⟨fun Q _ s => c.wp (Q ()) s⟩
  wp_trans_monotone _ := fun _ _ _ _ _ hQ _ h => Code.wp_mono (hQ ()) h

variable {prog : Program} {a : Word} {Q : Unit → Assn} {epost : EPost.Nil} {s : State}

theorem wp_halt_eq : wp (Code.mk prog a none) Q epost s = Q () (s.setPc a) := rfl

theorem wp_instr_eq {i : Instr} :
    wp (Code.mk prog a (some i)) Q epost s = i.wp (Exec prog (Q ())) (s.setPc a) := rfl

/-- The meaning of a triple about `prog.runFrom a`: the program counter of the initial state is
replaced by `a`, and then the program runs according to `Exec`. -/
theorem wp_runFrom_eq : wp (prog.runFrom a) Q epost s = Exec prog (Q ()) (s.setPc a) :=
  propext (Exec.iff (s := s.setPc a)).symm

/-! ## Specifications for `vcgen`

One specification per instruction. Each one states the weakest precondition of executing that
instruction at address `a` in terms of the weakest precondition of running the program from the
address of the instruction that is executed next. -/

private theorem triple_of_wp {c : Code} {pre : Assn}
    (h : ∀ s, wp c Q epost s = pre s) : Triple c pre Q epost :=
  Triple.iff.mpr (by rw [funext h]; exact PartialOrder.rel_refl)

private theorem triple_of_meet_imp_wp {c : Code} {pre₁ pre₂ : Assn}
    (h : ∀ s, pre₁ s → pre₂ s → wp c Q epost s) : Triple c (pre₁ ⊓ pre₂) Q epost :=
  Triple.iff.mpr fun s hs => by
    simp only [meet_apply, meet_prop_eq_and] at hs
    exact h s hs.1 hs.2

/-- `k (Program.ofList base is a)`, in a form that lets `vcgen` evaluate the lookup: it only
rewrites and splits at the head of the program. -/
def Program.fetchList (base : Word) (is : List Instr) (a : Word) (k : Option Instr → Code) : Code :=
  k (Program.ofList base is a)

/-- Lets `vcgen` fetch instructions of programs given as a list. -/
@[spec] theorem Program.runFrom_ofList (base : Word) (is : List Instr) :
    (Program.ofList base is).runFrom a =
      Program.fetchList base is a (Code.mk (Program.ofList base is) a) := rfl

@[spec] theorem Program.fetchList_nil (base : Word) (k : Option Instr → Code) :
    Program.fetchList base [] a k = k none := rfl

@[spec] theorem Program.fetchList_cons (base : Word) (i : Instr) (is : List Instr)
    (k : Option Instr → Code) :
    Program.fetchList base (i :: is) a k =
      if a = base then k (some i) else Program.fetchList (base + 4) is a k := by
  simp only [Program.fetchList, Program.ofList]
  split <;> rfl

@[spec] theorem Spec.halt : Triple (Code.mk prog a none) (fun s => Q () (s.setPc a)) Q epost :=
  triple_of_wp fun _ => wp_halt_eq

@[spec] theorem Spec.mov (dst : Reg) (src : Operand) :
    Triple (Code.mk prog a (some (.mov dst src)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setReg dst (src.eval s))) Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.add (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog a (some (.add dst src1 src2)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setReg dst (s.regs src1 + src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.sub (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog a (some (.sub dst src1 src2)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setReg dst (s.regs src1 - src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.mul (dst src1 src2 : Reg) :
    Triple (Code.mk prog a (some (.mul dst src1 src2)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setReg dst (s.regs src1 * s.regs src2)))
      Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.and (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog a (some (.and dst src1 src2)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setReg dst (s.regs src1 &&& src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.cmp (src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog a (some (.cmp src1 src2)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost
        { s with flags := .ofSub (s.regs src1) (src2.eval s) }) Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.csel (dst src1 src2 : Reg) (cond : Cond) :
    Triple (Code.mk prog a (some (.csel dst src1 src2 cond)))
      (fun s => wp (prog.runFrom (a + 4)) Q epost
        (s.setReg dst (if cond.holds s.flags then s.regs src1 else s.regs src2))) Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.ldr (dst base : Reg) (off : Word) :
    Triple (Code.mk prog a (some (.ldr dst base off)))
      ((fun s => (s.mem (s.regs base + off)).isSome) ⊓
       (fun s => ∀ v, s.mem (s.regs base + off) = some v →
          wp (prog.runFrom (a + 4)) Q epost (s.setReg dst v))) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₁
    have h := h₂ v hv
    rw [wp_runFrom_eq] at h
    exact ⟨v, hv, h⟩

@[spec] theorem Spec.str (src base : Reg) (off : Word) :
    Triple (Code.mk prog a (some (.str src base off)))
      ((fun s => (s.mem (s.regs base + off)).isSome) ⊓
       (fun s => wp (prog.runFrom (a + 4)) Q epost (s.setMem (s.regs base + off) (s.regs src))))
      Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    rw [wp_runFrom_eq] at h₂
    exact ⟨h₁, h₂⟩

@[spec] theorem Spec.b (off : Word) :
    Triple (Code.mk prog a (some (.b off))) (wp (prog.runFrom (a + off)) Q epost) Q epost :=
  triple_of_wp fun _ => by rw [wp_instr_eq, wp_runFrom_eq]; rfl

@[spec] theorem Spec.bcond (cond : Cond) (off : Word) :
    Triple (Code.mk prog a (some (.bcond cond off)))
      ((fun s => cond.holds s.flags = true → wp (prog.runFrom (a + off)) Q epost s) ⊓
       (fun s => cond.holds s.flags = false → wp (prog.runFrom (a + 4)) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    simp only [wp_runFrom_eq] at h₁ h₂
    rw [wp_instr_eq]
    by_cases h : cond.holds s.flags = true <;> simp_all [Instr.wp, State.branch, State.next, State.setPc]

@[spec] theorem Spec.cbz (r : Reg) (off : Word) :
    Triple (Code.mk prog a (some (.cbz r off)))
      ((fun s => s.regs r = 0 → wp (prog.runFrom (a + off)) Q epost s) ⊓
       (fun s => s.regs r ≠ 0 → wp (prog.runFrom (a + 4)) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    simp only [wp_runFrom_eq] at h₁ h₂
    rw [wp_instr_eq]
    by_cases h : s.regs r = 0 <;> simp_all [Instr.wp, State.branch, State.next, State.setPc]

@[spec] theorem Spec.cbnz (r : Reg) (off : Word) :
    Triple (Code.mk prog a (some (.cbnz r off)))
      ((fun s => s.regs r ≠ 0 → wp (prog.runFrom (a + off)) Q epost s) ⊓
       (fun s => s.regs r = 0 → wp (prog.runFrom (a + 4)) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    simp only [wp_runFrom_eq] at h₁ h₂
    rw [wp_instr_eq]
    by_cases h : s.regs r = 0 <;> simp_all [Instr.wp, State.branch, State.next, State.setPc]

@[spec] theorem Spec.udf :
    Triple (Code.mk prog a (some .udf)) (fun _ => False) Q epost :=
  Triple.iff.mpr fun _ h => h.elim

/-! ## Example: the maximum of three numbers -/

/-- Computes the unsigned maximum of `X0`, `X1` and `X2` into `X0`. -/
def max3 : Program := .ofList 0x1000 [
  /- 0x1000 -/ .cmp .X0 (.reg .X1),
  /- 0x1004 -/ .bcond .HS 8,
  /- 0x1008 -/ .mov .X0 (.reg .X1),
  /- 0x100c -/ .cmp .X0 (.reg .X2),
  /- 0x1010 -/ .bcond .HS 8,
  /- 0x1014 -/ .mov .X0 (.reg .X2)
]

theorem max3_correct (a b c : Word) :
    ⦃ fun s => s.regs .X0 = a ∧ s.regs .X1 = b ∧ s.regs .X2 = c ⦄
      max3.runFrom 0x1000
    ⦃ fun _ s => s.pc = 0x1018 ∧ (s.regs .X0 = a ∨ s.regs .X0 = b ∨ s.regs .X0 = c) ∧
        a ≤ s.regs .X0 ∧ b ≤ s.regs .X0 ∧ c ≤ s.regs .X0 ⦄ := by
  unfold max3
  vcgen simplifying_assumptions
  all_goals grind [Cond.holds, Flags.ofSub, Operand.eval, State.setReg, State.setPc]

end ToySys
