import Std.Tactic.Do
import Std.Internal.Do

/-!
# A toy Arm-like ISA

A massively simplified version of the AArch64 syntax and semantics of Kraken
(`Kraken/AArch64/Syntax.lean` and `Kraken/AArch64/Semantics.lean`).

Simplifications compared to Kraken:
* Only 64-bit registers and 64-bit operations, so nothing is parameterized by a bit width.
* A single flat `Instr` type, which also contains labels.
* No stack pointer and no zero register.
* Memory is a partial map from addresses to whole 64-bit words instead of bytes.
* No `Effects` type: the semantics of an instruction is directly a weakest precondition
  (`Instr.wp`), and programs get an instance of the `WP` class of the standard library
  (`Std.Internal.Do.WP`), so that `vcgen` can be used to verify them.

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

inductive Cond | EQ | NE | HS | LO | HI | LS | GE | LT | GT | LE
  deriving DecidableEq, Repr

abbrev Label := String

inductive Instr
  /-- Pseudo-instruction marking a branch target; does nothing when executed. -/
  | label (l : Label)
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
  | b (target : Label)
  | bcond (cond : Cond) (target : Label)
  | cbz (r : Reg) (target : Label)
  | cbnz (r : Reg) (target : Label)
  /-- Permanently undefined instruction: executing it is always an error. -/
  | udf
  deriving DecidableEq, Repr

/-- A program is a list of instructions. Execution ends successfully when it falls off the end. -/
abbrev Program := List Instr

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

def State.setReg (s : State) (r : Reg) (v : Word) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

def State.setMem (s : State) (a : Word) (v : Word) : State :=
  { s with mem := fun a' => if a' = a then some v else s.mem a' }

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

/-- Weakest precondition of a single instruction: `i.wp next jmp s` holds if executing `i` in
state `s` is safe and either falls through into a state satisfying `next` or jumps to a label `l`
in a state satisfying `jmp l`. -/
def Instr.wp (i : Instr) (next : State → Prop) (jmp : Label → State → Prop) (s : State) : Prop :=
  match i with
  | .label _ => next s
  | .mov dst src => next (s.setReg dst (src.eval s))
  | .add dst src1 src2 => next (s.setReg dst (s.regs src1 + src2.eval s))
  | .sub dst src1 src2 => next (s.setReg dst (s.regs src1 - src2.eval s))
  | .mul dst src1 src2 => next (s.setReg dst (s.regs src1 * s.regs src2))
  | .and dst src1 src2 => next (s.setReg dst (s.regs src1 &&& src2.eval s))
  | .cmp src1 src2 => next { s with flags := .ofSub (s.regs src1) (src2.eval s) }
  | .csel dst src1 src2 cond =>
    next (s.setReg dst (if cond.holds s.flags then s.regs src1 else s.regs src2))
  | .ldr dst base off => ∃ v, s.mem (s.regs base + off) = some v ∧ next (s.setReg dst v)
  | .str src base off =>
    (s.mem (s.regs base + off)).isSome ∧ next (s.setMem (s.regs base + off) (s.regs src))
  | .b target => jmp target s
  | .bcond cond target => if cond.holds s.flags then jmp target s else next s
  | .cbz r target => if s.regs r = 0 then jmp target s else next s
  | .cbnz r target => if s.regs r ≠ 0 then jmp target s else next s
  | .udf => False

theorem Instr.wp_mono {i : Instr} {next next' : State → Prop} {jmp jmp' : Label → State → Prop}
    (hnext : ∀ s, next s → next' s) (hjmp : ∀ l s, jmp l s → jmp' l s) :
    ∀ s, i.wp next jmp s → i.wp next' jmp' s := by
  intro s h
  cases i <;> simp only [Instr.wp] at h ⊢ <;> grind

/-- A program together with the instructions that remain to be executed. This is the program type
that gets a `WP` instance: the whole program `prog` is needed to resolve branch targets, and `vcgen`
makes progress by matching on the first instruction of `pc`. -/
structure Code where
  prog : Program
  pc : List Instr

/-- `Code.jump prog code l` is the code following the first occurrence of label `l` in `code`.
Jumping to a label that does not exist is an error. -/
def Code.jump (prog : Program) (code : List Instr) (l : Label) : Code :=
  match code with
  | [] => ⟨prog, [.udf]⟩
  | i :: rest =>
    match i with
    | .label l' => if l' = l then ⟨prog, rest⟩ else Code.jump prog rest l
    | _ => Code.jump prog rest l

/-- Weakest precondition of running code until it falls off the end of the program. It is defined
inductively, so it expresses total correctness: loops have to terminate. -/
inductive Exec : Code → (State → Prop) → State → Prop
  | done {prog : Program} {Q : State → Prop} {s : State} : Q s → Exec ⟨prog, []⟩ Q s
  | step {prog : Program} {i : Instr} {rest : List Instr} {Q : State → Prop} {s : State}
      (next : State → Prop) (jmp : Label → State → Prop) :
      i.wp next jmp s →
      (∀ s', next s' → Exec ⟨prog, rest⟩ Q s') →
      (∀ l s', jmp l s' → Exec (Code.jump prog prog l) Q s') →
      Exec ⟨prog, i :: rest⟩ Q s

theorem Exec.mono {c : Code} {Q Q' : State → Prop} {s : State}
    (hQ : ∀ s, Q s → Q' s) (h : Exec c Q s) : Exec c Q' s := by
  induction h with
  | done h => exact .done (hQ _ h)
  | step next jmp hi _ _ ih₁ ih₂ =>
    exact .step next jmp hi (fun s' h => ih₁ s' h hQ) (fun l s' h => ih₂ l s' h hQ)

theorem Exec.nil_iff {prog : Program} {Q : State → Prop} {s : State} :
    Exec ⟨prog, []⟩ Q s ↔ Q s :=
  ⟨fun h => by cases h; assumption, .done⟩

theorem Exec.cons_iff {prog : Program} {i : Instr} {rest : List Instr} {Q : State → Prop}
    {s : State} :
    Exec ⟨prog, i :: rest⟩ Q s ↔
      i.wp (Exec ⟨prog, rest⟩ Q) (fun l => Exec (Code.jump prog prog l) Q) s := by
  constructor
  · intro h
    cases h with
    | step next jmp hi hnext hjmp => exact Instr.wp_mono hnext hjmp s hi
  · exact fun h => .step _ _ h (fun _ h => h) (fun _ _ h => h)

/-! ## `WP` instance -/

abbrev Assn := State → Prop

instance : WP Code Unit Assn EPost.Nil where
  wpTrans c := ⟨fun Q _ s => Exec c (Q ()) s⟩
  wp_trans_monotone _ := fun _ _ _ _ _ hQ _ h => h.mono (hQ ())

variable {prog : Program} {rest : List Instr} {Q : Unit → Assn} {epost : EPost.Nil} {s : State}

theorem wp_nil_eq : wp (Code.mk prog []) Q epost s = Q () s :=
  propext Exec.nil_iff

theorem wp_cons_eq {i : Instr} : wp (Code.mk prog (i :: rest)) Q epost s =
    i.wp (wp (Code.mk prog rest) Q epost) (fun l => wp (Code.jump prog prog l) Q epost) s :=
  propext Exec.cons_iff

/-! ## Specifications for `vcgen`

One specification per instruction. Each one states the weakest precondition of code starting with
that instruction in terms of the weakest precondition of the code that is executed next. -/

private theorem triple_of_wp {c : Code} {pre : Assn}
    (h : ∀ s, wp c Q epost s = pre s) : Triple c pre Q epost :=
  Triple.iff.mpr (by rw [funext h]; exact PartialOrder.rel_refl)

private theorem triple_of_meet_imp_wp {c : Code} {pre₁ pre₂ : Assn}
    (h : ∀ s, pre₁ s → pre₂ s → wp c Q epost s) : Triple c (pre₁ ⊓ pre₂) Q epost :=
  Triple.iff.mpr fun s hs => by
    simp only [meet_apply, meet_prop_eq_and] at hs
    exact h s hs.1 hs.2

/-- Lets `vcgen` resolve branch targets by scanning the program for the label. -/
@[spec] theorem Code.jump_nil (l : Label) : Code.jump prog [] l = ⟨prog, [.udf]⟩ := by
  rw [Code.jump]

@[spec] theorem Code.jump_cons (i : Instr) (l : Label) :
    Code.jump prog (i :: rest) l =
      match i with
      | .label l' => if l' = l then ⟨prog, rest⟩ else Code.jump prog rest l
      | _ => Code.jump prog rest l := by
  cases i <;> rfl

@[spec] theorem Spec.nil : Triple (Code.mk prog []) (Q ()) Q epost :=
  triple_of_wp fun _ => wp_nil_eq

@[spec] theorem Spec.label (l : Label) :
    Triple (Code.mk prog (.label l :: rest)) (wp (Code.mk prog rest) Q epost) Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.mov (dst : Reg) (src : Operand) :
    Triple (Code.mk prog (.mov dst src :: rest))
      (fun s => wp (Code.mk prog rest) Q epost (s.setReg dst (src.eval s))) Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.add (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog (.add dst src1 src2 :: rest))
      (fun s => wp (Code.mk prog rest) Q epost (s.setReg dst (s.regs src1 + src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.sub (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog (.sub dst src1 src2 :: rest))
      (fun s => wp (Code.mk prog rest) Q epost (s.setReg dst (s.regs src1 - src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.mul (dst src1 src2 : Reg) :
    Triple (Code.mk prog (.mul dst src1 src2 :: rest))
      (fun s => wp (Code.mk prog rest) Q epost (s.setReg dst (s.regs src1 * s.regs src2)))
      Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.and (dst src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog (.and dst src1 src2 :: rest))
      (fun s => wp (Code.mk prog rest) Q epost (s.setReg dst (s.regs src1 &&& src2.eval s)))
      Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.cmp (src1 : Reg) (src2 : Operand) :
    Triple (Code.mk prog (.cmp src1 src2 :: rest))
      (fun s => wp (Code.mk prog rest) Q epost
        { s with flags := .ofSub (s.regs src1) (src2.eval s) }) Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.csel (dst src1 src2 : Reg) (cond : Cond) :
    Triple (Code.mk prog (.csel dst src1 src2 cond :: rest))
      (fun s => wp (Code.mk prog rest) Q epost
        (s.setReg dst (if cond.holds s.flags then s.regs src1 else s.regs src2))) Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.ldr (dst base : Reg) (off : Word) :
    Triple (Code.mk prog (.ldr dst base off :: rest))
      ((fun s => (s.mem (s.regs base + off)).isSome) ⊓
       (fun s => ∀ v, s.mem (s.regs base + off) = some v →
          wp (Code.mk prog rest) Q epost (s.setReg dst v))) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₁
    rw [wp_cons_eq]
    exact ⟨v, hv, h₂ v hv⟩

@[spec] theorem Spec.str (src base : Reg) (off : Word) :
    Triple (Code.mk prog (.str src base off :: rest))
      ((fun s => (s.mem (s.regs base + off)).isSome) ⊓
       (fun s => wp (Code.mk prog rest) Q epost (s.setMem (s.regs base + off) (s.regs src))))
      Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    rw [wp_cons_eq]
    exact ⟨h₁, h₂⟩

@[spec] theorem Spec.b (target : Label) :
    Triple (Code.mk prog (.b target :: rest)) (wp (Code.jump prog prog target) Q epost) Q epost :=
  triple_of_wp fun _ => wp_cons_eq

@[spec] theorem Spec.bcond (cond : Cond) (target : Label) :
    Triple (Code.mk prog (.bcond cond target :: rest))
      ((fun s => cond.holds s.flags = true → wp (Code.jump prog prog target) Q epost s) ⊓
       (fun s => cond.holds s.flags = false → wp (Code.mk prog rest) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    rw [wp_cons_eq]
    simp only [Instr.wp]
    split <;> simp_all

@[spec] theorem Spec.cbz (r : Reg) (target : Label) :
    Triple (Code.mk prog (.cbz r target :: rest))
      ((fun s => s.regs r = 0 → wp (Code.jump prog prog target) Q epost s) ⊓
       (fun s => s.regs r ≠ 0 → wp (Code.mk prog rest) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    rw [wp_cons_eq]
    simp only [Instr.wp]
    split <;> simp_all

@[spec] theorem Spec.cbnz (r : Reg) (target : Label) :
    Triple (Code.mk prog (.cbnz r target :: rest))
      ((fun s => s.regs r ≠ 0 → wp (Code.jump prog prog target) Q epost s) ⊓
       (fun s => s.regs r = 0 → wp (Code.mk prog rest) Q epost s)) Q epost :=
  triple_of_meet_imp_wp fun s h₁ h₂ => by
    rw [wp_cons_eq]
    simp only [Instr.wp]
    split <;> simp_all

@[spec] theorem Spec.udf :
    Triple (Code.mk prog (.udf :: rest)) (fun _ => False) Q epost :=
  Triple.iff.mpr fun _ h => h.elim

/-! ## Example: the maximum of three numbers -/

/-- Computes the unsigned maximum of `X0`, `X1` and `X2` into `X0`. -/
def max3 : Program := [
  .cmp .X0 (.reg .X1),
  .bcond .HS "skip1",
  .mov .X0 (.reg .X1),
  .label "skip1",
  .cmp .X0 (.reg .X2),
  .bcond .HS "skip2",
  .mov .X0 (.reg .X2),
  .label "skip2"
]

theorem max3_correct (a b c : Word) :
    ⦃ fun s => s.regs .X0 = a ∧ s.regs .X1 = b ∧ s.regs .X2 = c ⦄
      Code.mk max3 max3
    ⦃ fun _ s => (s.regs .X0 = a ∨ s.regs .X0 = b ∨ s.regs .X0 = c) ∧
        a ≤ s.regs .X0 ∧ b ≤ s.regs .X0 ∧ c ≤ s.regs .X0 ⦄ := by
  unfold max3
  vcgen simplifying_assumptions
  all_goals grind [Cond.holds, Flags.ofSub, Operand.eval, State.setReg]

end ToySys
