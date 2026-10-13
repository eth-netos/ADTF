/-!
# A toy Arm-like ISA

A massively simplified version of the AArch64 syntax and semantics of Kraken
(`Kraken/AArch64/Syntax.lean` and `Kraken/AArch64/Semantics.lean`).

Simplifications compared to Kraken:
* Only 64-bit registers and 64-bit operations, so nothing is parameterized by a bit width.
* A single flat `Instr` type.
* No stack pointer and no zero register.
* Memory is a partial map from addresses to whole 64-bit words instead of bytes.
* No `Effects` type: the semantics of an instruction (`Instr.interp`) directly says which
  postconditions it guarantees, in omnisemantics style.

This is closer to machine code than to assembly: there are no labels, the state has a program
counter, a program is a map from addresses to instructions, every instruction occupies 4 bytes, and
branches are relative to the address of the branch instruction.

Nothing outside of core Lean is used.
-/

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

/-- A program maps addresses to instructions. Executing an address that holds no instruction is an
error. -/
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

/-- Omnisemantics of a single instruction: `i.interp s post` holds if executing `i` in state `s`
is safe and leads to a state satisfying `post`. `s.pc` is the address of `i`, and the resulting
state's `pc` is the address of the instruction to execute next. -/
def Instr.interp (i : Instr) (s : State) (post : State → Prop) : Prop :=
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

/-- One step of the machine: fetches the instruction at the program counter and executes it. If
there is no instruction at that address, the machine is stuck, which is an error. -/
def Machine.step (prog : Program) (s : State) (post : State → Prop) : Prop :=
  match prog s.pc with
  | some i => i.interp s post
  | none => False

/-! ## Omnisemantics for any number of steps -/

/-- Lifts a single-step omnisemantics judgment `step` to any number of steps:
`eventually step post s` holds if every execution starting in `s` is safe and reaches, after
finitely many steps, a state satisfying `post`. Because it is inductive, loops have to terminate.

This is `Eventually` of Kraken (`Kraken/OmniSemantics.lean`) and the `eventually` judgment of
Charguéraud, Chlipala, Erbsen and Gruetter, "Omnisemantics: Smooth Handling of Nondeterminism",
TOPLAS 2023. -/
inductive eventually {σ : Type} (step : σ → (σ → Prop) → Prop) (post : σ → Prop) : σ → Prop
  | done {s : σ} : post s → eventually step post s
  | step {s : σ} (mid : σ → Prop) :
      step s mid →
      (∀ s', mid s' → eventually step post s') →
      eventually step post s

/-- To show that `post` is eventually reached, take one step and show that `post` is eventually
reached from wherever that step leads. Unlike the `step` constructor, this needs no intermediate
postcondition. -/
theorem eventually_cps {σ : Type} {step : σ → (σ → Prop) → Prop} {post : σ → Prop} {s : σ}
    (h : step s (eventually step post)) : eventually step post s :=
  .step _ h (fun _ h => h)

/-- `Machine.wp prog post s` holds if running `prog` from state `s` is safe and eventually reaches
a state satisfying `post`. The program does not determine where execution ends; `post` does,
typically by constraining the final `pc`. -/
def Machine.wp (prog : Program) (post : State → Prop) (s : State) : Prop :=
  eventually (Machine.step prog) post s

/-! ## Stepping through a program -/

/-- Splits one machine step into determining the `pc`, fetching, and executing a given
instruction. The instruction is executed in `s.setPc a`, which equals `s`, so that the address
arithmetic of the instruction happens on `a` instead of on `s.pc`. -/
theorem Machine.step_of_fetch {prog : Program} {s : State} {post : State → Prop} (i : Instr)
    (a : Word) (hpc : s.pc = a) (hfetch : prog a = some i) (h : i.interp (s.setPc a) post) :
    Machine.step prog s post := by
  subst hpc
  simp only [Machine.step, hfetch]
  exact h

/-- `instr i at a` symbolically executes one instruction of a goal
`eventually (Machine.step prog) post s`. It applies `eventually_cps`, checks that the current `pc`
is `a` and that the instruction at address `a` is `i`, and simplifies through `Instr.interp`.

Both arguments are redundant, since the `pc` is determined by the state and the instruction by the
program and the `pc`, but they make proof scripts readable, and unlike comments they are checked.

`instr i at a using h₁, h₂, ...` additionally passes the given facts to the simplifier that
executes the instruction, e.g. facts about register and memory contents needed by a load or store.
Hypotheses in the context are not used unless they are listed there.

The program must be a `Program.ofList`, and `s.pc = a` must hold by assumption or by `rfl`. -/
syntax "instr " term " at " term (" using " term,+)? : tactic

open Lean in
macro_rules
  | `(tactic| instr $i at $a $[using $hs,*]?) => do
    let hs : Array Term := match hs with
      | some hs => hs.getElems
      | none => #[]
    `(tactic| (
      refine eventually_cps (Machine.step_of_fetch $i $a ?_ ?_ ?_)
      focus first
        | assumption
        | rfl
        | fail "instr: the current pc is not the given address"
      focus first
        | (simp [Program.ofList]; done)
        | fail "instr: the instruction at the given address is not the given one"
      simp [Instr.interp, State.next, State.branch, State.setPc, State.setReg, State.setMem,
        Operand.eval, $[$hs:term],*]))

/-- Proves a goal of the form `if c then p else q`, as left by `instr` for a conditional branch.
(`split` does not work on these goals: it fails to simplify the `if` using the new hypothesis.) -/
theorem ite_intro {c p q : Prop} [Decidable c] (ht : c → p) (hf : ¬c → q) : if c then p else q := by
  split
  · next h => exact ht h
  · next h => exact hf h

/-! ## Example: the maximum of three numbers -/

/-- Computes the unsigned maximum of `X0`, `X1` and `X2` into `X0`. -/
def max3 : Program := .ofList 0x1000 [
  .cmp .X0 (.reg .X1),
  .bcond .HS 8,
  .mov .X0 (.reg .X1),
  .cmp .X0 (.reg .X2),
  .bcond .HS 8,
  .mov .X0 (.reg .X2)
]

theorem max3_correct (a b c : Word) (s : State) (hpc : s.pc = 0x1000)
    (ha : s.regs .X0 = a) (hb : s.regs .X1 = b) (hc : s.regs .X2 = c) :
    Machine.wp max3
      (fun s' => s'.pc = 0x1018 ∧ (s'.regs .X0 = a ∨ s'.regs .X0 = b ∨ s'.regs .X0 = c) ∧
        a ≤ s'.regs .X0 ∧ b ≤ s'.regs .X0 ∧ c ≤ s'.regs .X0) s := by
  unfold Machine.wp max3
  instr .cmp .X0 (.reg .X1) at 0x1000
  instr .bcond .HS 8 at 0x1004
  apply ite_intro <;> intro _
  · instr .cmp .X0 (.reg .X2) at 0x100c
    instr .bcond .HS 8 at 0x1010
    apply ite_intro <;> intro _
    · exact .done (by grind [Cond.holds, Flags.ofSub])
    · instr .mov .X0 (.reg .X2) at 0x1014
      exact .done (by grind [Cond.holds, Flags.ofSub])
  · instr .mov .X0 (.reg .X1) at 0x1008
    instr .cmp .X0 (.reg .X2) at 0x100c
    instr .bcond .HS 8 at 0x1010
    apply ite_intro <;> intro _
    · exact .done (by grind [Cond.holds, Flags.ofSub])
    · instr .mov .X0 (.reg .X2) at 0x1014
      exact .done (by grind [Cond.holds, Flags.ofSub])

/-! ## Example: swapping two words in memory -/

/-- Swaps the words stored at the addresses in `X0` and `X1`, using `X2` and `X3` as scratch. -/
def swap : Program := .ofList 0x2000 [
  .ldr .X2 .X0 0,
  .ldr .X3 .X1 0,
  .str .X3 .X0 0,
  .str .X2 .X1 0
]

theorem swap_correct (p q v w : Word) (s : State) (hpc : s.pc = 0x2000)
    (hp : s.regs .X0 = p) (hq : s.regs .X1 = q) (hpq : p ≠ q)
    (hv : s.mem p = some v) (hw : s.mem q = some w) :
    Machine.wp swap
      (fun s' => s'.pc = 0x2010 ∧ s'.mem p = some w ∧ s'.mem q = some v ∧
        ∀ a, a ≠ p → a ≠ q → s'.mem a = s.mem a) s := by
  unfold Machine.wp swap
  instr .ldr .X2 .X0 0 at 0x2000 using hp, hv
  instr .ldr .X3 .X1 0 at 0x2004 using hq, hw
  instr .str .X3 .X0 0 at 0x2008 using hp, hv
  instr .str .X2 .X1 0 at 0x200c using hq, hw, hpq
  exact .done (by grind)

/-! ## Tests: `instr` rejects a wrong instruction or a wrong address -/

/--
error: instr: the instruction at the given address is not the given one
case refine_2
s : State
hpc : s.pc = 8192
⊢ Program.ofList 8192
      [Instr.ldr Reg.X2 Reg.X0 0, Instr.ldr Reg.X3 Reg.X1 0, Instr.str Reg.X3 Reg.X0 0, Instr.str Reg.X2 Reg.X1 0]
      8192 =
    some (Instr.ldr Reg.X2 Reg.X1 0)
-/
#guard_msgs in
example (s : State) (hpc : s.pc = 0x2000) : Machine.wp swap (fun _ => True) s := by
  unfold Machine.wp swap
  instr .ldr .X2 .X1 0 at 0x2000

/--
error: instr: the current pc is not the given address
case refine_1
s : State
hpc : s.pc = 8192
⊢ s.pc = 8196
-/
#guard_msgs in
example (s : State) (hpc : s.pc = 0x2000) : Machine.wp swap (fun _ => True) s := by
  unfold Machine.wp swap
  instr .ldr .X2 .X0 0 at 0x2004

end ToySys
