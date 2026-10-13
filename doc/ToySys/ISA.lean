import Std.Tactic.BVDecide
/-!
# A toy Arm-like instruction set architecture (ISA)

A massively simplified version of the AArch64 syntax and semantics of Kraken
(`Kraken/AArch64/Syntax.lean` and `Kraken/AArch64/Semantics.lean`).

How it differs from Kraken:
* All registers and operations are 64 bits wide, so nothing is parameterized by a bit width.
* There is a single flat `Instr` type.
* There is neither a stack pointer nor a zero register.
* Memory is a partial map from addresses to whole 64-bit words instead of bytes.
* The semantics of an instruction (`Instr.interp`) directly says which postconditions it
  guarantees, in omnisemantics style, without an intermediate type that describes its effects.

The level of abstraction is that of a disassembled `.o` file: the state has a program counter, a
program is a map from addresses to instructions, every instruction occupies 4 bytes, and branches
within a function are relative to the address of the branch instruction. Only calls (`bl`) refer to
their target by name, like a call with a relocation that the linker has not resolved yet; names are
mapped to addresses by a symbol table (`Symbols`).

## Naming scheme

For a function `f`:
* `f_code : List Instr` is its code, a closed term that does not depend on where it is loaded.
* `f_ok` is its correctness theorem. It has one hypothesis `hf : Loaded prog (syms "f") f_code`
  for `f` itself and one for each function that it calls. Nothing is assumed about how the code
  snippets are located relative to each other: if they overlap inconsistently, the hypotheses are
  contradictory.
* There is no definition named `f`, and the statement of `f_ok` refers to the address of `f` only as
  `syms "f"`. The name `f` is reserved for use inside the proof of `f_ok`, as a variable of type
  `Word` standing for that address, introduced by `generalize syms "f" = f at *`. It then reads
  like a label: `f + 8` is the address of the third instruction of `f`.

This file depends only on core Lean.
-/

namespace ToySys

/-! ## Syntax -/

abbrev Word := BitVec 64

/-- The general-purpose registers. `X30` is the link register, which holds the return address. -/
inductive Reg
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9
  | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19
  | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29
  | X30
  deriving DecidableEq, Repr

/-- The registers that a function may overwrite according to Arm's application binary interface
(ABI), the Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64): arguments and results
(`X0`-`X7`), the indirect result register (`X8`), temporaries (`X9`-`X15`) and the
intra-procedure-call scratch registers (`X16`, `X17`). -/
def Reg.callerSaved : List Reg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15, .X16, .X17]

/-- The registers that a function must preserve according to the Procedure Call Standard for the
Arm 64-bit Architecture (AAPCS64): `X19`-`X28` and the frame pointer `X29`. The platform register
`X18` and the link register `X30` are neither caller-saved nor callee-saved. -/
def Reg.calleeSaved : List Reg :=
  [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

/-- The last source operand of most instructions. -/
inductive Operand
  /-- The value of register `r`. -/
  | reg (r : Reg)
  /-- The immediate value `v`, a constant that is part of the instruction. -/
  | imm (v : Word)
  deriving DecidableEq, Repr

/-- The condition codes: predicates on the flags. -/
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

/-- The instructions. In their arguments, `dst` is the destination register, `src` a source, and
`off` an offset. -/
inductive Instr
  /-- Move: `dst := src`. -/
  | mov (dst : Reg) (src : Operand)
  /-- `dst := src1 + src2`. -/
  | add (dst src1 : Reg) (src2 : Operand)
  /-- Subtract: `dst := src1 - src2`. -/
  | sub (dst src1 : Reg) (src2 : Operand)
  /-- Multiply: `dst := src1 * src2`. -/
  | mul (dst src1 src2 : Reg)
  /-- Bitwise and: `dst := src1 &&& src2`. -/
  | and (dst src1 : Reg) (src2 : Operand)
  /-- Compare: sets the flags according to `src1 - src2`. -/
  | cmp (src1 : Reg) (src2 : Operand)
  /-- Conditional select: `dst := if cond then src1 else src2`. -/
  | csel (dst src1 src2 : Reg) (cond : Cond)
  /-- Load register: reads the word at address `base + off` into `dst`. -/
  | ldr (dst base : Reg) (off : Word)
  /-- Store register: writes `src` to the word at address `base + off`. -/
  | str (src base : Reg) (off : Word)
  /-- Branch: jumps to the address of this instruction plus `off`. -/
  | b (off : Word)
  /-- Branch conditionally: branches by `off` if `cond` holds. -/
  | bcond (cond : Cond) (off : Word)
  /-- Compare and branch on zero: branches by `off` if `r` is zero. -/
  | cbz (r : Reg) (off : Word)
  /-- Compare and branch on nonzero: branches by `off` if `r` is not zero. -/
  | cbnz (r : Reg) (off : Word)
  /-- Branch with link: calls the function named `target`, by setting `X30` to the address of the
  following instruction and jumping to the address of `target`. -/
  | bl (target : String)
  /-- Return: jumps to the address in `r`, which normally is `X30`. -/
  | ret (r : Reg)
  /-- Permanently undefined: executing it is always an error. -/
  | udf
  deriving DecidableEq, Repr

/-- A program maps addresses to instructions. Executing an address that holds no instruction is an
error. -/
abbrev Program := Word → Option Instr

/-- A symbol table, usually called `syms`, maps function names to addresses. -/
abbrev Symbols := String → Word

/-- The `code` is loaded at address `f`. -/
def Loaded (prog : Program) (f : Word) (code : List Instr) : Prop :=
  f % 4 = 0 ∧
  ∀ (i : Nat) (instr : Instr), code[i]? = some instr → prog (f + 4 * i) = some instr

/-! ## Machine state -/

/-- The condition flags, which `cmp` sets and `Cond` reads. -/
structure Flags where
  /-- Negative: the result, read as a signed number, is negative. -/
  n : Bool := false
  /-- Zero: the result is zero. -/
  z : Bool := false
  /-- Carry: the unsigned operation carried out of the top bit. -/
  c : Bool := false
  /-- Overflow: the signed operation overflowed. -/
  v : Bool := false
  deriving DecidableEq, Repr

/-- The memory. Addresses name whole words; unmapped addresses must not be accessed. -/
abbrev Mem := Word → Option Word

structure State where
  /-- The values of the registers. -/
  regs : Reg → Word
  flags : Flags
  /-- The memory. -/
  mem : Mem
  /-- The program counter: the address of the instruction that is executed next. -/
  pc : Word

/-- Sets register `r` to `v`. -/
def State.setReg (s : State) (r : Reg) (v : Word) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Sets the memory word at address `a`, mapped or not, to `v`. -/
def State.setMem (s : State) (a : Word) (v : Word) : State :=
  { s with mem := fun a' => if a' = a then some v else s.mem a' }

/-- Sets the program counter to `a`. -/
def State.setPc (s : State) (a : Word) : State :=
  { s with pc := a }

/-- Advances the program counter to the following instruction. -/
def State.next (s : State) : State := s.setPc (s.pc + 4)

/-- Moves the program counter by `off`, relative to the current instruction. -/
def State.branch (s : State) (off : Word) : State := s.setPc (s.pc + off)

/-- Evaluates an operand to its value in state `s`. -/
def Operand.eval (o : Operand) (s : State) : Word := match o with
  | .reg r => s.regs r
  | .imm v => v

/-- The flags set by comparing `a` to `b`, i.e. by the subtraction `a - b`. -/
def Flags.ofSub (a b : Word) : Flags :=
  let res := a - b
  { n := res.msb
    z := res == 0
    c := decide (b ≤ a) -- for a subtraction, carry means that there is no unsigned borrow
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

/-- Interprets a single instruction, in omnisemantics style: `i.interp syms s post` holds if
executing `i` in state `s` is safe and leads to a state satisfying `post`. `s.pc` is the address of
`i`, and the resulting state's `pc` is the address of the instruction to execute next. -/
def Instr.interp (syms : Symbols) (i : Instr) (s : State) (post : State → Prop) : Prop :=
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
  | .bl target => post ((s.setReg .X30 (s.pc + 4)).setPc (syms target))
  | .ret r => post (s.setPc (s.regs r))
  | .udf => False

/-- One step of the machine: fetches the instruction at the program counter and executes it. If
there is no instruction at that address, the machine is stuck, which is an error. -/
def Machine.step (syms : Symbols) (prog : Program) (s : State) (post : State → Prop) : Prop :=
  match prog s.pc with
  | some i => i.interp syms s post
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

/-- `eventually` in continuation-passing style (CPS): to show that `post` is eventually reached,
take one step and show that `post` is eventually reached from wherever that step leads. Unlike the
`step` constructor, this needs no intermediate postcondition. -/
theorem eventually_cps {σ : Type} {step : σ → (σ → Prop) → Prop} {post : σ → Prop} {s : σ}
    (h : step s (eventually step post)) : eventually step post s :=
  .step _ h (fun _ h => h)

/-- Transitivity of `eventually`, i.e. sequential composition: if `mid` is eventually reached, and
`post` is eventually reached from every state satisfying `mid`, then `post` is eventually reached.
This is how the correctness theorem of a callee is used in the proof of its caller. -/
theorem eventually_trans {σ : Type} {step : σ → (σ → Prop) → Prop} {mid post : σ → Prop} {s : σ}
    (h : eventually step mid s) (hk : ∀ s', mid s' → eventually step post s') :
    eventually step post s := by
  induction h with
  | done h => exact hk _ h
  | step mid' hstep _ ih => exact .step mid' hstep ih

/-- The weakest precondition (wp) of `post`: `Machine.wp syms prog post s` holds if running `prog`
from state `s` is safe and eventually reaches a state satisfying `post`. The program does not
determine where execution ends; `post` does, typically by constraining the final `pc`. -/
def Machine.wp (syms : Symbols) (prog : Program) (post : State → Prop) (s : State) : Prop :=
  eventually (Machine.step syms prog) post s

/-! ## Stepping through a program -/

/-- Fetches the instruction at `addr`, which has to be inside the code loaded at `f`. -/
theorem Loaded.fetch {instr : Instr} {addr : Word}  -- <-- determined by the goal
    {prog : Program} {f : Word} {code : List Instr} -- <-- determined by h
    (h : Loaded prog f code)   -- <-- determined by `assumption`, picks the last one, brittle
                               --     if there are multiple `Loaded` assumptions, but ok because
                               --     later we will ensure that there is only ever one
    (hm4 : (addr - f) % 4 = 0) -- <-- determined by `simp; try rfl`
    (hindex : code[((addr - f) / 4).toNat]? = some instr) -- <-- determined by `simp; try rfl`
     : prog addr = some instr := by
  rw [<- (h.right ((addr - f) / 4).toNat instr hindex)]
  congr 1
  rw [BitVec.natCast_eq_ofNat]
  rw [BitVec.ofNat_toNat]
  rw [BitVec.setWidth_eq]
  rw [show 4 * ((addr - f) / 4) = (addr - f) - (addr - f) % 4 by bv_decide]
  rw [hm4]
  bv_decide

/-- Splits one machine step into determining the program counter, fetching, and executing a given
instruction. The instruction is executed in `s.setPc a`, which equals `s`, so that the rest
of the proof uses the user-provided `a` instead of `s.pc`. -/
theorem Machine.step_of_fetch {syms : Symbols} {prog : Program} {s : State} {post : State → Prop}
    (i : Instr) (a : Word) (hpc : s.pc = a) (hfetch : prog a = some i)
    (h : i.interp syms (s.setPc a) post) : Machine.step syms prog s post := by
  subst hpc
  simp only [Machine.step, hfetch]
  exact h

/-- Starts or resumes stepping through a program: turns a weakest-precondition (wp) goal about a
state whose program counter (pc) is known to be `a` into an `eventually` goal about a state whose
`pc` is syntactically `a`, which is the form that `instr` expects. -/
theorem Machine.wp_of_pc {syms : Symbols} {prog : Program} {s : State} {post : State → Prop} {a : Word} (hpc : s.pc = a)
    (h : eventually (Machine.step syms prog) post (s.setPc a)) : Machine.wp syms prog post s := by
  subst hpc
  exact h

/-- Introduction rule for if-then-else (ite): proves a goal of the form `if c then p else q`, as
arises from a conditional branch. -/
theorem ite_intro {c p q : Prop} [Decidable c] (ht : c → p) (hf : ¬c → q) : if c then p else q := by
  split
  · next h => exact ht h
  · next h => exact hf h

-- TODO make this as powerful as Rocq's ring_simplify but without Mathlib dependency
macro "ring_simplify" : tactic => `(tactic|
  repeat (
    first
    | rw [BitVec.add_sub_cancel]
    | rw [BitVec.add_comm _ _, BitVec.add_sub_cancel]
    | rw [BitVec.sub_add_cancel]
    | rw [BitVec.sub_self]
    | rw [BitVec.add_zero]
    | rw [BitVec.zero_add]
    | rw [BitVec.sub_zero]
  )
)

/-- The part of `instr` that is the same for all instructions: one step that leaves the goal
produced by `Instr.interp`. -/
syntax "instr_step " term " at " term : tactic

macro "dsimp_proj" : tactic =>
  `(tactic| dsimp (config := { beta := false, zeta := false, iota := false, proj := true }) only)

macro_rules
  | `(tactic| instr_step $i at $a) => `(tactic| (
    refine eventually_cps (Machine.step_of_fetch $i $a ?_ (Loaded.fetch (by assumption) ?_ ?_) ?_)
    -- The current pc as computed by the proof equals the user-provided instruction address `a`
    ((try unfold State.setPc);
      first
      | bv_decide
      | (trace_state; fail "bv_decide can't prove that the user-provided instruction address matches the computed pc"))
    -- The byte offset `a - base` is a multiple of 4
    bv_decide
    -- The instruction at byte offset `a - base` of the code is `i`
    ring_simplify; (try simp); rfl
    -- simplify remainder of proof
    simp [Instr.interp, State.next, State.branch, State.setPc, State.setReg, State.setMem,
        Operand.eval]))

/-- `instr i at a` symbolically executes one instruction of a goal
`eventually (Machine.step syms prog) post s`: it checks that the program counter of `s` is `a` and
that the instruction at address `a` is `i`, and then simplifies through `Instr.interp`.

Both arguments are redundant, since the program counter is determined by the state and the
instruction by the program and the program counter. They are there so that a proof script can be
read next to a disassembly, and `instr` fails if either of them is wrong.

`a` can be any term that is equal to the program counter of `s` by `rfl`. To fetch the instruction,
`a` is split into the address `f` of a function and an offset by `SplitAddress`, and there has to be
a hypothesis `Loaded prog f code` in the context.

What is left depends on the instruction, which has to be written as `.name args` for the tactic to
recognize it:
* For a conditional branch (`.bcond`, `.cbz`, `.cbnz`) there are two goals, one for the branch being
  taken and one for it not being taken, each with the condition as a premise to introduce.
* For `.bl "g"` the goal is the `eventually` goal for the state at the entry of `g`, whose program
  counter is `syms "g"`. Use `eventually_trans` with `g_ok` to get to the state after the call, and
  `Machine.wp_of_pc` to continue from there.
* For `.ldr` and `.str` the goal still contains the condition that the address is mapped, which can
  be proved by `simp` with the relevant facts about the memory.
* For all other instructions the goal is the `eventually` goal for the next state.

To get started, use `Machine.wp_of_pc`. -/
syntax "instr " term " at " term : tactic

macro_rules
  | `(tactic| instr .bcond $c $off at $a) =>
    `(tactic| (instr_step .bcond $c $off at $a; refine ite_intro ?_ ?_))
  | `(tactic| instr .cbz $r $off at $a) =>
    `(tactic| (instr_step .cbz $r $off at $a; refine ite_intro ?_ ?_))
  | `(tactic| instr .cbnz $r $off at $a) =>
    `(tactic| (instr_step .cbnz $r $off at $a; refine ite_intro ?_ ?_))
  | `(tactic| instr $i at $a) => `(tactic| instr_step $i at $a)

/-! ## Example: the maximum of three numbers -/

/-- Computes the unsigned maximum of the three registers `X0`, `X1` and `X2` into `X0`. -/
def max3_code : List Instr := [
  .cmp .X0 (.reg .X1),
  .bcond .HS 8,
  .mov .X0 (.reg .X1),
  .cmp .X0 (.reg .X2),
  .bcond .HS 8,
  .mov .X0 (.reg .X2),
  .ret .X30
]

theorem max3_ok (syms : Symbols) (prog : Program)
    (hmax3 : Loaded prog (syms "max3") max3_code)
    (a b c : Word) (s : State) (hpc : s.pc = syms "max3")
    (ha : s.regs .X0 = a) (hb : s.regs .X1 = b) (hc : s.regs .X2 = c) :
    Machine.wp syms prog
      (fun s' => s'.pc = s.regs .X30 ∧
        (s'.regs .X0 = a ∨ s'.regs .X0 = b ∨ s'.regs .X0 = c) ∧
        a ≤ s'.regs .X0 ∧ b ≤ s'.regs .X0 ∧ c ≤ s'.regs .X0) s := by
  generalize syms "max3" = max3 at *
  refine Machine.wp_of_pc hpc ?_
  instr .cmp .X0 (.reg .X1) at max3
  instr .bcond .HS 8 at max3 + 0x4
  · intro _
    instr .cmp .X0 (.reg .X2) at max3 + 0xc
    instr .bcond .HS 8 at max3 + 0x10
    · intro _
      instr .ret .X30 at max3 + 0x18
      exact .done (by grind [Cond.holds, Flags.ofSub])
    · intro _
      instr .mov .X0 (.reg .X2) at max3 + 0x14
      instr .ret .X30 at max3 + 0x18
      exact .done (by grind [Cond.holds, Flags.ofSub])
  · intro _
    instr .mov .X0 (.reg .X1) at max3 + 0x8
    instr .cmp .X0 (.reg .X2) at max3 + 0xc
    instr .bcond .HS 8 at max3 + 0x10
    · intro _
      instr .ret .X30 at max3 + 0x18
      exact .done (by grind [Cond.holds, Flags.ofSub])
    · intro _
      instr .mov .X0 (.reg .X2) at max3 + 0x14
      instr .ret .X30 at max3 + 0x18
      exact .done (by grind [Cond.holds, Flags.ofSub])

/-! ## Example: swapping two words in memory -/

/-- Swaps the words stored at the addresses in `X0` and `X1`, using `X2` and `X3` as scratch. -/
def swap_code : List Instr := [
  .ldr .X2 .X0 0,
  .ldr .X3 .X1 0,
  .str .X3 .X0 0,
  .str .X2 .X1 0,
  .ret .X30
]

/-- Besides swapping, `swap` guarantees that it changes no other memory and no registers other than
`X2` and `X3`. That is more than the calling convention demands, and `swap_swap_ok` relies on
it. -/
theorem swap_ok (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code)
    (p q v w : Word) (s : State) (hpc : s.pc = syms "swap")
    (hp : s.regs .X0 = p) (hq : s.regs .X1 = q) (hpq : p ≠ q)
    (hv : s.mem p = some v) (hw : s.mem q = some w) :
    Machine.wp syms prog
      (fun s' => s'.pc = s.regs .X30 ∧
        s'.mem p = some w ∧ s'.mem q = some v ∧ (∀ a, a ≠ p → a ≠ q → s'.mem a = s.mem a) ∧
        ∀ r, r ≠ .X2 → r ≠ .X3 → s'.regs r = s.regs r) s := by
  generalize syms "swap" = swap at *
  refine Machine.wp_of_pc hpc ?_
  instr .ldr .X2 .X0 0 at swap
  simp [hp, hv]
  instr .ldr .X3 .X1 0 at swap + 0x4
  simp [hq, hw]
  instr .str .X3 .X0 0 at swap + 0x8
  simp [hp, hv]
  instr .str .X2 .X1 0 at swap + 0xc
  simp [hq, hw]
  instr .ret .X30 at swap + 0x10
  exact .done (by grind)

/-! ## Example: swapping twice -/

/-- Calls `swap` twice. Since there is no stack, the return address is stashed in `X9`, which
`swap` happens to leave alone. -/
def swap_swap_code : List Instr := [
  .mov .X9 (.reg .X30),
  .bl "swap",
  .bl "swap",
  .ret .X9
]

theorem swap_swap_ok (syms : Symbols) (prog : Program)
    (hswap_swap : Loaded prog (syms "swap_swap") swap_swap_code)
    (hswap : Loaded prog (syms "swap") swap_code)
    (p q v w : Word) (s : State) (hpc : s.pc = syms "swap_swap")
    (hp : s.regs .X0 = p) (hq : s.regs .X1 = q) (hpq : p ≠ q)
    (hv : s.mem p = some v) (hw : s.mem q = some w) :
    Machine.wp syms prog
      (fun s' => s'.pc = s.regs .X30 ∧ s'.mem = s.mem ∧
        ∀ r ∈ Reg.calleeSaved, s'.regs r = s.regs r) s := by
  generalize syms "swap_swap" = swap_swap at *
  refine Machine.wp_of_pc hpc ?_
  instr .mov .X9 (.reg .X30) at swap_swap
  instr .bl "swap" at swap_swap + 0x4
  refine eventually_trans
    (swap_ok syms prog hswap p q v w _ rfl (by simp [hp]) (by simp [hq]) hpq hv hw) ?_
  intro s1 ⟨hpc1, hp1, hq1, hmem1, hregs1⟩
  simp at hpc1 hp1 hq1 hmem1 hregs1
  refine Machine.wp_of_pc hpc1 ?_
  instr .bl "swap" at swap_swap + 0x8
  refine eventually_trans
    (swap_ok syms prog hswap p q w v _ rfl (by simp [hregs1, hp]) (by simp [hregs1, hq])
      hpq hp1 hq1) ?_
  intro s2 ⟨hpc2, hp2, hq2, hmem2, hregs2⟩
  simp at hpc2 hp2 hq2 hmem2 hregs2
  refine Machine.wp_of_pc hpc2 ?_
  instr .ret .X9 at swap_swap + 0xc
  refine .done ⟨?_, ?_, ?_⟩
  · grind
  · funext a
    grind
  · intro r hr
    simp [Reg.calleeSaved] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hregs2, hregs1]

/-! ## Tests: `instr` rejects a wrong instruction or a wrong address -/

/--
error: Tactic `rfl` failed: The left-hand side
  swap_code[0]?
is not definitionally equal to the right-hand side
  some (Instr.ldr Reg.X2 Reg.X1 0#64)
-/
#guard_msgs (substring := true) in
example (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code) (s : State) (hpc : s.pc = syms "swap") :
    Machine.wp syms prog (fun _ => True) s := by
  generalize syms "swap" = swap at *
  refine Machine.wp_of_pc hpc ?_
  instr .ldr .X2 .X1 0 at swap

/-- error: bv_decide can't prove that the user-provided instruction address
matches the computed pc -/
#guard_msgs (substring := true) in
example (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code) (s : State) (hpc : s.pc = syms "swap") :
    Machine.wp syms prog (fun _ => True) s := by
  generalize syms "swap" = swap at *
  refine Machine.wp_of_pc hpc ?_
  instr .ldr .X3 .X1 0 at swap + 0x4

end ToySys
