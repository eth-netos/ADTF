import Std.Tactic.BVDecide
/-!
# A toy Arm-like instruction set architecture (ISA)

A massively simplified version of the AArch64 syntax and semantics of Kraken
(`Kraken/AArch64/Syntax.lean` and `Kraken/AArch64/Semantics.lean`).

How it differs from Kraken:
* All registers and operations are 64 bits wide, so nothing is parameterized by
  a bit width.
* There is a single flat `Instr` type.
* There is neither a stack pointer nor a zero register.
* The core has no memory of its own. Memory accesses read and write whole 64-bit
  words, and they all go to the platform, be it to memory or to memory-mapped
  input/output (MMIO) registers.
* The semantics of an instruction (`Instr.interp`) produces an `Effects` value
  with fewer kinds of effects: it either finishes in a new state, fails, or
  reads from or writes to memory. What the platform does with memory accesses
  is not defined here: `Platform P` is the interface that a platform with state
  `P` implements.
* Instructions are not fetched from memory but from a separate `Program`.

The level of abstraction is that of a disassembled `.o` file: the state has a
program counter, a program is a map from addresses to instructions, every
instruction occupies 4 bytes, and branches within a function are relative to the
address of the branch instruction. Only calls (`bl`) refer to their target by
name, like a call with a relocation that the linker has not resolved yet; names
are mapped to addresses by a symbol table (`Symbols`).

## Naming scheme

For a function `f`:
* `f_code : List Instr` is its code, a closed term that does not depend on where
  it is loaded.
* `f_ok` is its correctness theorem. It has one hypothesis `hf : Loaded prog
  (syms "f") f_code` for `f` itself and one for each function that it calls.
  Nothing is assumed about how the code snippets are located relative to each
  other: if they overlap inconsistently, the hypotheses are contradictory.
* There is no definition named `f`, and the statement of `f_ok` refers to the
  address of `f` only as `syms "f"`. The name `f` is reserved for use inside the
  proof of `f_ok`, as a variable of type `Word` standing for that address,
  introduced by `generalize syms "f" = f at *`. It then reads like a label: `f +
  8` is the address of the third instruction of `f`.

This file depends only on core Lean.
-/

namespace ToySys

/-! ## Syntax -/

abbrev Word := BitVec 64

/-- The general-purpose registers. `X30` is the link register, which holds the
return address. -/
inductive Reg
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9
  | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19
  | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29
  | X30
  deriving DecidableEq, Repr

/-- The registers that a function may overwrite according to Arm's application
binary interface (ABI), the Procedure Call Standard for the Arm 64-bit
Architecture (AAPCS64): arguments and results (`X0`-`X7`), the indirect result
register (`X8`), temporaries (`X9`-`X15`) and the intra-procedure-call scratch
registers (`X16`, `X17`). -/
def Reg.callerSaved : List Reg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9,
   .X10, .X11, .X12, .X13, .X14, .X15, .X16, .X17]

/-- The registers that a function must preserve according to the Procedure Call
Standard for the Arm 64-bit Architecture (AAPCS64): `X19`-`X28` and the frame
pointer `X29`. The platform register `X18` and the link register `X30` are
neither caller-saved nor callee-saved. -/
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
  /-- Unsigned higher or same: after `cmp a b`, holds if `a ≥ b` as unsigned
  numbers. -/
  | HS
  /-- Unsigned lower: after `cmp a b`, holds if `a < b` as unsigned numbers. -/
  | LO
  /-- Unsigned higher: after `cmp a b`, holds if `a > b` as unsigned numbers. -/
  | HI
  /-- Unsigned lower or same: after `cmp a b`, holds if `a ≤ b` as unsigned
  numbers. -/
  | LS
  /-- Signed greater or equal: after `cmp a b`, holds if `a ≥ b` as signed
  numbers. -/
  | GE
  /-- Signed less than: after `cmp a b`, holds if `a < b` as signed numbers. -/
  | LT
  /-- Signed greater than: after `cmp a b`, holds if `a > b` as signed
  numbers. -/
  | GT
  /-- Signed less or equal: after `cmp a b`, holds if `a ≤ b` as signed
  numbers. -/
  | LE
  deriving DecidableEq, Repr

/-- The instructions. In their arguments, `dst` is the destination register,
`src` a source, and `off` an offset. -/
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
  /-- Branch with link: calls the function named `target`, by setting `X30` to
  the address of the following instruction and jumping to the address of
  `target`. -/
  | bl (target : String)
  /-- Return: jumps to the address in `r`, which normally is `X30`. -/
  | ret (r : Reg)
  /-- Permanently undefined: executing it is always an error. -/
  | udf
  deriving DecidableEq, Repr

/-- A program maps addresses to instructions. Executing an address that holds no
instruction is an error. -/
abbrev Program := Word → Option Instr

/-- A symbol table, usually called `syms`, maps function names to addresses. -/
abbrev Symbols := String → Word

/-- The `code` is loaded at address `f`. -/
def Loaded (prog : Program) (f : Word) (code : List Instr) : Prop :=
  f % 4 = 0 ∧
  ∀ (i : Nat) (instr : Instr),
    code[i]? = some instr → prog (f + 4 * i) = some instr

/-! ## Core state -/

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

structure State where
  /-- The values of the registers. -/
  regs : Reg → Word
  flags : Flags
  /-- The program counter: the address of the instruction that is executed
  next. -/
  pc : Word

/-- Sets register `r` to `v`. -/
def State.setReg (s : State) (r : Reg) (v : Word) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Sets the program counter to `a`. -/
def State.setPc (s : State) (a : Word) : State :=
  { s with pc := a }

/-- Evaluates an operand to its value in state `s`. -/
def Operand.eval (o : Operand) (s : State) : Word := match o with
  | .reg r => s.regs r
  | .imm v => v

/-- The flags set by comparing `a` to `b`, i.e. by the subtraction `a - b`. -/
def Flags.ofSub (a b : Word) : Flags :=
  let res := a - b
  { n := res.msb
    z := res == 0
    -- for a subtraction, carry means that there is no unsigned borrow
    c := decide (b ≤ a)
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

/-- What executing an instruction does, as a tree whose leaves are the possible
outcomes. Adapted from `Effects` of Kraken (`Kraken/AArch64/Semantics.lean`),
with only the kinds of effects needed here. Unlike in Kraken, there is one kind
of read and one kind of write for all memory accesses, because memory belongs to
the platform. -/
inductive Effects where
  /-- The instruction finished, in state `s`. -/
  | done (s : State)
  /-- Executing the instruction is an error. -/
  | error (msg : String)
  /-- A read of the word at address `addr`, which the platform answers. `ret`
  continues with the value read. -/
  | mem_read (addr : Word) (ret : Word -> Effects)
  /-- A write of `v` to the word at address `addr`, which the platform handles.
  `ret` continues afterwards. -/
  | mem_write (addr : Word) (v : Word) (ret : Effects)

/-- Interprets a single instruction: `i.interp syms s next jmp` executes `i` in
state `s`, where `s.pc` is the address of `i`, and either
* falls through to the following instruction, continuing with `next`, or
* jumps (`jmp`) to an address `a`, continuing with `jmp a`.

The instruction only decides between the two and computes the target of a jump.
It does not update the program counter: the states passed to `next` and `jmp`
still have the `pc` of `s`. -/
def Instr.interp (syms : Symbols) (i : Instr) (s : State)
    (next : State -> Effects) (jmp : Word -> State -> Effects) : Effects :=
  match i with
  | .mov dst src => next (s.setReg dst (src.eval s))
  | .add dst src1 src2 => next (s.setReg dst (s.regs src1 + src2.eval s))
  | .sub dst src1 src2 => next (s.setReg dst (s.regs src1 - src2.eval s))
  | .mul dst src1 src2 => next (s.setReg dst (s.regs src1 * s.regs src2))
  | .and dst src1 src2 => next (s.setReg dst (s.regs src1 &&& src2.eval s))
  | .cmp src1 src2 =>
    next { s with flags := .ofSub (s.regs src1) (src2.eval s) }
  | .csel dst src1 src2 cond =>
    next (s.setReg dst
      (if cond.holds s.flags then s.regs src1 else s.regs src2))
  | .ldr dst base off =>
    .mem_read (s.regs base + off) (fun v => next (s.setReg dst v))
  | .str src base off => .mem_write (s.regs base + off) (s.regs src) (next s)
  | .b off => jmp (s.pc + off) s
  | .bcond cond off => if cond.holds s.flags then jmp (s.pc + off) s else next s
  | .cbz r off => if s.regs r = 0 then jmp (s.pc + off) s else next s
  | .cbnz r off => if s.regs r ≠ 0 then jmp (s.pc + off) s else next s
  | .bl target => jmp (syms target) (s.setReg .X30 (s.pc + 4))
  | .ret r => jmp (s.regs r) s
  | .udf => .error "udf"

/-- One step of the core: fetches the instruction at the program counter,
executes it, and updates the program counter, to the following instruction if
the instruction fell through and to the target if it jumped. If there is no
instruction at the program counter, the core is stuck, which is an error. -/
def Core.step (syms : Symbols) (prog : Program) (s : State) : Effects :=
  match prog s.pc with
  | some i =>
    i.interp syms s
      (fun s' => .done (s'.setPc (s.pc + 4)))
      (fun a s' => .done (s'.setPc a))
  | none => .error "no instruction at the program counter"

/-- What a platform with state `P` does with the memory accesses of a core, in
omnisemantics style:
* `read a p post` holds if a read from address `a` in platform state `p` is safe
  and answers a value `v` and leaves a state `p'` such that `post v p'`,
* `write a v p post` holds if a write of `v` to address `a` in platform state
  `p` is safe and leaves a state `p'` such that `post p'`. -/
structure Platform (P : Type) where
  read : Word -> P -> (Word -> P -> Prop) -> Prop
  write : Word -> Word -> P -> (P -> Prop) -> Prop

/-- The weakest precondition (wp) of effects on a platform: `e.wp pl post p`
holds if the effects `e` are safe on platform `pl` in platform state `p`, and
lead to a core state `s` and platform state `p'` such that `post s p'`. -/
@[simp] def Effects.wp {P : Type} (pl : Platform P)
    (post : State -> P -> Prop) : Effects -> P -> Prop
  | .done s, p => post s p
  | .error _, _ => False
  | .mem_read a ret, p => pl.read a p (fun v p' => (ret v).wp pl post p')
  | .mem_write a v ret, p => pl.write a v p (fun p' => ret.wp pl post p')

/-- Pushes `Effects.wp` into the branches of an `if`, as arises from a conditional
branch, so that `ite_intro` applies. -/
theorem Effects.wp_ite {P : Type} {pl : Platform P}
    {post : State -> P -> Prop} {p : P} {c : Prop} [Decidable c]
    (a b : Effects) :
    (if c then a else b).wp pl post p =
      if c then a.wp pl post p else b.wp pl post p := by
  split <;> rfl

/-- One step of the core on platform `pl`, in omnisemantics style, on the state
of both: `Core.stepWp pl syms prog (s, p) post` holds if a step of the core in
state `s`, with the platform in state `p`, is safe and leads to states that
satisfy `post`. -/
def Core.stepWp {P : Type} (pl : Platform P) (syms : Symbols) (prog : Program)
    (sp : Prod State P) (post : Prod State P -> Prop) : Prop :=
  (Core.step syms prog sp.1).wp pl (fun s p => post (s, p)) sp.2

/-! ## Omnisemantics for any number of steps -/

/-- Lifts a single-step omnisemantics judgment `step` to any number of steps:
`eventually step post s` holds if every execution starting in `s` is safe and
reaches, after finitely many steps, a state satisfying `post`. Because it is
inductive, loops have to terminate.

This is `Eventually` of Kraken (`Kraken/OmniSemantics.lean`) and the
`eventually` judgment of Charguéraud, Chlipala, Erbsen and Gruetter,
"Omnisemantics: Smooth Handling of Nondeterminism", TOPLAS 2023. -/
inductive eventually {σ : Type} (step : σ → (σ → Prop) → Prop)
    (post : σ → Prop) : σ → Prop
  | done {s : σ} : post s → eventually step post s
  | step {s : σ} (mid : σ → Prop) :
      step s mid →
      (∀ s', mid s' → eventually step post s') →
      eventually step post s

/-- `eventually` in continuation-passing style (CPS): to show that `post` is
eventually reached, take one step and show that `post` is eventually reached
from wherever that step leads. Unlike the `step` constructor, this needs no
intermediate postcondition. -/
theorem eventually_cps {σ : Type} {step : σ → (σ → Prop) → Prop}
    {post : σ → Prop} {s : σ} (h : step s (eventually step post)) :
    eventually step post s :=
  .step _ h (fun _ h => h)

/-- Transitivity of `eventually`, i.e. sequential composition: if `mid` is
eventually reached, and `post` is eventually reached from every state satisfying
`mid`, then `post` is eventually reached. This is how the correctness theorem of
a callee is used in the proof of its caller. -/
theorem eventually_trans {σ : Type} {step : σ → (σ → Prop) → Prop}
    {mid post : σ → Prop} {s : σ} (h : eventually step mid s)
    (hk : ∀ s', mid s' → eventually step post s') :
    eventually step post s := by
  induction h with
  | done h => exact hk _ h
  | step mid' hstep _ ih => exact .step mid' hstep ih

/-- The weakest precondition (wp) of `post`: `Core.wp pl syms prog post (s, p)`
holds if running `prog` on platform `pl`, from core state `s` and platform state
`p`, is safe and eventually reaches states satisfying `post`. The program does
not determine where execution ends; `post` does, typically by constraining the
final `pc`. -/
def Core.wp {P : Type} (pl : Platform P) (syms : Symbols) (prog : Program)
    (post : Prod State P -> Prop) (sp : Prod State P) : Prop :=
  eventually (Core.stepWp pl syms prog) post sp

/-! ## Stepping through a program -/

/-- Fetches the instruction at `addr`, which has to be inside the code loaded at
`f`. -/
theorem Loaded.fetch
    {instr : Instr} {addr : Word}  -- <-- determined by the goal
    {prog : Program} {f : Word} {code : List Instr} -- <-- determined by h
    (h : Loaded prog f code)   -- <-- determined by `assumption`, picks the
                               --     last one, brittle if there are multiple
                               --     `Loaded` assumptions, but ok because
                               --     later we will ensure that there is only
                               --     ever one
    (hm4 : (addr - f) % 4 = 0) -- <-- determined by `simp; try rfl`
    (hindex : code[((addr - f) / 4).toNat]? = some instr)
                               -- <-- determined by `simp; try rfl`
     : prog addr = some instr := by
  rw [<- (h.right ((addr - f) / 4).toNat instr hindex)]
  congr 1
  rw [BitVec.natCast_eq_ofNat]
  rw [BitVec.ofNat_toNat]
  rw [BitVec.setWidth_eq]
  rw [show 4 * ((addr - f) / 4) = (addr - f) - (addr - f) % 4 by bv_decide]
  rw [hm4]
  bv_decide

/-- Splits one machine step into determining the program counter, fetching, and
executing a given instruction. The instruction is executed in `s.setPc a`, which
equals `s`, so that the rest of the proof uses the user-provided `a` instead of
`s.pc`. -/
theorem Core.step_of_fetch {P : Type} {pl : Platform P} {syms : Symbols}
    {prog : Program} {s : State} {p : P} {post : Prod State P -> Prop}
    (i : Instr) (a : Word) (hpc : s.pc = a) (hfetch : prog a = some i)
    (h : (i.interp syms (s.setPc a)
      (fun s' => .done (s'.setPc (a + 4)))
      (fun a' s' => .done (s'.setPc a'))).wp pl (fun s' p' => post (s', p')) p) :
    Core.stepWp pl syms prog (s, p) post := by
  subst hpc
  simp only [Core.stepWp, Core.step, hfetch]
  exact h

/-- Starts or resumes stepping through a program: turns a weakest-precondition
(wp) goal about a state whose program counter (pc) is known to be `a` into an
`eventually` goal about a state whose `pc` is syntactically `a`, which is the
form that `instr` expects. -/
theorem Core.wp_of_pc {P : Type} {pl : Platform P} {syms : Symbols}
    {prog : Program} {sp : Prod State P} {post : Prod State P -> Prop} {a : Word}
    (hpc : sp.1.pc = a)
    (h : eventually (Core.stepWp pl syms prog) post (sp.1.setPc a, sp.2)) :
    Core.wp pl syms prog post sp := by
  subst hpc
  exact h

/-- Introduction rule for if-then-else (ite): proves a goal of the form `if c
then p else q`, as arises from a conditional branch. -/
theorem ite_intro {c p q : Prop} [Decidable c] (ht : c → p) (hf : ¬c → q) :
    if c then p else q := by
  split
  · next h => exact ht h
  · next h => exact hf h

-- TODO make this as powerful as Rocq's ring_simplify but without Mathlib
-- dependency
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

/-- The part of `instr` that is the same for all instructions: one step that
leaves the goal produced by `Instr.interp`. -/
syntax "instr_step " term " at " term : tactic

macro "dsimp_proj" : tactic =>
  `(tactic| dsimp (config :=
      { beta := false, zeta := false, iota := false, proj := true }) only)

macro_rules
  | `(tactic| instr_step $i at $a) => `(tactic| (
    refine eventually_cps (Core.step_of_fetch $i $a ?_
      (Loaded.fetch (by assumption) ?_ ?_) ?_)
    -- The current pc as computed by the proof equals the user-provided
    -- instruction address `a`
    ((try unfold State.setPc);
      first
      | bv_decide
      | (trace_state;
         fail "bv_decide can't prove that the user-provided instruction \
               address matches the computed pc"))
    -- The byte offset `a - base` is a multiple of 4
    bv_decide
    -- The instruction at byte offset `a - base` of the code is `i`
    ring_simplify; (try simp); rfl
    -- What remains is the effects of `i`
    simp only [Instr.interp]))

/-- Simplifies the effects of an instruction, as left by `instr_step`. -/
macro "instr_simp" : tactic => `(tactic|
  simp [Effects.wp, State.setPc, State.setReg, Operand.eval])

/-- `instr i at a` symbolically executes one instruction of a goal `eventually
(Core.stepWp pl syms prog) post (s, p)`: it checks that the program counter of
`s` is `a` and that the instruction at address `a` is `i`, and then simplifies
through `Instr.interp` and `Effects.wp`.

Both arguments are redundant, since the program counter is determined by the
state and the instruction by the program and the program counter. They are there
so that a proof script can be read next to a disassembly, and `instr` fails if
either of them is wrong.

`a` can be any term that `bv_decide` can show to be equal to the program counter
of `s`. To fetch the instruction, there has to be a hypothesis
`Loaded prog f code` in the context such that `a - f` simplifies to the byte
offset of the instruction in `code`.

What is left depends on the instruction, which has to be written as `.name args`
for the tactic to recognize it:
* For a conditional branch (`.bcond`, `.cbz`, `.cbnz`) there are two goals, one
  for the branch being taken and one for it not being taken, each with the
  condition as a premise to introduce.
* For `.bl "g"` the goal is the `eventually` goal for the state at the entry of
  `g`, whose program counter is `syms "g"`. Use `eventually_trans` with `g_ok`
  to get to the state after the call, and `Core.wp_of_pc` to continue from
  there.
* For `.ldr` and `.str` the goal is what the platform's `read` or `write` says
  about the access, which can be simplified by `simp` with the relevant facts
  about the platform.
* For all other instructions the goal is the `eventually` goal for the next
  state.

To get started, use `Core.wp_of_pc`. -/
syntax "instr " term " at " term : tactic

-- For a conditional branch, `Effects.wp` is pushed into the two branches before
-- anything else is simplified: simplifying the condition first would leave the
-- `Decidable` instance of the `if` behind, which `Effects.wp_ite` then cannot
-- match.
macro_rules
  | `(tactic| instr .bcond $c $off at $a) =>
    `(tactic| (instr_step .bcond $c $off at $a; simp only [Effects.wp_ite];
               refine ite_intro ?_ ?_ <;> instr_simp))
  | `(tactic| instr .cbz $r $off at $a) =>
    `(tactic| (instr_step .cbz $r $off at $a; simp only [Effects.wp_ite];
               refine ite_intro ?_ ?_ <;> instr_simp))
  | `(tactic| instr .cbnz $r $off at $a) =>
    `(tactic| (instr_step .cbnz $r $off at $a; simp only [Effects.wp_ite];
               refine ite_intro ?_ ?_ <;> instr_simp))
  | `(tactic| instr $i at $a) => `(tactic| (instr_step $i at $a; instr_simp))

/-! ## Example: the maximum of three numbers -/

/-- Computes the unsigned maximum of the three registers `X0`, `X1` and `X2`
into `X0`. -/
def max3_code : List Instr := [
  .cmp .X0 (.reg .X1),
  .bcond .HS 8,
  .mov .X0 (.reg .X1),
  .cmp .X0 (.reg .X2),
  .bcond .HS 8,
  .mov .X0 (.reg .X2),
  .ret .X30
]

theorem max3_ok {P : Type} (pl : Platform P) (syms : Symbols) (prog : Program)
    (hmax3 : Loaded prog (syms "max3") max3_code)
    (a b c : Word) (s : State) (ps : P) (hpc : s.pc = syms "max3")
    (ha : s.regs .X0 = a) (hb : s.regs .X1 = b) (hc : s.regs .X2 = c) :
    Core.wp pl syms prog
      (fun sp => sp.1.pc = s.regs .X30 ∧
        (sp.1.regs .X0 = a ∨ sp.1.regs .X0 = b ∨ sp.1.regs .X0 = c) ∧
        a ≤ sp.1.regs .X0 ∧ b ≤ sp.1.regs .X0 ∧ c ≤ sp.1.regs .X0) (s, ps) := by
  generalize syms "max3" = max3 at *
  refine Core.wp_of_pc hpc ?_
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

/-! ## A platform that is nothing but memory -/

/-- A memory that maps the addresses of some words to their values. -/
abbrev Mem := Word → Option Word

/-- Sets the word at address `a` of memory `m` to `v`. -/
def Mem.set (m : Mem) (a v : Word) : Mem :=
  fun a' => if a' = a then some v else m a'

/-- The platform whose state is a `Mem`. Reading or writing an address that is
not mapped is an error. -/
def memPlatform : Platform Mem where
  read a m post := match m a with
    | some v => post v m
    | none => False
  write a v m post := match m a with
    | some _ => post (m.set a v)
    | none => False

/-! ## Example: swapping two words in memory -/

/-- Swaps the words stored at the addresses in `X0` and `X1`, using `X2` and
`X3` as scratch. -/
def swap_code : List Instr := [
  .ldr .X2 .X0 0,
  .ldr .X3 .X1 0,
  .str .X3 .X0 0,
  .str .X2 .X1 0,
  .ret .X30
]

/-- Besides swapping, `swap` guarantees that it changes no other memory and no
registers other than `X2` and `X3`. That is more than the calling convention
demands, and `swap_swap_ok` relies on it. -/
theorem swap_ok (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code)
    (p q v w : Word) (s : State) (m : Mem) (hpc : s.pc = syms "swap")
    (hp : s.regs .X0 = p) (hq : s.regs .X1 = q) (hpq : p ≠ q)
    (hv : m p = some v) (hw : m q = some w) :
    Core.wp memPlatform syms prog
      (fun sp => sp.1.pc = s.regs .X30 ∧
        sp.2 p = some w ∧ sp.2 q = some v ∧
        (∀ a, a ≠ p → a ≠ q → sp.2 a = m a) ∧
        (∀ r, r ≠ .X2 → r ≠ .X3 → sp.1.regs r = s.regs r))
      (s, m) := by
  generalize syms "swap" = swap at *
  refine Core.wp_of_pc hpc ?_
  instr .ldr .X2 .X0 0 at swap
  simp [memPlatform, hp, hv]
  instr .ldr .X3 .X1 0 at swap + 0x4
  simp [hq, hw]
  instr .str .X3 .X0 0 at swap + 0x8
  simp [hp, hv]
  instr .str .X2 .X1 0 at swap + 0xc
  simp [Mem.set, hq, hw, Ne.symm hpq]
  instr .ret .X30 at swap + 0x10
  exact .done (by simp [Mem.set]; grind)

/-! ## Example: swapping twice -/

/-- Calls `swap` twice. Since there is no stack, the return address is stashed
in `X9`, which `swap` happens to leave alone. -/
def swap_swap_code : List Instr := [
  .mov .X9 (.reg .X30),
  .bl "swap",
  .bl "swap",
  .ret .X9
]

theorem swap_swap_ok (syms : Symbols) (prog : Program)
    (hswap_swap : Loaded prog (syms "swap_swap") swap_swap_code)
    (hswap : Loaded prog (syms "swap") swap_code)
    (p q v w : Word) (s : State) (m : Mem) (hpc : s.pc = syms "swap_swap")
    (hp : s.regs .X0 = p) (hq : s.regs .X1 = q) (hpq : p ≠ q)
    (hv : m p = some v) (hw : m q = some w) :
    Core.wp memPlatform syms prog
      (fun sp => sp.1.pc = s.regs .X30 ∧ sp.2 = m ∧
        ∀ r ∈ Reg.calleeSaved, sp.1.regs r = s.regs r) (s, m) := by
  generalize syms "swap_swap" = swap_swap at *
  refine Core.wp_of_pc hpc ?_
  instr .mov .X9 (.reg .X30) at swap_swap
  instr .bl "swap" at swap_swap + 0x4
  refine eventually_trans
    (swap_ok syms prog hswap p q v w _ _ rfl (by simp [hp]) (by simp [hq])
      hpq hv hw) ?_
  intro s1 ⟨hpc1, hp1, hq1, hmem1, hregs1⟩
  simp at hpc1 hp1 hq1 hmem1 hregs1
  refine Core.wp_of_pc hpc1 ?_
  instr .bl "swap" at swap_swap + 0x8
  refine eventually_trans
    (swap_ok syms prog hswap p q w v _ _ rfl (by simp [hregs1, hp])
      (by simp [hregs1, hq]) hpq hp1 hq1) ?_
  intro s2 ⟨hpc2, hp2, hq2, hmem2, hregs2⟩
  simp at hpc2 hp2 hq2 hmem2 hregs2
  refine Core.wp_of_pc hpc2 ?_
  instr .ret .X9 at swap_swap + 0xc
  refine .done ⟨?_, ?_, ?_⟩
  · grind
  · funext a
    grind
  · intro r hr
    simp [Reg.calleeSaved] at hr
    rcases hr with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hregs2, hregs1]

/-! ## Tests: `instr` rejects a wrong instruction or a wrong address -/

/--
error: Tactic `rfl` failed: The left-hand side
  swap_code[0]?
is not definitionally equal to the right-hand side
  some (Instr.ldr Reg.X2 Reg.X1 0#64)
-/
#guard_msgs (substring := true) in
example {P : Type} (pl : Platform P) (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code) (s : State) (ps : P)
    (hpc : s.pc = syms "swap") :
    Core.wp pl syms prog (fun _ => True) (s, ps) := by
  generalize syms "swap" = swap at *
  refine Core.wp_of_pc hpc ?_
  instr .ldr .X2 .X1 0 at swap

/-- error: bv_decide can't prove that the user-provided instruction address
matches the computed pc -/
#guard_msgs (substring := true) in
example {P : Type} (pl : Platform P) (syms : Symbols) (prog : Program)
    (hswap : Loaded prog (syms "swap") swap_code) (s : State) (ps : P)
    (hpc : s.pc = syms "swap") :
    Core.wp pl syms prog (fun _ => True) (s, ps) := by
  generalize syms "swap" = swap at *
  refine Core.wp_of_pc hpc ?_
  instr .ldr .X3 .X1 0 at swap + 0x4

end ToySys
