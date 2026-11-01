# A loop rule for the beacon core

This document records the design of a proof rule for loops in the beacon
core of `aarch64-obj-verification-design.md` (section 1.3.1), and what was
found when it was formalized. The C library's functions with loops
(`strlen`, `memcpy`, `memcmp`, ...) need such a rule (section 1.2.1 there).

The rule is in Kraken, branch `aarch64-atf`, in
`Kraken/AArch64/BeaconLoop.lean`. Its tests are in
`Kraken/AArch64/BeaconLoopTests.lean`.

## The statement

```lean
theorem loop_rule.{u} [Labels] {code : Code} {Measure : Sort u}
    {lt : Measure → Measure → Prop} (h_wf : WellFounded lt)
    (invariant : Measure → MachineData → Prop)
    (post : MachineState → Prop) (loop_start after_loop : Int64)
    (initial_measure : Measure) (initial : MachineData)
    (h_initial : invariant initial_measure initial)
    (h_loopbody : ∀ measure s, invariant measure s →
      Eventually code.stepWp (fun s' =>
        (s'.pc = loop_start ∧
          ∃ measure', lt measure' measure ∧ invariant measure' s'.data) ∨
        (s'.pc = after_loop ∧ Eventually code.stepWp post s'))
      ⟨s, loop_start⟩) :
    Eventually code.stepWp post ⟨initial, loop_start⟩
```

The user picks an invariant indexed by a termination measure. Starting at
the loop head `loop_start` in a state that satisfies the invariant, one run
of the loop body has two possible outcomes:

- "again": it reaches the head again, in a state that satisfies the
  invariant for a smaller measure;
- "exit": it reaches `after_loop`, from where `post` is eventually
  reached.

Decisions made while writing it in Lean:

- The termination measure is a `WellFounded lt` from Lean's core library,
  for any `Measure : Sort u`. It does not use `WellFoundedRelation`, so
  that a proof can name its relation directly. For a `Nat` measure, `lt`
  is `(· < ·)` and `h_wf` is `Nat.lt_wfRel.wf`. A lexicographic measure
  on `Nat × Nat`, e.g. for nested loops, has `lt` = `Prod.Lex (· < ·)
  (· < ·)` and `h_wf` = `(Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf`
  (checked). No mathlib is needed.
- The invariant is about the `MachineData` only, not about the whole
  `MachineState`: the program counter at the head is always `loop_start`.
- `post` is about the whole `MachineState`, as in the specs of
  `setjmp_spec` and `longjmp_spec`, whose postconditions name the
  program counter after `ret`.

## Finding: the rule holds

`loop_rule` is proven, not `sorry`ed. The proof is a well-founded
induction on the measure, followed by Kraken's `eventually_trans`:

```lean
  suffices h : ∀ measure s, invariant measure s →
      Eventually code.stepWp post ⟨s, loop_start⟩ from
    h initial_measure initial h_initial
  intro measure
  induction measure using h_wf.induction with
  | _ measure ih =>
    intro s hs
    refine eventually_trans _ _ _ _ (h_loopbody measure s hs) ?_
    rintro ⟨d, pc⟩ (⟨rfl, measure', hlt, hinv⟩ | ⟨-, h⟩)
    · exact ih measure' hlt d hinv
    · exact h
```

### The suspected problem: a trivial invariant with zero steps

The suspicion was that the invariant `fun _ _ => True` makes `h_loopbody`
trivially true: take the "again" branch with `Eventually.done`, without
running any instruction, since the state is still at `loop_start`.

That is not possible for every measure. The "again" branch needs a smaller
measure, and a well-founded relation has, in any nonempty set of measures,
a minimal one with nothing below it. For a `Nat` measure with `<`, that is
measure 0, as the first test in `BeaconLoopTests.lean` shows. At a minimal
measure, `h_loopbody` has to take the "exit" branch, so the body has to
actually reach `after_loop` and then `post`.

A zero-step "again" is still allowed for a non-minimal measure. It only
lowers the measure without running the loop, and the well-founded
induction allows only finitely many such steps in a row. So it is
harmless, though useless.

### Termination is in `Eventually` already

Kraken's `Eventually` is an inductive predicate, so every derivation of it
is finite. That is why the rule needs a measure at all: without one,
`h_loopbody` would only give one more iteration, never a finite proof.

The second test in `BeaconLoopTests.lean` checks this directly. It takes a
program that is a single `b 0` (a branch to itself). That program never
gets stuck: every step is a valid `.done`. Yet
`Eventually code.stepWp (fun _ => False)` cannot be derived for it. The
proof is an induction on the `Eventually` derivation: the step case needs
the `Eventually` again at the same state, which is the induction
hypothesis. So a sound loop rule cannot prove anything about code that
does not terminate.

`Eventually` is also total over all executions. It quantifies over every
value of an `undefined` effect (`Effects.All`), and it treats every stuck
step as `False`: an unimplemented instruction, a misaligned `sp`, an access
outside the data memory, or no instruction at the program counter.

## Other problems with the statement

None of these make the rule unsound. They are about how usable it is.

1. `after_loop` does nothing. The proof never uses it (see the `-` in
   `⟨-, h⟩` above), because the "exit" branch already includes
   `Eventually code.stepWp post s'`. The rule would hold just as well with
   the exit branch `Eventually code.stepWp post s'` alone. The address
   only documents which way the loop leaves.
2. Loops with several exits (`return` or `break` inside the body, which is
   common in the C library, e.g. `memchr` returns from inside its loop)
   do not fit one `after_loop`. Dropping `after_loop` (point 1) fixes this
   too.
3. The code after the loop is proven inside `h_loopbody`, under the
   invariant of the last iteration, in a deeply nested goal. A separate
   premise would be clearer:

   ```lean
   (exit : MachineData → Prop)
   (h_exit : ∀ s, exit s → Eventually code.stepWp post ⟨s, after_loop⟩)
   ```

   Here the body's "exit" branch only establishes `exit s'.data`. Choosing
   `exit s := Eventually code.stepWp post ⟨s, after_loop⟩` shows that this
   is as strong as the current statement, so it is only a question of
   structure. With a separate `exit`, `after_loop` does have a purpose
   (point 1).
4. The body can stop at the head too early, e.g. with `Eventually.done`
   before the back edge (the zero-step case above). This is sound, but
   then the proof does not follow the code. When the body's proof steps
   with beacons, it is up to the user to apply `Eventually.done` exactly
   after the branch back to `loop_start`. A loop's beacons are therefore
   not a complete script of the iteration.
5. The rule has no special support for the beacon core:
   - It is a statement about `code.stepWp`, but nothing in it depends on
     AArch64. The same proof works for any `trans` and any `State`, with
     the head given as a predicate instead of a program counter value.
     Kraken's `reg_dec_loop` in `Kraken/OmniSemantics.lean` is such a
     generic rule, for a `Nat` measure that goes down by 1.
   - A generic version in `OmniSemantics.lean`, with `loop_rule` as its
     instance for the beacon core, would avoid duplication if Kraken's
     `Executable`-based proofs need loops too.
6. Inside the body, the conditional branch at the end of each iteration
   (`cbnz`, `b.ne`, ...) gives two goals, one per direction. The `instr`
   tactic does not split goals yet, and objdump's branch-target form needs
   Kraken's parser extension (`aarch64-obj-verification-design.md`,
   section 4.8). These are needed before the rule can be used on
   `strlen`, and are not part of the rule itself.
7. The invariant must carry everything that later iterations and the code
   after the loop need. That includes the frame `R` of the
   separation-logic memory assertion, and the registers that the function
   must preserve. This is the usual cost of invariant-based rules, but it
   makes the invariants of even simple loops long. A rule that frames the
   unchanged parts of the state automatically is left for later.

## Next steps

- Decide between the current statement and the version with
  `exit`/`h_exit` and without a single `after_loop` (points 1 to 3).
- Decide whether a generic rule goes into Kraken's `OmniSemantics.lean`
  (point 5).
- Use the rule on `strlen` once branches work in the beacon tactic
  (point 6).
