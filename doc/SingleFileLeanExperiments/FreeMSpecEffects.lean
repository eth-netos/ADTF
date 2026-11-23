import Lean.Data.Json

open Lean (Json ToJson FromJson toJson fromJson?)

/-! # Sketch: `SpecEffects` as a free monad over its effects

This is `sockeye/lean/Scratch/SpecEffects.lean`, restructured around the
free monad `FreeM` of lean-sail, which xv6iris uses for the Sail model. There,
`SailM` is a `FreeM` over `Except (Sail.Error ue) Outcome`: an event, or a
failure without a continuation. Here, the failures are effects themselves,
`Outcome.failedAssert` and `Outcome.failedAssume`, whose answer type is
`Empty`, so that their continuation can never be called. `SpecEffects S` is
`FreeM (Outcome S)`, and everything else is as in `SpecEffects.lean`:

* `SpecEffects.wp`, which quantifies over the values of `T` itself, so that a
  proof can `intro` the value, and never sees the `Pickable` instance,
* `SpecEffects.eval` with `PickSource.random`, which draws a pseudo-random
  value from a seed through `Pickable.random`,
* `SpecEffects.eval` with `PickSource.ofList`, which takes the values from a
  given list of `Json` values, read back with the `FromJson` that the
  `Pickable` instance of each picked type extends.

`wp_iff_eval` at the end shows that `wp` and `eval` agree.

`SpecEffects` knows nothing about predicates on the picked values. To restrict
a pick, code picks and then assumes, as `natBelow` does: `wp` then gets the
assumption as a hypothesis. To make fuzzing hit the assumption, `natBelow`
passes a `Pickable Nat` that is not an instance, `natBelowPickable`, whose
`random` only gives values that satisfy it. -/

/-! ## The free monad of lean-sail

`Effect`, `FreeM`, `FreeM.bind` and the `Monad` instance are, except for
the doc comments and `A`, `B` for `α`, `β`, copied from
https://github.com/mit-pdos/xv6iris/blob/5cb9df992c45829f6210b3e4176962d7b7a4c408/vendor/lean-sail/Sail/ArchSem.lean#L100-L143
-/

/-- A type of effects, each with the type of the answer that the environment
gives to it. -/
class Effect.{u, v} (Eff : Type v) where
  ret : Eff -> Type u

/-- A computation with answer `A`, as the tree of its effects. A node
`impure call cont` performs `call` and continues with `cont` applied to the
answer. Because the answer type is given by `Effect.ret`, and not by an index
of `Eff`, `FreeM` lives in the same universe as the answer types. -/
inductive FreeM.{u, v, w} (Eff : Type v) [Effect.{u, v} Eff] (A : Type w) :
    Type (max u (max v w)) where
  | pure (a : A) : FreeM Eff A
  | impure (call : Eff) (cont : Effect.ret call -> FreeM Eff A) : FreeM Eff A

def FreeM.bind [Effect Eff] (x : FreeM Eff A) (f : A -> FreeM Eff B) :
    FreeM Eff B :=
  match x with
  | FreeM.pure x => f x
  | FreeM.impure op cont => FreeM.impure op (fun r => FreeM.bind (cont r) f)

instance [Effect Eff] : Monad (FreeM Eff) where
  pure x := FreeM.pure x
  bind := FreeM.bind

/-! ## Types that values can be picked from

`Pickable` is an ordinary type class, so any type can be made pickable by
writing an instance, without changing anything here (see `Color` below). For
values of different types to fit in one list, a list stores them as `Json`,
with the `ToJson` and `FromJson` that their `Pickable` instances extend. -/

/-- A pseudo-random number determined by `seed` and `i`. -/
def mixSeed (seed i : Nat) : Nat :=
  let x := (seed * 6364136223846793005 + i * 1442695040888963407 + 1)
    % 2 ^ 64
  let x := x ^^^ (x >>> 29)
  (x * 0xbf58476d1ce4e5b9 % 2 ^ 64) ^^^ (x >>> 32)

/-- How `SpecEffects.eval` picks values of `T`: `random seed` is a
pseudo-random value, and values are turned into `Json` and back. Reading back
a value from its `Json` gives the value, so that `eval` can be given any value
of `T` as `Json`. An instance can omit the `ToJson` and `FromJson` fields when
`T` has instances of these classes. -/
class Pickable (T : Type) extends ToJson T, FromJson T where
  random : Nat -> T
  fromJson_toJson : forall x : T, fromJson? (toJson x) = .ok x

instance : Pickable Unit where
  random _ := ()
  fromJson_toJson _ := rfl

instance : Pickable Bool where
  random seed := seed % 2 == 0
  fromJson_toJson b := by cases b <;> rfl

/-- Half of the values are below 16, because small numbers are the most
interesting ones. -/
instance : Pickable Nat where
  random seed :=
    if seed % 2 == 0 then seed / 2 % 16 else seed / 2 % 2 ^ 32
  fromJson_toJson _ := rfl

instance : Pickable Int where
  random seed :=
    let magnitude : Int := (Pickable.random (seed / 2) : Nat)
    if seed % 2 == 0 then magnitude else -magnitude
  fromJson_toJson _ := rfl

/-- Lean has no `Json` instances for `BitVec`, so here is one: the number
`toNat`. -/
instance (n : Nat) : ToJson (BitVec n) where
  toJson b := toJson b.toNat

instance (n : Nat) : FromJson (BitVec n) where
  fromJson? j := do
    let m <- (fromJson? j : Except String Nat)
    if h : m < 2 ^ n then return BitVec.ofFin ⟨m, h⟩
    else throw s!"{m} does not fit in {n} bits"

instance (n : Nat) : Pickable (BitVec n) where
  random seed := BitVec.ofNat n seed
  fromJson_toJson b := by
    cases b with
    | ofFin x =>
      show (if h : x.val < 2 ^ n then _ else _) = _
      simp only [x.isLt, dite_true]
      rfl

/-! ## Effects and effect trees -/

/-- The effects of a computation in a system with state `S`. Because `pick`
holds a type, the effects are in `Type 1`. -/
inductive Outcome (S : Type) : Type 1 where
  | getState
  | setState (s : S)
  /-- Picks any value of `T`. Only `eval` uses the instance. -/
  | pick (T : Type) [Pickable T]
  | failedAssert (msg : String)
  /-- An assumption that does not hold, so the computation does not count. -/
  | failedAssume (msg : String)

/-- The answer that the environment gives to an effect. The failures get no
answer, so a computation ends with them. -/
def Outcome.ret {S : Type} : Outcome S -> Type
  | .getState => S
  | .setState _ => Unit
  | @pick _ T _ => T
  | .failedAssert _ => Empty
  | .failedAssume _ => Empty

instance (S : Type) : Effect (Outcome S) where
  ret := Outcome.ret

/-- A computation with state `S`, as the tree of its effects. -/
abbrev SpecEffects (S : Type) : Type -> Type 1 :=
  FreeM (Outcome S)

namespace SpecEffects

variable {S : Type}

def getState : SpecEffects S S :=
  .impure .getState .pure

def setState (s : S) : SpecEffects S Unit :=
  .impure (.setState s) .pure

def pick (T : Type) [Pickable T] : SpecEffects S T :=
  .impure (.pick T) .pure

def failedAssert {A : Type} (msg : String) : SpecEffects S A :=
  .impure (.failedAssert msg) Empty.elim

def failedAssume {A : Type} (msg : String) : SpecEffects S A :=
  .impure (.failedAssume msg) Empty.elim

def assert (cond : Bool) (msg : String) : SpecEffects S Unit :=
  if cond then .pure () else failedAssert msg

def assume (cond : Bool) (msg : String) : SpecEffects S Unit :=
  if cond then .pure () else failedAssume msg

/-! ## Use case 1: weakest preconditions -/

def wp {A : Type} :
    SpecEffects S A -> (A -> S -> Prop) -> S -> Prop
  | .pure a, post, s => post a s
  | .impure .getState k, post, s => wp (k s) post s
  | .impure (.setState s') k, post, _ => wp (k ()) post s'
  | .impure (@Outcome.pick _ T _) k, post, s =>
    forall x : T, wp (k x) post s
  | .impure (.failedAssert _) _, _, _ => False
  | .impure (.failedAssume _) _, _, _ => True

theorem wp_bind {A B : Type} (m : SpecEffects S A)
    (f : A -> SpecEffects S B) (post : B -> S -> Prop) (s : S) :
    wp (m >>= f) post s = wp m (fun a s' => wp (f a) post s') s := by
  show wp (m.bind f) post s = _
  induction m generalizing s with
  | pure => rfl
  | impure call k ih =>
    cases call with
    | getState => exact ih s s
    | setState s' => exact ih () s'
    | pick T => exact forall_congr fun x => ih x s
    | failedAssert => rfl
    | failedAssume => rfl

@[simp] theorem wp_pure {A : Type} (a : A) (post : A -> S -> Prop) (s : S) :
    wp (Pure.pure a : SpecEffects S A) post s = post a s := rfl

@[simp] theorem wp_getState (post : S -> S -> Prop) (s : S) :
    wp (getState : SpecEffects S S) post s = post s s := rfl

@[simp] theorem wp_setState (s' : S) (post : Unit -> S -> Prop) (s : S) :
    wp (setState s') post s = post () s' := rfl

/-- Holds for every `Pickable T`, including ones that are not instances. -/
@[simp] theorem wp_pick {T : Type} [Pickable T]
    (post : T -> S -> Prop) (s : S) :
    wp (pick T) post s = forall x, post x s := rfl

@[simp] theorem wp_assert (cond : Bool) (msg : String)
    (post : Unit -> S -> Prop) (s : S) :
    wp (assert cond msg) post s = (cond = true /\ post () s) := by
  cases cond <;> simp [assert, failedAssert, wp]

@[simp] theorem wp_assume (cond : Bool) (msg : String)
    (post : Unit -> S -> Prop) (s : S) :
    wp (assume cond msg) post s = (cond = true -> post () s) := by
  cases cond <;> simp [assume, failedAssume, wp]

/-! ## Use cases 2 and 3: running -/

/-- How a run of `SpecEffects.eval` ended, with an answer of type `A` if it
succeeded. -/
inductive ExecResult (A : Type) where
  | success (val : A)
  | assertionFailed (msg : String)
  /-- An assumption did not hold, so this run does not count. -/
  | assumptionFailed (msg : String)
  /-- The `PickSource` had no value, for the reason `msg`, so this run does
  not count either. -/
  | noValueToPick (msg : String)
  deriving Repr

/-- Where `SpecEffects.eval` gets the values it picks: given how many values
were picked before, the type `T` to pick and its `Pickable` instance, a
value, or why there is none. -/
def PickSource : Type 1 :=
  (i : Nat) -> (T : Type) -> Pickable T -> Except String T

/-- For the `i`-th pick, `Pickable.random` of a number drawn from `seed`. -/
def PickSource.random (seed : Nat) : PickSource :=
  fun i _ p => .ok (p.random (mixSeed seed i))

/-- The `i`-th value of `values` for the `i`-th pick. A value that the
`FromJson` instance of the type to pick cannot read ends the run with
`noValueToPick`. -/
def PickSource.ofList (values : List Json) : PickSource :=
  fun i T _ =>
    match values[i]? with
    | none => .error s!"the list has no value for pick {i}"
    | some v =>
      match (fromJson? v : Except String T) with
      | .ok x => .ok x
      | .error e => .error s!"pick {i}: {e}"

def eval {A : Type} :
    SpecEffects S A -> PickSource -> Nat -> S -> ExecResult A × S
  | .pure a, _, _, s => (.success a, s)
  | .impure .getState k, source, i, s => eval (k s) source i s
  | .impure (.setState s') k, source, i, _ => eval (k ()) source i s'
  | .impure (@Outcome.pick _ T p) k, source, i, s =>
    match source i T p with
    | .error reason => (.noValueToPick reason, s)
    | .ok x => eval (k x) source (i + 1) s
  | .impure (.failedAssert msg) _, _, _, s => (.assertionFailed msg, s)
  | .impure (.failedAssume msg) _, _, _, s => (.assumptionFailed msg, s)

end SpecEffects

/-! ## Custom generators, as `Pickable`s that are not instances -/

open SpecEffects

/-- Like the `Pickable Nat` instance, but `random` only gives values below
`bound`. -/
@[instance_reducible]
def natBelowPickable (bound : Nat) : Pickable Nat :=
  { (inferInstance : Pickable Nat) with random := fun seed => seed % bound }

/-- Like the `Pickable (BitVec n)` instance, but `random` only gives values in
`lo <= x < hi`. -/
@[instance_reducible]
def bitVecInRangePickable {n : Nat} (lo hi : BitVec n) : Pickable (BitVec n) :=
  { (inferInstance : Pickable (BitVec n)) with
    random := fun seed =>
      BitVec.ofNat n (lo.toNat + seed % (hi.toNat - lo.toNat)) }

/-- A value below `bound`. -/
def natBelow {S : Type} (bound : Nat) : SpecEffects S Nat := do
  let x <- @pick S Nat (natBelowPickable bound)
  assume (decide (x < bound)) s!"x < {bound}"
  return x

/-- A value in `lo <= x < hi`. -/
def bitVecInRange {S : Type} {n : Nat} (lo hi : BitVec n) :
    SpecEffects S (BitVec n) := do
  let x <- @pick S (BitVec n) (bitVecInRangePickable lo hi)
  assume (decide (lo <= x /\ x < hi)) s!"{lo} <= x < {hi}"
  return x

/-! ## Examples -/

/-- Reads a register value from the state, picks an offset below 10, and
stores and returns their sum. -/
def addSmallOffset : SpecEffects Nat Nat := do
  let base <- getState
  let offset <- natBelow 10
  SpecEffects.assert (decide (offset <= 9)) "offset <= 9"
  setState (base + offset)
  return base + offset

/-! ### Use case 1: a proof just introduces the picked value -/

theorem addSmallOffset_wp (base : Nat) :
    addSmallOffset.wp (fun r s => r = s /\ r < base + 10) base := by
  simp only [addSmallOffset, natBelow, wp_bind, wp_getState, wp_pick]
  intro offset
  simp only [wp_assume, wp_pure, wp_assert, wp_setState]
  intro h
  simp only [decide_eq_true_eq] at h
  exact ⟨by simp; omega, by simp; omega⟩

/-! ### Use case 2: pseudo-random values, from a seed -/

/-- info: (SpecEffects.ExecResult.success 109, 109) -/
#guard_msgs in
#eval addSmallOffset.eval (PickSource.random 0) 0 100

/-- The device window `0x80 <= addr < 0x90`, picked with the custom
generator. -/
def pickDeviceAddr : SpecEffects Unit (BitVec 8) :=
  bitVecInRange 0x80#8 0x90#8

/-- The same window, picked with the `Pickable (BitVec 8)` instance. -/
def pickDeviceAddrNaively : SpecEffects Unit (BitVec 8) := do
  let x <- pick (BitVec 8)
  assume (decide (0x80#8 <= x /\ x < 0x90#8)) "0x80 <= x < 0x90"
  return x

/-- How many of the runs with seeds `0` to `199` succeed. -/
def countSuccesses {A : Type} (m : SpecEffects Unit A) : Nat :=
  (List.range 200).countP fun seed =>
    match (m.eval (PickSource.random seed) 0 ()).1 with
    | .success _ => true
    | _ => false

/-- info: (200, 17) -/
#guard_msgs in
#eval (countSuccesses pickDeviceAddr, countSuccesses pickDeviceAddrNaively)

/-! ### Use case 3: values from a heterogeneous list -/

/-- info: (SpecEffects.ExecResult.success 107, 107) -/
#guard_msgs in
#eval addSmallOffset.eval (PickSource.ofList [toJson (7 : Nat)]) 0 100

-- A value that violates the assumption makes the run not count.
/-- info: (SpecEffects.ExecResult.assumptionFailed "x < 10", 100) -/
#guard_msgs in
#eval addSmallOffset.eval (PickSource.ofList [toJson (12 : Nat)]) 0 100

/-- The first pick of `twoPicks` is a `BitVec 8` and the second a `Bool`. -/
def twoPicks : SpecEffects Unit (BitVec 8 × Bool) := do
  let a <- pickDeviceAddr
  let b <- pick Bool
  return (a, b)

/-- info: (SpecEffects.ExecResult.success (0x85#8, true), ()) -/
#guard_msgs in
#eval twoPicks.eval
  (PickSource.ofList [toJson (0x85#8 : BitVec 8), toJson true]) 0 ()

/--
info: SpecEffects.ExecResult.noValueToPick "pick 0: Natural number expected"
-/
#guard_msgs in
#eval (twoPicks.eval (PickSource.ofList [toJson true]) 0 ()).1

-- Without type tags, a `Json` value is read as whatever type is picked:
-- here `133` is read as a `BitVec 8`.
/-- info: (SpecEffects.ExecResult.success (0x85#8, true), ()) -/
#guard_msgs in
#eval twoPicks.eval (PickSource.ofList [toJson (133 : Nat), toJson true]) 0 ()

/-! ### A type that `SpecEffects` does not know about -/

inductive Color where
  | red
  | green
  | blue
  deriving Repr, DecidableEq, ToJson, FromJson

instance : Pickable Color where
  random seed :=
    match seed % 3 with
    | 0 => .red
    | 1 => .green
    | _ => .blue
  fromJson_toJson c := by cases c <;> rfl

def pickTwoColors : SpecEffects Unit (Color × Color) := do
  let a <- pick Color
  let b <- pick Color
  return (a, b)

/-- info: (SpecEffects.ExecResult.success (Color.blue, Color.red), ()) -/
#guard_msgs in
#eval pickTwoColors.eval
  (PickSource.ofList [toJson Color.blue, toJson Color.red]) 0 ()

example : pickTwoColors.wp (fun (a, b) _ => a = b -> b = a) () := by
  simp only [pickTwoColors, wp_bind, wp_pick, wp_pure]
  intro a b h
  exact h.symm

/-! ### Picking a record -/

/-- Two registers, as a record. -/
structure Registers where
  base : Nat
  result : Nat
  deriving Repr, ToJson, FromJson

instance : Pickable Registers where
  random seed :=
    ⟨Pickable.random (mixSeed seed 0), Pickable.random (mixSeed seed 1)⟩
  fromJson_toJson regs := by cases regs; rfl

/-- Like `addSmallOffset`, but on a record of two registers whose initial
values are picked: stores the sum of `base` and an offset below 10 in
`result`, and returns it. -/
def addSmallOffsetToRegs : SpecEffects Registers Nat := do
  let regs <- pick Registers
  setState regs
  let offset <- natBelow 10
  setState { regs with result := regs.base + offset }
  return regs.base + offset

theorem addSmallOffsetToRegs_wp (regs : Registers) :
    addSmallOffsetToRegs.wp
      (fun r s => r = s.result /\ s.base <= r /\ r < s.base + 10) regs := by
  simp only [addSmallOffsetToRegs, natBelow, wp_bind, wp_pick, wp_setState,
    wp_assume, wp_pure, decide_eq_true_eq, true_and]
  intro initial offset h
  exact ⟨by omega, by omega⟩

/-- info: (SpecEffects.ExecResult.success 20, { base := 15, result := 20 }) -/
#guard_msgs in
#eval addSmallOffsetToRegs.eval (PickSource.random 0) 0 ⟨0, 0⟩

/--
info: (SpecEffects.ExecResult.success 107, { base := 100, result := 107 })
-/
#guard_msgs in
#eval addSmallOffsetToRegs.eval
  (PickSource.ofList
    [toJson ({ base := 100, result := 0 } : Registers), toJson (7 : Nat)])
  0 ⟨0, 0⟩

-- The record can also be given as `Json` directly.
/--
info: (SpecEffects.ExecResult.success 107, { base := 100, result := 107 })
-/
#guard_msgs in
#eval addSmallOffsetToRegs.eval
  (PickSource.ofList
    [Json.mkObj [("base", 100), ("result", 0)], (7 : Nat)])
  0 ⟨0, 0⟩

-- A missing field means there is no value for the pick.
/-- info: "pick 0: Registers.result: Natural number expected" -/
#guard_msgs in
#eval
  let values := [Json.mkObj [("base", 100)], (7 : Nat)]
  match (addSmallOffsetToRegs.eval (PickSource.ofList values) 0 ⟨0, 0⟩).1 with
  | .noValueToPick msg => msg
  | _ => "a value for every pick"

/-! ## Consistency of `wp` and `eval`

The weakest precondition of a computation `m` for a postcondition `post`
holds in a state if and only if every run of `eval` from that state satisfies
`post` (see `Satisfies`), whatever `PickSource` gives the picked values.

A run in which the source has no value ends with `noValueToPick`, which
`Satisfies` accepts, like a run in which an assumption fails: the source,
which plays the demon that picks the values, is to blame, not the program.

In the direction from `eval` to `wp`, the proof picks the source: for the
value `x : T` over which `wp` quantifies, it uses a source that reads back
`toJson x`, which is `x` by `Pickable.fromJson_toJson`. -/

namespace SpecEffects

/-- A run of `eval` that ended with `res` and state `s` satisfies `post` the
way `wp` means it: no assertion failed, and if all assumptions held and the
source had all values, the answer and the final state satisfy `post`. -/
def Satisfies {S A : Type} (post : A -> S -> Prop) :
    ExecResult A × S -> Prop
  | (.success a, s) => post a s
  | (.assertionFailed _, _) => False
  | (.assumptionFailed _, _) => True
  | (.noValueToPick _, _) => True

/-- Some source, for runs whose outcome does not depend on it. -/
def PickSource.empty : PickSource := fun _ _ _ => .error "no value"

/-- `source`, except that the `i`-th pick reads back `v`. -/
def PickSource.update (source : PickSource) (i : Nat) (v : Json) :
    PickSource :=
  fun j T p => if j = i then fromJson? v else source j T p

/-- A run that starts after `i` picks only asks the source for the `i`-th and
later values. -/
theorem eval_congr {S A : Type} (m : SpecEffects S A)
    (source source' : PickSource) (i : Nat)
    (h : forall j, i <= j -> source j = source' j) (s : S) :
    eval m source i s = eval m source' i s := by
  induction m generalizing i s with
  | pure a => rfl
  | impure call k ih =>
    cases call with
    | getState => exact ih s i h s
    | setState s' => exact ih () i h s'
    | pick T =>
      simp only [eval]
      rw [h i (Nat.le_refl i)]
      split
      · rfl
      · exact ih _ (i + 1) (fun j hj => h j (by omega)) s
    | failedAssert msg => rfl
    | failedAssume msg => rfl

/-- The weakest precondition of `m` for `post` holds in state `s` if and only
if each run of `m` from `s` after `i` picks, with any source, satisfies
`post`. -/
theorem wp_iff_eval {S A : Type} (m : SpecEffects S A)
    (post : A -> S -> Prop) (s : S) (i : Nat) :
    wp m post s <->
      forall source : PickSource, Satisfies post (eval m source i s) := by
  induction m generalizing s i with
  | pure a =>
    simp only [wp, eval, Satisfies]
    exact ⟨fun h _ => h, fun h => h PickSource.empty⟩
  | impure call k ih =>
    cases call with
    | getState => exact ih s s i
    | setState s' => exact ih () s' i
    | pick T =>
      simp only [wp]
      constructor
      · intro h source
        simp only [eval]
        split
        · trivial
        · exact (ih _ s (i + 1)).mp (h _) source
      · intro h x
        refine (ih x s (i + 1)).mpr (fun source => ?_)
        have := h (source.update i (toJson x))
        simp only [eval, PickSource.update, ↓reduceIte,
          Pickable.fromJson_toJson] at this
        rwa [eval_congr (k x) _ source (i + 1)
          (fun j hj => by
            funext T' p'
            simp only [PickSource.update, show j ≠ i by omega,
              ↓reduceIte])] at this
    | failedAssert msg =>
      simp only [wp, eval, Satisfies]
      exact ⟨False.elim, fun h => h PickSource.empty⟩
    | failedAssume msg =>
      simp only [wp, eval, Satisfies]
      exact ⟨fun _ _ => trivial, fun _ => trivial⟩

end SpecEffects
