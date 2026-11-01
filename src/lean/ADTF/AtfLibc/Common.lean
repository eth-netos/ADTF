module

public import Kraken.AArch64.Beacon
public import Kraken.AArch64.BeaconMem
public import Kraken.AArch64.BeaconLoop

/-!
# Lemmas and tactics shared by the proofs of TF-A's C library functions
-/

@[expose] public section

/-- The condition of `cbz`/`cbnz` on a 32-bit register into which `ldrb`
loaded the byte `b`. -/
theorem ldrb_eq_zero_iff (b : UInt8) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) = 0 ↔ b = 0 := by
  rw [← UInt8.toBitVec_inj]
  generalize b.toBitVec = v
  simp only [UInt8.toBitVec_zero]
  bv_decide

theorem ofInt_toNat64 (x : BitVec 64) :
    BitVec.ofInt 64 (x.toNat : Int) = x := by
  simp

theorem ofNat_zero_or64 (x : BitVec 64) : 0#64 ||| x = x := BitVec.zero_or

/-- Rewrites the byte loads of an instruction's effects with
`MachineData.load_byte_of_sep64 h_mem hw`, for the separation-logic
hypothesis `h_mem` and the length bound `hw` of the bytes. The index has to
be below the length, which the discharger proves with `omega`. -/
macro "load_byte" h_mem:term:max hw:term:max : tactic => `(tactic|
  simp (disch := first | rfl | omega | (simp; omega)) only [UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat', MachineData.load_byte_of_sep64 $h_mem $hw,
    MachineData.load_byte_of_sep64_zero $h_mem $hw, ofInt_toNat64,
    ofNat_zero_or64, Effects.All])

/-- Proves an equality of two `UInt64`s by `bv_decide` on their bit vectors,
with `UInt64.ofNat` of a sum split up. -/
macro "uint64_eq" : tactic => `(tactic| (
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.ofNat_add,
    UInt64.ofNat_toNat, UInt64.toBitVec_ofNat', UInt64.toBitVec_ofNat]
  bv_decide))

/-- Proves `d = { s0 with ... }` for a state `d` that the beacons computed,
field by field. Fields of the right-hand side that are metavariables, e.g.
from an existential, are assigned by unification. -/
macro "state_eq" : tactic => `(tactic| (
  first
  | rfl
  | (dsimp only
     congr 2 <;> first | rfl | uint64_eq)))

/-- A search through `bs` for `b` that has not found it in the first `n`
bytes may read the byte at `n`, if `b` is in `bs`. -/
theorem lt_length_of_forall_ne {bs : List UInt8} {n : Nat} {b : UInt8}
    (hz : ∀ i < n, bs[i]? ≠ some b) (h : b ∈ bs) : n < bs.length := by
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem h
  refine Nat.lt_of_not_le fun hle => hz j (by omega) ?_
  simp [hj, hjb]

/-- A search through `bs` that has found no 0 in the first `n` bytes and
stops at the latest after `m` bytes, where `bs` is at least `m` bytes long or
contains a 0, may read the byte at `n`. -/
theorem lt_length_of_no_zero {bs : List UInt8} {n m : Nat}
    (hz : ∀ i < n, bs[i]? ≠ some 0) (hn : n < m)
    (h_bs : m ≤ bs.length ∨ 0 ∈ bs) : n < bs.length := by
  rcases h_bs with h_bs | h_bs
  · omega
  · exact lt_length_of_forall_ne hz h_bs

theorem UInt64.ofNat_eq_iff {n : Nat} {x : UInt64} (hn : n < 2 ^ 64) :
    UInt64.ofNat n = x ↔ n = x.toNat := by
  constructor
  · rintro rfl
    simp only [UInt64.toNat_ofNat']; omega
  · rintro rfl
    exact UInt64.ofNat_toNat

/-- The condition of `b.eq` after `cmp w3, w1`, where `ldrb` loaded the byte
`b` into `w3` and `and w1, w1, #0xff` truncated `x` to its low byte. -/
theorem ldrb_cmp_and_eq_iff (b : UInt8) (x : UInt64) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) -
      BitVec.extractLsb' 0 32 (x &&& 255).toBitVec = BitVec.zero 32 ↔
    b = x.toUInt8 := by
  rw [← UInt8.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_toUInt8]
  generalize b.toBitVec = v
  generalize x.toBitVec = w
  simp only [BitVec.zero_eq, UInt64.toBitVec_ofNat]
  bv_decide

/-- The value of `csel x0, y, z, ne` after `cmp w3, w1`, where `ldrb` loaded
the byte `b` into `w3` and `and w1, w1, #0xff` truncated `x` to its low
byte. -/
theorem csel_ne_ldrb_cmp_and (b : UInt8) (x y z : UInt64) :
    (if (!BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.zeroExtend 32 b.toBitVec)) -
          BitVec.extractLsb' 0 32 (x &&& 255).toBitVec ==
        BitVec.zero 32) = true then y.toBitVec else z.toBitVec) =
      (if b = x.toUInt8 then z else y).toBitVec := by
  by_cases hb : b = x.toUInt8
  · have := (ldrb_cmp_and_eq_iff b x).mpr hb
    rw [ite_eq_right (by simp only [this, beq_self_eq_true]; decide),
      ite_eq_left hb]
  · have := mt (ldrb_cmp_and_eq_iff b x).mp hb
    rw [ite_eq_left (by simpa only [Bool.not_eq_true', beq_eq_false_iff_ne]),
      ite_eq_right hb]

/-- `x0` points to the last occurrence of `c` among the first `n` bytes at
`base`, or is the null pointer if there is none. -/
def IsLastMatch (bs : List UInt8) (c : UInt8) (base : UInt64) (n : Nat)
    (x0 : UInt64) : Prop :=
  (x0 = 0 ∧ ∀ i < n, bs[i]? ≠ some c) ∨
  ∃ j < n, bs[j]? = some c ∧ x0 = base + .ofNat j ∧
    ∀ i < n, j < i → bs[i]? ≠ some c

theorem IsLastMatch.zero (bs : List UInt8) (c : UInt8) (base : UInt64) :
    IsLastMatch bs c base 0 0 :=
  .inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem IsLastMatch.succ_eq {bs : List UInt8} {c : UInt8} {base : UInt64}
    {n : Nat} (hn : n < bs.length) (hc : bs[n] = c) :
    IsLastMatch bs c base (n + 1) (base + .ofNat n) :=
  .inr ⟨n, by omega, by simp [hn, hc], rfl, fun i hi hni => by omega⟩

theorem IsLastMatch.succ_ne {bs : List UInt8} {c : UInt8} {base : UInt64}
    {n : Nat} {x0 : UInt64} (h : IsLastMatch bs c base n x0)
    (hn : n < bs.length) (hc : bs[n] ≠ c) :
    IsLastMatch bs c base (n + 1) x0 := by
  rcases h with ⟨h0, hz⟩ | ⟨j, hj, hjc, hx, hz⟩
  · refine .inl ⟨h0, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hz i hi
    · simp [hn, hc]
  · refine .inr ⟨j, by omega, hjc, hx, fun i hi hji => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hz i hi hji
    · simp [hn, hc]
