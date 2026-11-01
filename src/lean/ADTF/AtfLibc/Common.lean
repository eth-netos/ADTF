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

/-- Rewrites the byte loads of an instruction's effects with
`MachineData.load_byte_of_sep64 h_mem hw`, for the separation-logic
hypothesis `h_mem` and the length bound `hw` of the bytes. The index has to
be below the length, which the discharger proves with `omega`. -/
macro "load_byte" h_mem:term:max hw:term:max : tactic => `(tactic|
  simp (disch := first | rfl | omega | (simp; omega)) only [UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat', MachineData.load_byte_of_sep64 $h_mem $hw,
    MachineData.load_byte_of_sep64_zero $h_mem $hw, ofInt_toNat64,
    Effects.All])

/-- Proves an equality of two `UInt64`s by `bv_decide` on their bit vectors,
with `UInt64.ofNat` of a sum split up. -/
macro "uint64_eq" : tactic => `(tactic| (
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_add, UInt64.ofNat_add, UInt64.toBitVec_ofNat',
    UInt64.toBitVec_ofNat]
  bv_decide))

/-- Proves `d = { s0 with ... }` for a state `d` that the beacons computed,
field by field. Fields of the right-hand side that are metavariables, e.g.
from an existential, are assigned by unification. -/
macro "state_eq" : tactic => `(tactic| (
  first
  | rfl
  | (dsimp only
     congr 2 <;> first | rfl | uint64_eq)))

/-- A search through `bs` that has found no 0 in the first `n` bytes and
stops at the latest after `m` bytes, where `bs` is at least `m` bytes long or
contains a 0, may read the byte at `n`. -/
theorem lt_length_of_no_zero {bs : List UInt8} {n m : Nat}
    (hz : ∀ i < n, bs[i]? ≠ some 0) (hn : n < m)
    (h_bs : m ≤ bs.length ∨ 0 ∈ bs) : n < bs.length := by
  rcases h_bs with h_bs | h_bs
  · omega
  · obtain ⟨j, hj, hj0⟩ := List.getElem_of_mem h_bs
    refine Nat.lt_of_not_le fun hle => hz j (by omega) ?_
    simp [hj, hj0]

theorem UInt64.ofNat_eq_iff {n : Nat} {x : UInt64} (hn : n < 2 ^ 64) :
    UInt64.ofNat n = x ↔ n = x.toNat := by
  constructor
  · rintro rfl
    simp only [UInt64.toNat_ofNat']; omega
  · rintro rfl
    exact UInt64.ofNat_toNat
