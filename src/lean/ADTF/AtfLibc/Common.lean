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
  all_goals bv_decide))

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

/-- The value of `sub w0, w3, w5` after `ldrb` loaded the bytes `a` into `w3`
and `b` into `w5`: the difference of the bytes as a 32-bit integer (see
`byteDiff_toInt`), zero-extended to 64 bits. -/
def byteDiff (a b : UInt8) : UInt64 :=
  ⟨(a.toBitVec.zeroExtend 32 - b.toBitVec.zeroExtend 32).zeroExtend 64⟩

theorem byteDiff_toInt (a b : UInt8) :
    ((byteDiff a b).toBitVec.extractLsb' 0 32).toInt =
      (a.toNat : Int) - b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [byteDiff, BitVec.toInt_eq_toNat_bmod, BitVec.extractLsb'_toNat,
    BitVec.toNat_setWidth, BitVec.toNat_sub, UInt8.toNat_toBitVec]
  rw [Int.bmod_def]
  split <;> omega

/-- The condition of `b.eq` after `cmp` of two registers into which `ldrb`
loaded the bytes `a` and `b`. -/
theorem ldrb_cmp_ldrb_eq_iff (a b : UInt8) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 a.toBitVec)) -
      BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 b.toBitVec)) = BitVec.zero 32 ↔ a = b := by
  rw [← UInt8.toBitVec_inj]
  generalize a.toBitVec = v
  generalize b.toBitVec = w
  simp only [BitVec.zero_eq]
  bv_decide

/-- The address of a load from `x - 1 + (y + 1)`. -/
theorem sub_one_add_add_one (x : UInt64) (y : BitVec 64) :
    (x - 1).toBitVec + (y + 1) = x.toBitVec + y := by
  rw [UInt64.toBitVec_sub]
  generalize x.toBitVec = v
  simp only [UInt64.toBitVec_one]
  bv_decide

/-- After copying the first `n` bytes of `a` over `b`, copying byte `n`
too. -/
theorem List.getElem_take_append_drop {x y : List UInt8} {n : Nat}
    (hx : n ≤ x.length) (h : n < (x.take n ++ y.drop n).length) :
    (x.take n ++ y.drop n)[n] = y[n]'(by simp at h; omega) := by
  rw [List.getElem_append_right (by simp; omega)]
  simp [Nat.min_eq_left hx]

theorem List.set_take_append_drop {a b : List UInt8} {n : Nat}
    (ha : n < a.length) (hb : n < b.length) :
    (a.take n ++ b.drop n).set n a[n] = a.take (n + 1) ++ b.drop (n + 1) := by
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt ha), Nat.sub_self,
    List.drop_eq_getElem_cons hb, List.set_cons_zero, List.take_add_one,
    List.getElem?_eq_getElem ha, Option.toList_some, List.append_assoc,
    List.singleton_append]

theorem List.set_take_append_drop' {a b : List UInt8} {n : Nat} (x : UInt8)
    (ha : n ≤ a.length) (hb : n < b.length) :
    (a.take n ++ b.drop n).set n x = a.take n ++ x :: b.drop (n + 1) := by
  rw [List.set_append_right _ _ (by simp; omega), List.length_take,
    Nat.min_eq_left ha, Nat.sub_self, List.drop_eq_getElem_cons hb,
    List.set_cons_zero]

/-- After `subs x2, x2, #1` on `x2 = x - n`, a taken `b.ne` means that
`n + 1` is still below `x`. -/
theorem subs_count_ne {x : UInt64} {n : Nat} (hn : n < x.toNat)
    (hne : (!(x - UInt64.ofNat n).toBitVec - 1 == BitVec.zero 64) = true) :
    n + 1 < x.toNat := by
  have h1 : (x - UInt64.ofNat n).toBitVec - 1 ≠ 0 := by simpa using hne
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat'] at h1
  rw [← UInt64.toNat_toBitVec] at *
  bv_omega

/-- After `subs x2, x2, #1` on `x2 = x - n`, a `b.ne` that is not taken
means that `n + 1` is `x`. -/
theorem subs_count_eq {x : UInt64} {n : Nat} (hn : n < x.toNat)
    (heq : ¬(!(x - UInt64.ofNat n).toBitVec - 1 == BitVec.zero 64) = true) :
    n + 1 = x.toNat := by
  have h1 : (x - UInt64.ofNat n).toBitVec - 1 = 0 := by simpa using heq
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat'] at h1
  rw [← UInt64.toNat_toBitVec] at *
  bv_omega

/-- The byte that `strb` stores from a register into which `ldrb` loaded
`v`. -/
theorem ldrb_strb_byte (v : BitVec 8) :
    BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32
      (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 v))) = v := by
  bv_decide

/-- Rewrites the byte stores of an instruction's effects with
`MachineData.store_byte_of_sep64 h_mem`, for the separation-logic hypothesis
`h_mem` about the data memory. The index has to be below the length, which
the discharger proves with `omega`. -/
macro "store_byte" h_mem:term:max : tactic => `(tactic|
  simp (disch := first | rfl | omega | (simp; omega)) only
    [UInt64.toBitVec_add, UInt64.toBitVec_ofNat', ofInt_toNat64,
      ldrb_strb_byte, MachineData.store_byte_of_sep64 $h_mem, Effects.All])

/-- Setting byte `n` of a buffer whose first `n` bytes are `c` to `c`. -/
theorem List.set_replicate_append_drop {b : List UInt8} {n : Nat}
    (c : UInt8) (hb : n < b.length) :
    (List.replicate n c ++ b.drop n).set n c =
      List.replicate (n + 1) c ++ b.drop (n + 1) := by
  rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
    List.drop_eq_getElem_cons hb, List.set_cons_zero, List.replicate_succ',
    List.append_assoc]
  rfl

/-- The value of 8 bytes `c`. -/
theorem Int.ofBytes_replicate_eight (c : UInt8) :
    Int.ofBytes (List.replicate 8 c) =
      ((c.toNat * 0x101010101010101 : Nat) : Int) := by
  simp only [Int.ofBytes, List.replicate, List.foldr]
  omega

/-- The doubleword whose 8 bytes are `c`, as `memset` computes it with
`mul`. -/
theorem fill_toNat (c : UInt8) :
    (c.toBitVec.zeroExtend 64 * 0x101010101010101#64).toNat =
      c.toNat * 0x101010101010101 := by
  have hc := c.toBitVec.isLt
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := c.toBitVec.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

theorem BitVec.toInt_take_eq_toNat (x : BitVec 64) :
    x.toInt.take (8 * 8) = x.toNat := by
  have := x.isLt
  rw [Int.take, BitVec.toInt_eq_toNat_cond]
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · simp only [Nat.reduceMul, Int.reducePow, Nat.reducePow]
    omega

/-- The bytes of the doubleword of `fill_toNat` are 8 bytes `c`. -/
theorem Int.toBytes_fill (c : UInt8) :
    Int.toBytes 8 (c.toBitVec.zeroExtend 64 * 0x101010101010101#64).toInt =
      List.replicate 8 c := by
  rw [← Int.toBytes_emod, BitVec.toInt_take_eq_toNat, fill_toNat,
    ← Int.ofBytes_replicate_eight]
  have := Int.toBytes_ofBytes_all (List.replicate 8 c)
  rw [List.length_replicate] at this
  exact this

/-- Storing 8 bytes `c` at offset `k` of a buffer whose first `k` bytes are
`c`. -/
theorem List.replicate_append_drop_store {b : List UInt8} {k : Nat}
    (c : UInt8) :
    (List.replicate k c ++ b.drop k).take k ++ List.replicate 8 c ++
      (List.replicate k c ++ b.drop k).drop (k + 8) =
      List.replicate (k + 8) c ++ b.drop (k + 8) := by
  rw [← List.replicate_append_replicate]
  simp [List.drop_append, List.drop_drop]

/-- Rounding `r` down to a multiple of 8 gives `q`, if `q` is that multiple.
-/
theorem and_neg8_eq {r : BitVec 64} {q : Nat} (hq8 : q % 8 = 0)
    (h1 : q ≤ r.toNat) (h2 : r.toNat - q ≤ 7) :
    r &&& (-8 : Int64).toBitVec = BitVec.ofNat 64 q := by
  have e : (-8 : Int64).toBitVec = 0xfffffffffffffff8#64 := by decide
  have hs : r &&& 0xfffffffffffffff8#64 = r - (r &&& 7#64) := by bv_decide
  have hl : r &&& 7#64 ≤ r := by bv_decide
  have h7 : (r &&& 7#64).toNat = r.toNat % 8 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 3
  have := r.isLt
  apply BitVec.eq_of_toNat_eq
  rw [e, hs, BitVec.toNat_sub_of_le hl, h7, BitVec.toNat_ofNat]
  omega

/-- The condition `hi` after `cmp r, k`: `r` is above `k`, unsigned. -/
theorem cmp_hi_iff (r : BitVec 64) (k : BitVec 64) :
    ((↑(r - k).toNat : Int) == ↑r.toNat - ↑k.toNat &&
      !(r - k == BitVec.zero 64)) = true ↔ k.toNat < r.toNat := by
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, BitVec.zero_eq]
  constructor
  · rintro ⟨h1, h2⟩
    bv_omega
  · intro h
    constructor <;> bv_omega

/-- The length of `l.takeWhile p` is the index `i` of the first element for
which `p` is false, or `l.length` if there is none. -/
theorem List.length_takeWhile_eq {α : Type} {l : List α} {p : α → Bool}
    {i : Nat} (hi : i ≤ l.length) (h : ∀ j (hj : j < i), p (l[j]'(by omega)))
    (h2 : ∀ hi' : i < l.length, p l[i] = false) :
    (l.takeWhile p).length = i := by
  induction l generalizing i with
  | nil => simp at hi; simp [hi]
  | cons x xs ih =>
    cases i with
    | zero =>
      have : p x = false := h2 (by simp)
      simp [this]
    | succ i =>
      have hx := h 0 (by omega)
      simp only [List.getElem_cons_zero] at hx
      simp only [List.takeWhile_cons, hx, ite_true, List.length_cons]
      rw [ih (by simp at hi; omega)
        (fun j hj => by simpa using h (j + 1) (by omega))
        (fun hi' => h2 (by simp; omega))]

/-- `MachineData.store_of_sep64` at offset 0. -/
theorem MachineData.store_of_sep64_zero {d : DataMem} {bs : List UInt8}
    {a : BitVec 64} {R : DataMem → Prop} (h : d =⋆ Eq (bs.At a) ⋆ R)
    (s : MachineData) {w : MemWidth} (v : w.type)
    (ret : MachineData → Effects) (hd : s.dmem = d)
    (hi : w.bytes ≤ bs.length) :
    s.store a v ret =
      require_write_access a w (fun _ =>
        ret { s with dmem := Mem.storeInt d a w.bytes v.toInt }) := by
  simpa using MachineData.store_of_sep64 h s 0 v ret hd (by omega)

theorem ofNat_toBitVec_eq_zero {k : Nat} (hk : k < 2 ^ 64)
    (h : (UInt64.ofNat k).toBitVec = 0) : k = 0 := by
  have := congrArg BitVec.toNat h
  rwa [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    at this

/-- A register after `sub x, x, #0x1`, e.g. a count down. -/
theorem ofNat_succ_sub_one (j : Nat) :
    UInt64.ofBitVec ((UInt64.ofNat (j + 1)).toBitVec - 1) = UInt64.ofNat j := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_ofNat', UInt64.toBitVec_ofNat', BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _
