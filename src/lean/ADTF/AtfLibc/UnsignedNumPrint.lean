module

public import ADTF.AtfLibc.Listing.unsigned_num_print_o
public import ADTF.AtfLibc.Common
public import ADTF.AtfLibc.Strtoul
public import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `unsigned_num_print` from TF-A's `libc/snprintf.o`

The static function `unsigned_num_print` of `snprintf.c` prints an unsigned
number with `CHECK_AND_PUT_CHAR`, in four loops, each proven with
`loop_rule`: the digit loop (`unum_digits`), the left padding loop
(`unum_pad`), the output loop (`unum_out`) and the right padding loop
(`unum_neg`). `unum_spec` composes them.

The C code returns early if `radix < 10`, but the object code has no such
check: every call in `snprintf.c` passes 10 or 16, and the compiler dropped
it. So `unum_spec` assumes `10 ≤ radix`, which also makes the 20 bytes of
`num_buf` enough.

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

@[expose] public section

/-- The instructions of `unsigned_num_print` in ATF's `snprintf.o`. -/
def unsigned_num_print_o : List Instr :=
  objdumpAArch64(unsigned_num_print_o_dump)

/-- The character for the digit 10 of `unsigned_num_print` (unsigned number
print, `unum`), `A` (ASCII, `ascii_a`) if `cap` (`capitalise`). -/
def unumA (cap : Bool) : Nat := if cap then 0x41 else 0x61

/-- The character that `unsigned_num_print` (unsigned number print) uses for
the digit `r`. -/
def unumChar (cap : Bool) (r : Nat) : UInt8 :=
  if r ≤ 9 then .ofNat (r + 0x30) else .ofNat (r + unumA cap - 10)

/-- The digits of a number (the second `Nat`) in base `b`, most significant
first, at most as many as the first `Nat` says, as `unsigned_num_print`
(unsigned number print) prints them. -/
def unumStr (cap : Bool) (b : Nat) : Nat → Nat → List UInt8
  | 0, _ => []
  | f + 1, v =>
    (if v < b then [] else unumStr cap b f (v / b)) ++ [unumChar cap (v % b)]

/-- The digits of `v` in base `b` that `unsigned_num_print` (unsigned number
print) prints; `64` digits are enough for `v < 2 ^ 64` and `2 ≤ b`. -/
def unumDigits (cap : Bool) (b v : Nat) : List UInt8 := unumStr cap b 64 v

/-- A power of `b ≥ 10` (`pow`) that is at most (`le`) some `v < 2 ^ 64`
(`lt64`) has an exponent of at most 19. -/
theorem pow_le_lt64 {b v k : Nat} (hb : 10 ≤ b) (hv : v < 2 ^ 64)
    (h : b ^ k ≤ v) : k ≤ 19 := by
  refine Nat.le_of_not_lt fun hk => ?_
  have h1 : 10 ^ 20 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h2 : 10 ^ k ≤ b ^ k := Nat.pow_le_pow_left hb k
  have : (2 : Nat) ^ 64 < 10 ^ 20 := by decide
  omega

/-- The result of `udiv` (unsigned divide) on `UInt64.ofNat`s. -/
theorem udiv_ofNat (u b : Nat) (hu : u < 2 ^ 64) (hb0 : 0 < b)
    (hb : b < 2 ^ 64) :
    (if ((UInt64.ofNat b).toBitVec == 0) = true then (0 : BitVec 64)
      else (UInt64.ofNat u).toBitVec / (UInt64.ofNat b).toBitVec) =
      BitVec.ofNat 64 (u / b) := by
  have h0 : ((UInt64.ofNat b).toBitVec == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  rw [h0]
  simp only [Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  simp [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self u b) hu)]

/-- The result of `msub` (multiply-subtract) that computes the remainder
of a `udiv` (unsigned divide), on `UInt64.ofNat`s. -/
theorem msub_ofNat (u b : Nat) (hu : u < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat u).toBitVec - BitVec.ofNat 64 (u / b) *
      (UInt64.ofNat b).toBitVec = BitVec.ofNat 64 (u % b) := by
  have e : u = u / b * b + u % b := (Nat.div_add_mod' u b).symm
  have h1 : u / b * b ≤ u := Nat.div_mul_le_self u b
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toBitVec_ofNat', BitVec.toNat_sub, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self u b) hu),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h1 hu)]
  have h2 : u % b < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le u b) hu
  rw [Nat.mod_eq_of_lt h2]
  omega

/-- `BitVec.ofNat 8` is the truncation (`setWidth`) of `BitVec.ofNat 64`. -/
theorem ofNat8_eq_setWidth (r : Nat) :
    BitVec.ofNat 8 r = (BitVec.ofNat 64 r).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- The byte that the digit loop of `unsigned_num_print` (unsigned number,
`unum`) stores for the remainder `r`, computed with `add`, `and` and `csel`,
is `unumChar cap r`. -/
theorem unum_char_byte (cap : Bool) (r : Nat) (hr : r < 2 ^ 64) :
    BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (if ((↑(BitVec.ofNat 64 r - 9).toNat : Int) ==
            ↑(BitVec.ofNat 64 r).toNat - ↑(BitVec.toNat (9 : BitVec 64)) &&
          !(BitVec.ofNat 64 r - 9 == BitVec.zero 64)) = true then
        BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
            (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
              (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 r) &&&
                BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64)))) +
            BitVec.extractLsb' 0 32
              (UInt64.ofNat (unumA cap - 10)).toBitVec)) &&&
          BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64))))
      else
        BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
            (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
              (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 r) &&&
                BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64)))) +
            BitVec.ofInt 32 (BitVec.toInt (48 : BitVec 64)))) &&&
          BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64))))))) =
      (unumChar cap r).toBitVec := by
  have e9 : (9 : BitVec 64).toNat = 9 := rfl
  have hr' : (BitVec.ofNat 64 r).toNat = r := by
    simp only [BitVec.toNat_ofNat]; omega
  simp only [cmp_hi_iff]
  simp only [e9, hr']
  unfold unumChar
  by_cases h9 : r ≤ 9
  · simp only [show ¬ 9 < r by omega, h9, ↓reduceIte, UInt8.toBitVec_ofNat',
      BitVec.ofNat_add, ofNat8_eq_setWidth]
    generalize BitVec.ofNat 64 r = R
    bv_decide
  · have ha : 10 ≤ unumA cap := by cases cap <;> decide
    simp only [show 9 < r by omega, h9, ↓reduceIte, UInt8.toBitVec_ofNat',
      show r + unumA cap - 10 = r + (unumA cap - 10) by omega,
      BitVec.ofNat_add, ofNat8_eq_setWidth]
    generalize BitVec.ofNat 64 r = R
    cases cap <;> simp only [unumA, UInt64.toBitVec_ofNat'] <;> bv_decide

/-- Setting the element of `B ++ b.drop k` (`drop`) right after `B`, whose
length (`len`) is `k`, appends it to `B`. -/
theorem List.set_append_drop_len {B b : List UInt8} {k : Nat}
    (hB : B.length = k) (hk : k < b.length) (x : UInt8) :
    (B ++ b.drop k).set k x = (B ++ [x]) ++ b.drop (k + 1) := by
  rw [List.set_append_right _ _ (by omega), hB, Nat.sub_self,
    List.drop_eq_getElem_cons hk, List.set_cons_zero, List.append_assoc]
  rfl

/-- The address `p + k` as `strb` with a register offset computes it, with
`k` an `ofNat`. -/
theorem addr_ofNat_add (k : Nat) (p : UInt64) :
    (UInt64.ofNat k).toBitVec + BitVec.ofInt 64 (p.toBitVec.toNat : Int) =
      p.toBitVec + BitVec.ofNat 64 k := by
  rw [ofInt_toNat64, UInt64.toBitVec_ofNat', BitVec.add_comm]

/-- The digit loop of `unsigned_num_print` (unsigned number print), from
`unsigned_num_print + 0x28` to `unsigned_num_print + 0x5c`: it stores the
digits of `v` in base `b`, least significant first (`B`), in the buffer
`num_buf` at `bufp`. -/
theorem unum_digits [Labels] (code : Code) (f : Int64)
    (h : Loaded code f unsigned_num_print_o)
    (h_sym : label "unsigned_num_print" = f)
    (d : MachineData) (cap : Bool) (b v : Nat) (stk : List UInt8)
    (R : DataMem → Prop) (bufp : UInt64) (hv : v < 2 ^ 64) (hb : 10 ≤ b)
    (hb' : b < 2 ^ 32) (hstk : stk.length = 20)
    (h_x3 : d.regs.X3 = .ofNat v) (h_x4 : d.regs.X4 = .ofNat b)
    (h_x7 : d.regs.X7 = 0) (h_x9 : d.regs.X9 = .ofNat (unumA cap - 10))
    (h_x11 : d.regs.X11 = bufp)
    (h_mem : d.dmem =⋆ Eq (stk.At bufp.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s => s.pc = f + 0x5c ∧
      ∃ B : List UInt8, 0 < B.length ∧ B.length ≤ 20 ∧
      unumDigits cap b v = B.reverse ∧
      ∃ x3 x8 x10 x12 x13 st m,
      (m =⋆ Eq ((B ++ stk.drop B.length).At bufp.toBitVec) ⋆ R) ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X7 := .ofNat (B.length - 1)
          X8 := x8
          X10 := x10
          X12 := x12
          X13 := x13 }
        status := st
        dmem := m })
    ⟨d, f + 0x28⟩ := by
  refine loop_rule (measure fun k => 20 - k).wf
    (fun k s => s.pc = f + 0x28 ∧ ∃ B : List UInt8, B.length = k ∧
      (b ^ k ≤ v ∨ k = 0) ∧
      unumDigits cap b v = unumStr cap b (64 - k) (v / b ^ k) ++ B.reverse ∧
      ∃ x8 x10 x12 x13 st m,
      (m =⋆ Eq ((B ++ stk.drop k).At bufp.toBitVec) ⋆ R) ∧
      s.data = { d with
        regs := { d.regs with
          X3 := .ofNat (v / b ^ k)
          X7 := .ofNat k
          X8 := x8
          X10 := x10
          X12 := x12
          X13 := x13 }
        status := st
        dmem := m })
    _ 0 _ ⟨rfl, [], rfl, .inr rfl, by simp [unumDigits], d.regs.X8,
      d.regs.X10, d.regs.X12, d.regs.X13, d.status, d.dmem,
      by simpa using h_mem, ?init⟩ ?_
  case init =>
    simp only [Nat.pow_zero, Nat.div_one, ← h_x3,
      show (UInt64.ofNat 0) = d.regs.X7 by rw [h_x7]; rfl]
  rintro k ⟨d', pc⟩ ⟨rfl, B, hB, hpow, hdig, x8, x10, x12, x13, st, m, hm,
    rfl⟩
  have hk : k ≤ 19 := by
    rcases hpow with hpow | rfl
    · exact pow_le_lt64 hb hv hpow
    · omega
  have hu : v / b ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  generalize hU : v / b ^ k = u at hu hdig
  have hu' : u < 2 ^ 64 := hu
  have hl : (B ++ stk.drop k).length = 20 := by simp [hB, hstk]; omega
  instr "udiv x13, x3, x4" at f + 0x28
  instr "msub x12, x13, x4, x3" at f + 0x2c
  instr "and w8, w12, #0xff" at f + 0x30
  instr "cmp x12, #0x9" at f + 0x34
  instr "add w10, w8, #0x30" at f + 0x38
  instr "add w8, w8, w9" at f + 0x3c
  instr "and w10, w10, #0xff" at f + 0x40
  instr "and w8, w8, #0xff" at f + 0x44
  instr "csel w8, w8, w10, hi" at f + 0x48
  simp only [h_x4, h_x9, h_x11, udiv_ofNat u b hu' (by omega) (by omega),
    msub_ofNat u b hu' (by omega)]
  instr "strb w8, [x7, x11]" at f + 0x4c

  simp only [unum_char_byte cap (u % b)
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hu'), addr_ofNat_add]
  store_byte hm
  have hm' := Mem.storeInt_byte_sep _ _ k _ _ hm (by omega) (by omega)
    (unumChar cap (u % b))
  rw [List.set_append_drop_len hB (by omega)] at hm'
  instr "add x8, x7, #0x1" at f + 0x50
  instr "cmp x4, x3" at f + 0x54
  instr "b.ls c0 <unsigned_num_print+0xc0>" at f + 0x58
  · intro hls
    simp only [cmp_ls_eq] at hls
    simp only [decide_eq_true_eq, UInt64.toBitVec_ofNat',
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu',
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)] at hls
    instr "mov x7, x8" at f + 0xc0
    instr "mov x3, x13" at f + 0xc4
    instr "b 28 <unsigned_num_print+0x28>" at f + 0xc8
    rw [h_sym]
    have hpow' : b ^ (k + 1) ≤ v := by
      rw [← hU, Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))] at hls
      rw [Nat.pow_succ, Nat.mul_comm]; exact hls
    have hdiv : v / b ^ (k + 1) = u / b := by
      rw [← hU, Nat.div_div_eq_div_mul, Nat.pow_succ]
    refine .done _ (.inl ⟨k + 1, ?rel, rfl, B ++ [unumChar cap (u % b)],
      by simp [hB], .inl hpow', ?dig, ?y8, ?y10, ?y12, ?y13, ?yst, _, hm',
      ?heq⟩)
    case heq =>
      rw [hdiv]
      state_eq
    case rel => simp only [InvImage, WellFoundedRelation.rel]; omega
    case dig =>
      rw [hdig, show 64 - k = (64 - (k + 1)) + 1 by omega, unumStr]
      simp [show ¬u < b by omega, hdiv]
  · intro hls
    simp only [cmp_ls_eq] at hls
    simp only [decide_eq_true_eq, UInt64.toBitVec_ofNat',
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu',
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.not_le] at hls
    refine .done _ (.inr ⟨by dsimp only; bv_decide,
      B ++ [unumChar cap (u % b)], by simp, by simp; omega, ?dig, ?y3, ?y8,
      ?y10, ?y12, ?y13, ?yst, _, by simpa [hB] using hm', ?heq⟩)
    case heq =>
      simp only [List.length_append, List.length_singleton, hB,
        Nat.add_sub_cancel]
      state_eq
    case dig =>
      rw [hdig, show 64 - k = (63 - k) + 1 by omega, unumStr]
      simp [hls]

/-- The characters that `unsigned_num_print` (unsigned number print) prints:
the digits of `v` in base `b`, right-aligned to `padn` characters with
`padc` if `padn` is positive, left-aligned to `-padn` characters with `padc`
if `padn` is negative. -/
def unumText (cap : Bool) (b v : Nat) (padn : Int) (padc : UInt8) :
    List UInt8 :=
  List.replicate (padn - (unumDigits cap b v).length).toNat padc ++
    unumDigits cap b v ++
    List.replicate (-(padn + (unumDigits cap b v).length)).toNat padc

/-- The number of characters that `unsigned_num_print` (unsigned number print)
has written (`Wr`) to the output after `j` calls of `CHECK_AND_PUT_CHAR`,
which writes only while the count `c + j` is below the size `n`. -/
def unumWr (c n : UInt64) (j : Nat) : Nat := min j (n.toNat - c.toNat)

/-- The memory (`Mem`) of `unsigned_num_print` (unsigned number print) after
`j` characters of `text`: the output pointer (`*s`) at `ps` points `unumWr`
bytes after the start `p`, the count (`*chars_printed`) at `pc` is `c + j`,
the output buffer at `p` (initially `out`) starts with the written part of
`text`, and `K` holds for the rest. -/
def UnumMem (ps pc p c n : UInt64) (text out : List UInt8)
    (K : DataMem → Prop) (j : Nat) (m : DataMem) : Prop :=
  m =⋆ Eq ((p + .ofNat (unumWr c n j)).toBytes.At ps.toBitVec) ⋆
    (Eq ((c + .ofNat j).toBytes.At pc.toBitVec) ⋆
      (Eq ((text.take (unumWr c n j) ++ out.drop (unumWr c n j)).At
        p.toBitVec) ⋆ K))

/-- The low 32 bits (`extract`) of a zero extension (`zext`) of 32 bits. -/
theorem extract_zext32 (y : BitVec 32) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 y) = y := by bv_decide

/-- The condition `gt` after `cmp w, #0x0`. -/
theorem gt_zero_iff (y : BitVec 32) :
    (!(y - BitVec.ofInt 32 (BitVec.toInt (0 : BitVec 64)) == BitVec.zero 32) &&
      (y - BitVec.ofInt 32 (BitVec.toInt (0 : BitVec 64))).msb ==
        ((y - BitVec.ofInt 32 (BitVec.toInt (0 : BitVec 64))).toInt !=
          y.toInt - (BitVec.ofInt 32 (BitVec.toInt (0 : BitVec 64))).toInt)) =
      true ↔ 0 < y.toInt := by
  have e : BitVec.ofInt 32 (BitVec.toInt (0 : BitVec 64)) = 0#32 := by decide
  rw [e, ← BitVec.toInt_zero (w := 32), ← BitVec.slt_iff_toInt_lt]
  simp only [BitVec.sub_zero, BitVec.toInt_zero, Int.sub_zero,
    bne_self_eq_false, BitVec.zero_eq]
  bv_decide

/-- `sub w, w, #0x1` on `BitVec.ofInt 32 z`. -/
theorem ofInt32_sub_one (z : Int) :
    BitVec.ofInt 32 z - BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) =
      BitVec.ofInt 32 (z - 1) := by
  have e : BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) = 1#32 := by decide
  rw [e]
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofInt]

/-- `BitVec.toInt` of `BitVec.ofInt 32 z` for `z` in range. -/
theorem toInt_ofInt32 (z : Int) (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) :
    (BitVec.ofInt 32 z).toInt = z := by
  rw [BitVec.toInt_ofInt]
  rw [Int.bmod_def]
  split <;> omega

/-- Rotates (`rot`) the third conjunct of a separating conjunction to the
front. -/
theorem sep_rot3 (a b c r : DataMem → Prop) :
    a ⋆ (b ⋆ (c ⋆ r)) = c ⋆ (a ⋆ (b ⋆ r)) := by ac_rfl

/-- The bytes that `str` stores for `x + 1`. -/
theorem toBytes_add_one (x : UInt64) :
    Int.toBytes 8 (x.toBitVec + 1).toInt = (x + 1).toBytes := rfl

/-- `c + j + 1` for `UInt64`s (`u64`). -/
theorem ofNat_add_one_u64 (c : UInt64) (j : Nat) :
    c + UInt64.ofNat j + 1 = c + UInt64.ofNat (j + 1) := by
  rw [UInt64.ofNat_add, UInt64.add_assoc]; rfl

/-- One call of `CHECK_AND_PUT_CHAR` that does not write (`no`), because the
count is at least the size `n`. -/
theorem UnumMem.no {ps pc p c n : UInt64} {text out : List UInt8}
    {K : DataMem → Prop} {j : Nat} {m : DataMem}
    (h : m =⋆ Eq ((Int.toBytes 8 ((c + .ofNat j).toBitVec + 1).toInt).At
        pc.toBitVec) ⋆
      (Eq ((p + .ofNat (unumWr c n j)).toBytes.At ps.toBitVec) ⋆
        (Eq ((text.take (unumWr c n j) ++ out.drop (unumWr c n j)).At
          p.toBitVec) ⋆ K)))
    (hn : n.toNat ≤ c.toNat + j) :
    UnumMem ps pc p c n text out K (j + 1) m := by
  have hw : unumWr c n (j + 1) = unumWr c n j := by unfold unumWr; omega
  unfold UnumMem
  rw [hw]
  rw [toBytes_add_one, ofNat_add_one_u64, Std.ExtHashMap.sep_comm_l] at h
  exact h

/-- One call of `CHECK_AND_PUT_CHAR` that writes (`yes`) `text[j]`. -/
theorem UnumMem.yes {ps pc p c n : UInt64} {text out : List UInt8}
    {K : DataMem → Prop} {j : Nat} {m : DataMem} {x : UInt8}
    (h : m =⋆ Eq ((Int.toBytes 8 ((c + .ofNat j).toBitVec + 1).toInt).At
        pc.toBitVec) ⋆
      (Eq ((Int.toBytes 8 ((p + .ofNat (unumWr c n j)).toBitVec + 1).toInt).At
          ps.toBitVec) ⋆
        (Eq (((text.take (unumWr c n j) ++ out.drop (unumWr c n j)).set
          (unumWr c n j) x).At p.toBitVec) ⋆ K)))
    (hlt : c.toNat + j < n.toNat) (hj : j < text.length)
    (hx : text[j] = x) (ho : j < out.length) :
    UnumMem ps pc p c n text out K (j + 1) m := by
  have hw : unumWr c n j = j := by unfold unumWr; omega
  have hw' : unumWr c n (j + 1) = j + 1 := by unfold unumWr; omega
  unfold UnumMem
  rw [hw']
  rw [hw, toBytes_add_one, toBytes_add_one, ofNat_add_one_u64,
    ofNat_add_one_u64, ← hx, List.set_take_append_drop hj ho,
    Std.ExtHashMap.sep_comm_l] at h
  exact h

/-- The first padding (`pad`) loop of `unsigned_num_print` (unsigned number
print), from `unsigned_num_print + 0x64` to `unsigned_num_print + 0x70`: it
prints the first `P` characters of `text`, which are `padc`, where `w3` is
the `int` `z0` and `P` is `z0` if it is positive, else 0. -/
theorem unum_pad [Labels] (code : Code) (f : Int64)
    (h : Loaded code f unsigned_num_print_o)
    (h_sym : label "unsigned_num_print" = f)
    (d : MachineData) (ps pc p c n : UInt64) (text out : List UInt8)
    (K : DataMem → Prop) (padc : UInt8) (z0 : Int) (P : Nat)
    (hP : P = z0.toNat) (hz1 : -2 ^ 31 ≤ z0) (hz2 : z0 < 2 ^ 31)
    (hPT : P ≤ text.length)
    (htext : ∀ i (hi : i < P), text[i]'(by omega) = padc)
    (hout : min text.length (n.toNat - c.toNat) ≤ out.length)
    (hol : out.length ≤ 2 ^ 64)
    (hcT : c.toNat + text.length < 2 ^ 64)
    (h_x0 : d.regs.X0 = ps) (h_x1 : d.regs.X1 = n) (h_x2 : d.regs.X2 = pc)
    (h_x3 : d.regs.X3 = ⟨(BitVec.ofInt 32 z0).zeroExtend 64⟩)
    (h_x5 : BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 d.regs.X5.toBitVec)
      = padc.toBitVec)
    (h_mem : UnumMem ps pc p c n text out K 0 d.dmem) :
    Eventually code.stepWp (fun s => s.pc = f + 0x70 ∧ ∃ x3 x4 st m,
      UnumMem ps pc p c n text out K P m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X4 := x4 }
        status := st
        dmem := m })
    ⟨d, f + 0x64⟩ := by
  refine loop_rule (measure fun i => P + 1 - i).wf
    (fun i s => s.pc = f + 0x64 ∧ i ≤ P ∧ ∃ x4 st m,
      UnumMem ps pc p c n text out K i m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := ⟨(BitVec.ofInt 32 (z0 - i)).zeroExtend 64⟩
          X4 := x4 }
        status := st
        dmem := m })
    _ 0 _ ⟨rfl, Nat.zero_le _, d.regs.X4, d.status, d.dmem, h_mem,
      by simp [← h_x3]⟩ ?_
  rintro i ⟨d', pc'⟩ ⟨rfl, hi, x4, st, m, hm, rfl⟩
  have hB := hm
  unfold UnumMem at hB
  rw [Std.ExtHashMap.sep_comm_l] at hB
  have hzi1 : -2 ^ 31 ≤ z0 - i := by omega
  have hzi2 : z0 - i < 2 ^ 31 := by omega
  instr "ldr x4, [x2]" at f + 0x64
  simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
    [h_x2, MachineData.load_of_sep64_zero hB (by simp [UInt64.toBytes_length]),
      Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
      BitVec.ofInt_ofBytes_toBytes64]
  instr "cmp w3, #0x0" at f + 0x68
  instr "b.gt cc <unsigned_num_print+0xcc>" at f + 0x6c
  · intro hgt
    rw [extract_zext32, gt_zero_iff, toInt_ofInt32 _ hzi1 hzi2] at hgt
    have hiP : i < P := by omega
    have hcj : (c + UInt64.ofNat i).toNat = c.toNat + i := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_sym]
    instr "cmp x1, x4" at f + 0xcc
    instr "b.ls e8 <unsigned_num_print+0xe8>" at f + 0xd0
    · intro hls
      simp only [cmp_ls_eq] at hls
      simp only [decide_eq_true_eq, h_x1, UInt64.toNat_toBitVec, hcj] at hls
      rw [h_sym]
      instr "ldr x4, [x2]" at f + 0xe8
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hB (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "sub w3, w3, #0x1" at f + 0xec
      instr "add x4, x4, #0x1" at f + 0xf0
      instr "str x4, [x2]" at f + 0xf4
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hB, Effects.All, MemWidth.bytes]
      have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hB, UInt64.toBytes_length _⟩
        ((c + UInt64.ofNat i).toBitVec + 1).toInt
      instr "b 64 <unsigned_num_print+0x64>" at f + 0xf8
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?rel, rfl, hiP, ?y4, ?yst, _,
        UnumMem.no hB' hls, ?heq⟩)
      case heq =>
        rw [extract_zext32, ofInt32_sub_one,
          show z0 - i - 1 = z0 - ↑(i + 1) by omega]
      case rel => simp only [InvImage, WellFoundedRelation.rel]; omega
    · intro hls
      simp only [cmp_ls_eq] at hls
      simp only [decide_eq_true_eq, h_x1, UInt64.toNat_toBitVec, hcj,
        Nat.not_le] at hls
      have hwr : unumWr c n i = i := by unfold unumWr; omega
      have hio : i < out.length := by omega
      have hOl : unumWr c n i <
          (text.take (unumWr c n i) ++ out.drop (unumWr c n i)).length := by
        simp; omega
      have hA := hm
      unfold UnumMem at hA
      have hO := hA
      rw [sep_rot3] at hO
      instr "ldr x4, [x0]" at f + 0xd4
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [h_x0, MachineData.load_of_sep64_zero hA
          (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "strb w5, [x4]" at f + 0xd8
      simp only [h_x5]
      store_byte hO
      have hO' := Mem.storeInt_byte_sep _ _ (unumWr c n i) _ _ hO hOl
        (by simp; omega) padc
      rw [← sep_rot3] at hO'
      instr "ldr x4, [x0]" at f + 0xdc
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hO'
          (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "add x4, x4, #0x1" at f + 0xe0
      instr "str x4, [x0]" at f + 0xe4
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hO', Effects.All, MemWidth.bytes]
      have hA2 := Mem.storeInt_sep _ 8 _ _ _ ⟨hO', UInt64.toBytes_length _⟩
        ((p + UInt64.ofNat (unumWr c n i)).toBitVec + 1).toInt
      rw [Std.ExtHashMap.sep_comm_l] at hA2
      instr "ldr x4, [x2]" at f + 0xe8
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hA2 (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "sub w3, w3, #0x1" at f + 0xec
      instr "add x4, x4, #0x1" at f + 0xf0
      instr "str x4, [x2]" at f + 0xf4
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hA2, Effects.All, MemWidth.bytes]
      have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hA2, UInt64.toBytes_length _⟩
        ((c + UInt64.ofNat i).toBitVec + 1).toInt
      instr "b 64 <unsigned_num_print+0x64>" at f + 0xf8
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?rel, rfl, hiP, ?y4, ?yst, _,
        UnumMem.yes hB' hls (by omega) (htext i hiP) hio, ?heq⟩)
      case heq =>
        rw [extract_zext32, ofInt32_sub_one,
          show z0 - i - 1 = z0 - ↑(i + 1) by omega]
        rfl
      case rel => simp only [InvImage, WellFoundedRelation.rel]; omega
  · intro hgt
    rw [extract_zext32, gt_zero_iff, toInt_ofInt32 _ hzi1 hzi2] at hgt
    obtain rfl : i = P := by omega
    exact .done _ (.inr ⟨by dsimp only; bv_decide, _, _, _, _, hm, by state_eq⟩)

/-- The condition `cs` (carry set) after `cmp x, y`. -/
theorem cmp_cs_iff (a b : BitVec 64) :
    (↑(a - b).toNat : Int) = ↑a.toNat - ↑b.toNat ↔ b.toNat ≤ a.toNat := by
  constructor
  · intro h; bv_omega
  · intro h; bv_omega

/-- Rotates (`rot`) the fourth conjunct of a separating conjunction to the
front. -/
theorem sep_rot4 (a b c k r : DataMem → Prop) :
    a ⋆ (b ⋆ (c ⋆ (k ⋆ r))) = k ⋆ (a ⋆ (b ⋆ (c ⋆ r))) := by ac_rfl

/-- The address `x + k - 1` as `ldurb` with offset `-1` (`sub_one`) computes
it. -/
theorem addr_sub_one (x : BitVec 64) (k : Nat) (hk : 1 ≤ k)
    (hk' : k < 2 ^ 64) :
    x + ((UInt64.ofNat k).toBitVec + (-1 : Int64).toBitVec) =
      x + BitVec.ofNat 64 (k - 1) := by
  have e : (-1 : Int64).toBitVec = -1#64 := by decide
  have e2 : BitVec.ofNat 64 k = BitVec.ofNat 64 (k - 1) + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e, UInt64.toBitVec_ofNat', e2]
  generalize BitVec.ofNat 64 (k - 1) = y
  bv_decide

/-- `sub x, x, #0x1` on `UInt64.ofNat k` (`u64`) for `1 ≤ k`. -/
theorem ofNat_sub_one_u64 (k : Nat) (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    (UInt64.ofNat k).toBitVec - 1 = (UInt64.ofNat (k - 1)).toBitVec := by
  have e2 : BitVec.ofNat 64 k = BitVec.ofNat 64 (k - 1) + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [UInt64.toBitVec_ofNat', UInt64.toBitVec_ofNat', e2]
  generalize BitVec.ofNat 64 (k - 1) = y
  bv_decide

/-- The output (`out`) loop of `unsigned_num_print` (unsigned number print),
from `unsigned_num_print + 0x70` to `unsigned_num_print + 0xb0`: it prints
the `w` digits in `buf` in reverse order, the characters `P` to `P + w` of
`text`. -/
theorem unum_out [Labels] (code : Code) (f : Int64)
    (h : Loaded code f unsigned_num_print_o)
    (h_sym : label "unsigned_num_print" = f)
    (d : MachineData) (ps pc p c n : UInt64) (text out buf : List UInt8)
    (R : DataMem → Prop) (bufp : UInt64) (w P : Nat)
    (hw0 : 0 < w) (hw : w ≤ 20) (hbuf : buf.length = 20)
    (hPw : P + w ≤ text.length)
    (hdig : ∀ i (hi : i < w),
      text[P + i]'(by omega) = buf[w - 1 - i]'(by omega))
    (hout : min text.length (n.toNat - c.toNat) ≤ out.length)
    (hol : out.length ≤ 2 ^ 64)
    (hcT : c.toNat + text.length < 2 ^ 64)
    (h_x0 : d.regs.X0 = ps) (h_x1 : d.regs.X1 = n) (h_x2 : d.regs.X2 = pc)
    (h_x7 : d.regs.X7 = .ofNat w) (h_x11 : d.regs.X11 = bufp)
    (h_mem : UnumMem ps pc p c n text out (Eq (buf.At bufp.toBitVec) ⋆ R) P
      d.dmem) :
    Eventually code.stepWp (fun s => s.pc = f + 0xb0 ∧ ∃ x3 x4 x8 st m,
      UnumMem ps pc p c n text out (Eq (buf.At bufp.toBitVec) ⋆ R) (P + w) m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X4 := x4
          X8 := x8 }
        status := st
        dmem := m })
    ⟨d, f + 0x70⟩ := by
  instr "sxtw x3, w7" at f + 0x70

  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, ge_iff_le,
    Nat.zero_le, ↓reduceIte, BitVec.ushiftRight_zero, h_x7, extract_ofNat64,
    sext_ofNat32 w (by omega)]
  refine loop_rule (measure fun i => w - i).wf
    (fun i s => s.pc = f + 0x74 ∧ i < w ∧ ∃ x4 x8 st m,
      UnumMem ps pc p c n text out (Eq (buf.At bufp.toBitVec) ⋆ R) (P + i) m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := .ofNat (w - i)
          X4 := x4
          X8 := x8 }
        status := st
        dmem := m })
    _ 0 _ ⟨by dsimp only; bv_decide, hw0, d.regs.X4, d.regs.X8, d.status,
      d.dmem, h_mem, by simp only [Nat.sub_zero, h_x7] <;> rfl⟩ ?_
  rintro i ⟨d', pc'⟩ ⟨rfl, hi, x4, x8, st, m, hm, rfl⟩
  have hB := hm
  unfold UnumMem at hB
  rw [Std.ExtHashMap.sep_comm_l] at hB
  have hcj : (c + UInt64.ofNat (P + i)).toNat = c.toNat + (P + i) := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega : P + i < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  instr "ldr x4, [x2]" at f + 0x74
  simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
    [h_x2, MachineData.load_of_sep64_zero hB (by simp [UInt64.toBytes_length]),
      Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
      BitVec.ofInt_ofBytes_toBytes64]
  instr "cmp x4, x1" at f + 0x78
  instr "b.cs 9c <unsigned_num_print+0x9c>" at f + 0x7c
  · intro hcs
    rw [cmp_cs_iff, h_x1, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec,
      hcj] at hcs
    rw [h_sym]
    instr "ldr x4, [x2]" at f + 0x9c
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.load_of_sep64_zero hB (by simp [UInt64.toBytes_length]),
        Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
        BitVec.ofInt_ofBytes_toBytes64]
    instr "sub x3, x3, #0x1" at f + 0xa0
    instr "add x4, x4, #0x1" at f + 0xa4
    instr "str x4, [x2]" at f + 0xa8
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.store_of_sep64_zero hB, Effects.All, MemWidth.bytes]
    have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hB, UInt64.toBytes_length _⟩
      ((c + UInt64.ofNat (P + i)).toBitVec + 1).toInt
    rw [ofNat_sub_one_u64 _ (by omega) (by omega)]
    instr "cbnz w3, 74 <unsigned_num_print+0x74>" at f + 0xac
    · intro hnz
      rw [extract_ofNat64] at hnz
      have hi1 : i + 1 < w := by
        refine Nat.lt_of_not_le fun hle => hnz ?_
        rw [show w - i - 1 = 0 by omega]; rfl
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?rel, rfl, hi1, ?y4, ?y8, ?yst, _,
        UnumMem.no hB' hcs, ?heq⟩)
      case heq =>
        rw [show w - i - 1 = w - (i + 1) by omega]
      case rel => simp only [InvImage, WellFoundedRelation.rel]; omega
    · intro hnz
      rw [extract_ofNat64] at hnz
      have hi1 : i + 1 = w := by
        have hlt : w - i - 1 < 2 ^ 32 := by omega
        have := congrArg BitVec.toNat hnz
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        have h0 : (0 : BitVec 32).toNat = 0 := rfl
        rw [h0] at this
        omega
      refine .done _ (.inr ⟨by dsimp only; bv_decide, ?y3, ?y4, ?y8, ?yst, _,
        by rw [← hi1]; exact UnumMem.no hB' hcs, by state_eq⟩)
  · intro hcs
    rw [cmp_cs_iff, h_x1, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec,
      hcj, Nat.not_le] at hcs
    have hA := hm
    unfold UnumMem at hA
    have hK := hA
    rw [sep_rot4] at hK
    instr "ldr x4, [x0]" at f + 0x80
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [h_x0, MachineData.load_of_sep64_zero hA
        (by simp [UInt64.toBytes_length]),
        Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
        BitVec.ofInt_ofBytes_toBytes64]
    instr "add x8, x11, x3" at f + 0x84
    instr "ldurb w8, [x8, #-1]" at f + 0x88
    have hwi : w - i - 1 < buf.length := by omega
    rw [h_x11, addr_sub_one _ _ (by omega) (by omega)]
    load_byte hK (by omega)
    have hwr : unumWr c n (P + i) = P + i := by unfold unumWr; omega
    have hio : P + i < out.length := by omega
    have hOl : unumWr c n (P + i) < (text.take (unumWr c n (P + i)) ++
        out.drop (unumWr c n (P + i))).length := by
      simp; omega
    have hO := hA
    rw [sep_rot3] at hO
    instr "strb w8, [x4]" at f + 0x8c
    store_byte hO
    have hO' := Mem.storeInt_byte_sep _ _ (unumWr c n (P + i)) _ _ hO hOl
      (by simp; omega) buf[w - i - 1]
    rw [← sep_rot3] at hO'
    instr "ldr x4, [x0]" at f + 0x90
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.load_of_sep64_zero hO'
        (by simp [UInt64.toBytes_length]),
        Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
        BitVec.ofInt_ofBytes_toBytes64]
    instr "add x4, x4, #0x1" at f + 0x94
    instr "str x4, [x0]" at f + 0x98
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.store_of_sep64_zero hO', Effects.All, MemWidth.bytes]
    have hA2 := Mem.storeInt_sep _ 8 _ _ _ ⟨hO', UInt64.toBytes_length _⟩
      ((p + UInt64.ofNat (unumWr c n (P + i))).toBitVec + 1).toInt
    rw [Std.ExtHashMap.sep_comm_l] at hA2
    instr "ldr x4, [x2]" at f + 0x9c
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.load_of_sep64_zero hA2 (by simp [UInt64.toBytes_length]),
        Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
        BitVec.ofInt_ofBytes_toBytes64]
    instr "sub x3, x3, #0x1" at f + 0xa0
    instr "add x4, x4, #0x1" at f + 0xa4
    instr "str x4, [x2]" at f + 0xa8
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [MachineData.store_of_sep64_zero hA2, Effects.All, MemWidth.bytes]
    have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hA2, UInt64.toBytes_length _⟩
      ((c + UInt64.ofNat (P + i)).toBitVec + 1).toInt
    have hyes := UnumMem.yes hB' hcs (by omega)
      ((hdig i hi).trans (by congr 1; omega)) hio
    rw [ofNat_sub_one_u64 _ (by omega) (by omega)]
    instr "cbnz w3, 74 <unsigned_num_print+0x74>" at f + 0xac
    · intro hnz
      rw [extract_ofNat64] at hnz
      have hi1 : i + 1 < w := by
        refine Nat.lt_of_not_le fun hle => hnz ?_
        rw [show w - i - 1 = 0 by omega]; rfl
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?wrel, rfl, hi1, ?wy4, ?wy8, ?wyst, _,
        hyes, ?wheq⟩)
      case wheq =>
        simp only [show w - i - 1 = w - (i + 1) by omega]
        rfl
      case wrel => simp only [InvImage, WellFoundedRelation.rel]; omega
    · intro hnz
      rw [extract_ofNat64] at hnz
      have hi1 : i + 1 = w := by
        have hlt : w - i - 1 < 2 ^ 32 := by omega
        have := congrArg BitVec.toNat hnz
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        have h0 : (0 : BitVec 32).toNat = 0 := rfl
        rw [h0] at this
        omega
      refine .done _ (.inr ⟨by dsimp only; bv_decide, ?wy3, ?wy4, ?wy8, ?wyst,
        _, by rw [← hi1]; exact hyes, by state_eq⟩)

/-- The sign bit that `tbnz w, #31` tests: whether (`iff`) the `int` is
negative (`neg`). -/
theorem neg_bit_iff (z : Int) (i : Nat) (h1 : -2 ^ 31 ≤ z + i)
    (h2 : z + i < 2 ^ 31) :
    (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.ofInt 32 z + BitVec.ofInt 32 i))).getLsbD 31 = true ↔
      z + i < 0 := by
  rw [extract_zext32, ← BitVec.ofInt_add,
    show (31 : Nat) = 32 - 1 from rfl, ← BitVec.msb_eq_getLsbD_last,
    BitVec.msb_eq_toInt, toInt_ofInt32 _ h1 h2]
  simp


/-- `add w, w, #0x1` on `BitVec.ofInt 32 z + BitVec.ofInt 32 i`. -/
theorem ofInt32_add_one (z : Int) (i : Nat) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
        (BitVec.ofInt 32 z + BitVec.ofInt 32 i)) +
      BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) =
      BitVec.ofInt 32 z + BitVec.ofInt 32 ↑(i + 1) := by
  have e : BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) = 1#32 := by decide
  rw [e, extract_zext32, BitVec.add_assoc]
  congr 1
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_add]

/-- The last padding loop of `unsigned_num_print` (unsigned number print) for
a negative (`neg`) `padn`, from `unsigned_num_print + 0xb4` to
`unsigned_num_print + 0xb8`: it prints the `Q` characters of `text` from `P`
on, which are `padc`, where `w6` is the `int` `z0` and `Q` is `-z0` if it is
positive, else 0. -/
theorem unum_neg [Labels] (code : Code) (f : Int64)
    (h : Loaded code f unsigned_num_print_o)
    (h_sym : label "unsigned_num_print" = f)
    (d : MachineData) (ps pc p c n : UInt64) (text out : List UInt8)
    (K : DataMem → Prop) (padc : UInt8) (z0 : Int) (P Q : Nat)
    (hQ : Q = (-z0).toNat) (hz1 : -2 ^ 31 ≤ z0) (hz2 : z0 < 2 ^ 31)
    (hPT : P + Q ≤ text.length)
    (htext : ∀ i (hi : i < Q), text[P + i]'(by omega) = padc)
    (hout : min text.length (n.toNat - c.toNat) ≤ out.length)
    (hol : out.length ≤ 2 ^ 64)
    (hcT : c.toNat + text.length < 2 ^ 64)
    (h_x0 : d.regs.X0 = ps) (h_x1 : d.regs.X1 = n) (h_x2 : d.regs.X2 = pc)
    (h_x6 : d.regs.X6 = ⟨(BitVec.ofInt 32 z0).zeroExtend 64⟩)
    (h_x5 : BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 d.regs.X5.toBitVec)
      = padc.toBitVec)
    (h_mem : UnumMem ps pc p c n text out K P d.dmem) :
    Eventually code.stepWp (fun s => s.pc = f + 0xb8 ∧ ∃ x3 x6 st m,
      UnumMem ps pc p c n text out K (P + Q) m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X6 := x6 }
        status := st
        dmem := m })
    ⟨d, f + 0xb4⟩ := by
  refine loop_rule (measure fun i => Q + 1 - i).wf
    (fun i s => s.pc = f + 0xb4 ∧ i ≤ Q ∧ ∃ x3 st m,
      UnumMem ps pc p c n text out K (P + i) m ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X6 := ⟨(BitVec.ofInt 32 (z0 + i)).zeroExtend 64⟩ }
        status := st
        dmem := m })
    _ 0 _ ⟨rfl, Nat.zero_le _, d.regs.X3, d.status, d.dmem, h_mem,
      by simp [← h_x6]⟩ ?_
  rintro i ⟨d', pc'⟩ ⟨rfl, hi, x3, st, m, hm, rfl⟩
  have hzi1 : -2 ^ 31 ≤ z0 + i := by omega
  have hzi2 : z0 + i < 2 ^ 31 := by omega
  instr "tbnz w6, #31, fc <unsigned_num_print+0xfc>" at f + 0xb4
  · intro hneg
    rw [neg_bit_iff _ _ hzi1 hzi2] at hneg
    have hiQ : i < Q := by omega
    have hcj : (c + UInt64.ofNat (P + i)).toNat = c.toNat + (P + i) := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega : P + i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    have hB := hm
    unfold UnumMem at hB
    rw [Std.ExtHashMap.sep_comm_l] at hB
    rw [h_sym]
    instr "ldr x3, [x2]" at f + 0xfc
    simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
      [h_x2, MachineData.load_of_sep64_zero hB
        (by simp [UInt64.toBytes_length]),
        Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
        BitVec.ofInt_ofBytes_toBytes64]
    instr "cmp x3, x1" at f + 0x100
    instr "b.cs 11c <unsigned_num_print+0x11c>" at f + 0x104
    · intro hcs
      rw [cmp_cs_iff, h_x1, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec,
        hcj] at hcs
      rw [h_sym]
      instr "ldr x3, [x2]" at f + 0x11c
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hB (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "add w6, w6, #0x1" at f + 0x120
      instr "add x3, x3, #0x1" at f + 0x124
      instr "str x3, [x2]" at f + 0x128
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hB, Effects.All, MemWidth.bytes]
      have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hB, UInt64.toBytes_length _⟩
        ((c + UInt64.ofNat (P + i)).toBitVec + 1).toInt
      instr "b b4 <unsigned_num_print+0xb4>" at f + 0x12c
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?rel, rfl, hiQ, ?y3, ?yst, _,
        UnumMem.no hB' hcs, ?heq⟩)
      case rel => simp only [InvImage, WellFoundedRelation.rel]; omega
      case heq => rw [ofInt32_add_one]
    · intro hcs
      rw [cmp_cs_iff, h_x1, UInt64.toNat_toBitVec, UInt64.toNat_toBitVec,
        hcj, Nat.not_le] at hcs
      have hwr : unumWr c n (P + i) = P + i := by unfold unumWr; omega
      have hio : P + i < out.length := by omega
      have hOl : unumWr c n (P + i) < (text.take (unumWr c n (P + i)) ++
          out.drop (unumWr c n (P + i))).length := by
        simp; omega
      have hA := hm
      unfold UnumMem at hA
      have hO := hA
      rw [sep_rot3] at hO
      instr "ldr x3, [x0]" at f + 0x108
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [h_x0, MachineData.load_of_sep64_zero hA
          (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "strb w5, [x3]" at f + 0x10c
      simp only [h_x5]
      store_byte hO
      have hO' := Mem.storeInt_byte_sep _ _ (unumWr c n (P + i)) _ _ hO hOl
        (by simp; omega) padc
      rw [← sep_rot3] at hO'
      instr "ldr x3, [x0]" at f + 0x110
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hO'
          (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "add x3, x3, #0x1" at f + 0x114
      instr "str x3, [x0]" at f + 0x118
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hO', Effects.All, MemWidth.bytes]
      have hA2 := Mem.storeInt_sep _ 8 _ _ _ ⟨hO', UInt64.toBytes_length _⟩
        ((p + UInt64.ofNat (unumWr c n (P + i))).toBitVec + 1).toInt
      rw [Std.ExtHashMap.sep_comm_l] at hA2
      instr "ldr x3, [x2]" at f + 0x11c
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.load_of_sep64_zero hA2 (by simp [UInt64.toBytes_length]),
          Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
          BitVec.ofInt_ofBytes_toBytes64]
      instr "add w6, w6, #0x1" at f + 0x120
      instr "add x3, x3, #0x1" at f + 0x124
      instr "str x3, [x2]" at f + 0x128
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hA2, Effects.All, MemWidth.bytes]
      have hB' := Mem.storeInt_sep _ 8 _ _ _ ⟨hA2, UInt64.toBytes_length _⟩
        ((c + UInt64.ofNat (P + i)).toBitVec + 1).toInt
      instr "b b4 <unsigned_num_print+0xb4>" at f + 0x12c
      rw [h_sym]
      refine .done _ (.inl ⟨i + 1, ?wrel, rfl, hiQ, ?wy3, ?wyst, _,
        UnumMem.yes hB' hcs (by omega : P + i < text.length) (htext i hiQ)
          hio, ?wheq⟩)
      case wrel => simp only [InvImage, WellFoundedRelation.rel]; omega
      case wheq => rw [ofInt32_add_one]
  · intro hneg
    rw [neg_bit_iff _ _ hzi1 hzi2] at hneg
    obtain rfl : i = Q := by omega
    exact .done _ (.inr ⟨by dsimp only; bv_decide, _, _, _, _, hm,
      by state_eq⟩)

/-- `x4` (radix) after `mov w4, w4` in `unsigned_num_print` (unsigned
number print). -/
theorem unum_x4 (x : UInt64) (b : Nat) (hb : b < 2 ^ 32)
    (h : x.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b) :
    (⟨BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 0) |||
      BitVec.extractLsb' 0 32 x.toBitVec)⟩ : UInt64) = .ofNat b := by
  apply UInt64.toBitVec_inj.mp
  rw [h, UInt64.toBitVec_ofNat']
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- The low byte of `x5` (`padc`) after `and w5, w5, #0xff` in
`unsigned_num_print` (unsigned number print). -/
theorem unum_x5 (x : BitVec 64) :
    BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.extractLsb' 0 32 x &&&
        BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64))))) =
      BitVec.extractLsb' 0 8 x := by
  have e : BitVec.ofInt 32 (BitVec.toInt (255 : BitVec 64)) = 255#32 := by
    decide
  rw [e]
  bv_decide

/-- `x7` after `mov x7, #0x0` in `unsigned_num_print` (unsigned number
print). -/
theorem unum_x7 :
    (⟨((0 : BitVec 64) &&& BitVec.ofNat 64 65535) <<< 0⟩ : UInt64) = 0 := by
  decide

/-- `x9` (`ascii_a - 10`) after `tst`, `csel` and `sub` in
`unsigned_num_print` (unsigned number print). -/
theorem unum_x9 (x : BitVec 64) (cap : Bool) (h : x.getLsbD 0 = cap) :
    (⟨BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (if (BitVec.extractLsb' 0 32 x &&&
          BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) ==
            BitVec.zero 32) = true then
        BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          ((BitVec.ofInt 32 (BitVec.toInt (97 : BitVec 64)) &&&
            BitVec.ofNat 32 65535) <<< 0))
      else
        BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          ((BitVec.ofInt 32 (BitVec.toInt (65 : BitVec 64)) &&&
            BitVec.ofNat 32 65535) <<< 0)))) -
      BitVec.ofInt 32 (BitVec.toInt (10 : BitVec 64)))⟩ : UInt64) =
      .ofNat (unumA cap - 10) := by
  have e1 : BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) = 1#32 := by decide
  have e10 : BitVec.ofInt 32 (BitVec.toInt (10 : BitVec 64)) = 10#32 := by
    decide
  have e97 : BitVec.ofInt 32 (BitVec.toInt (97 : BitVec 64)) = 97#32 := by
    decide
  have e65 : BitVec.ofInt 32 (BitVec.toInt (65 : BitVec 64)) = 65#32 := by
    decide
  apply UInt64.toBitVec_inj.mp
  rw [e1, e10, e97, e65, UInt64.toBitVec_ofNat', BitVec.zero_eq]
  subst h
  cases hx : x.getLsbD 0 <;> simp only [unumA] <;> bv_decide

/-- The length of `unumText`. -/
theorem unumText_length (cap : Bool) (b v : Nat) (padn : Int)
    (padc : UInt8) :
    (unumText cap b v padn padc).length =
      (padn - (unumDigits cap b v).length).toNat +
        (unumDigits cap b v).length +
        (-(padn + (unumDigits cap b v).length)).toNat := by
  simp only [unumText, List.length_append, List.length_replicate]

/-- The left padding of `unumText` is `padc`. -/
theorem unumText_left (cap : Bool) (b v : Nat) (padn : Int) (padc : UInt8)
    (i : Nat) (hi : i < (padn - (unumDigits cap b v).length).toNat)
    (hl : i < (unumText cap b v padn padc).length) :
    (unumText cap b v padn padc)[i] = padc := by
  simp only [unumText]
  rw [List.getElem_append_left (by simp; omega),
    List.getElem_append_left (by simp; omega), List.getElem_replicate]

/-- The digits of `unumText`. -/
theorem unumText_digit (cap : Bool) (b v : Nat) (padn : Int) (padc : UInt8)
    (i : Nat) (hi : i < (unumDigits cap b v).length)
    (hl : (padn - (unumDigits cap b v).length).toNat + i <
      (unumText cap b v padn padc).length) :
    (unumText cap b v padn padc)[(padn - (unumDigits cap b v).length).toNat +
      i] = (unumDigits cap b v)[i] := by
  simp only [unumText]
  rw [List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by simp)]
  simp

/-- The right padding of `unumText` is `padc`. -/
theorem unumText_right (cap : Bool) (b v : Nat) (padn : Int) (padc : UInt8)
    (i : Nat) (hl : (padn - (unumDigits cap b v).length).toNat +
      (unumDigits cap b v).length + i < (unumText cap b v padn padc).length) :
    (unumText cap b v padn padc)[(padn - (unumDigits cap b v).length).toNat +
      (unumDigits cap b v).length + i] = padc := by
  simp only [unumText]
  rw [List.getElem_append_right (by simp)]
  simp

/-- `w7` after `add w7, w7, #0x1` in `unsigned_num_print` (unsigned number
print): the number of digits, the length (`len`) of the buffer content. -/
theorem unum_len (k : Nat) (hk0 : 0 < k) (hk : k ≤ 20) :
    BitVec.zeroExtend 64
      (BitVec.extractLsb' 0 32 (UInt64.ofNat (k - 1)).toBitVec +
        BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64))) =
      BitVec.ofNat 64 k := by
  have e : BitVec.ofInt 32 (BitVec.toInt (1 : BitVec 64)) = 1#32 := by decide
  rw [e, UInt64.toBitVec_ofNat']
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- `w3` after `sub w3, w6, w7` in `unsigned_num_print` (unsigned number
print): the count (`cnt`) of the first padding loop, `padn - width`. -/
theorem unum_padcnt (z : Int) (k : Nat) :
    BitVec.ofInt 32 z - BitVec.extractLsb' 0 32 (BitVec.ofNat 64 k) =
      BitVec.ofInt 32 (z - k) := by
  have e : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 k) = BitVec.ofInt 32 k := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [e, eq_comm, BitVec.eq_sub_iff_add_eq, ← BitVec.ofInt_add,
    Int.sub_add_cancel]

/-- `w6` after `add w6, w7, w6` in `unsigned_num_print` (unsigned number
print): `width + padn`, the negated (`neg`) count (`cnt`) of the last
padding loop. -/
theorem unum_negcnt (z : Int) (k : Nat) :
    BitVec.extractLsb' 0 32 (BitVec.ofNat 64 k) + BitVec.ofInt 32 z =
      BitVec.ofInt 32 (z + k) := by
  have e : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 k) = BitVec.ofInt 32 k := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [e, BitVec.ofInt_add, BitVec.add_comm]

/-- `UnumMem` before the first character (`zero`). -/
theorem UnumMem.zero {ps pc p c n : UInt64} {text out : List UInt8}
    {K : DataMem → Prop} {m : DataMem}
    (h : m =⋆ Eq (p.toBytes.At ps.toBitVec) ⋆
      (Eq (c.toBytes.At pc.toBitVec) ⋆ (Eq (out.At p.toBitVec) ⋆ K))) :
    UnumMem ps pc p c n text out K 0 m := by
  unfold UnumMem unumWr
  simpa using h

/-- `unsigned_num_print (s, n, chars_printed, unum, radix, padc, padn,
capitalise)` (unsigned number print, `unum`) with `s` in `x0` pointing to
the output pointer `p`, `chars_printed` in `x2` pointing to the count `c`,
and the 20-byte `num_buf` at `sp - 0x18`. It prints
`unumText cap b v padn padc` with `CHECK_AND_PUT_CHAR`: it writes the
characters while the count is below `n`, and counts all of them. -/
theorem unum_spec [Labels] (code : Code) (f : Int64)
    (h : Loaded code f unsigned_num_print_o)
    (h_sym : label "unsigned_num_print" = f)
    (s0 : MachineData) (p c : UInt64) (cap : Bool) (b v : Nat)
    (padn : Int) (padc : UInt8) (out stk : List UInt8)
    (R : DataMem → Prop)
    (hv : v < 2 ^ 64) (hb : 10 ≤ b) (hb' : b < 2 ^ 32)
    (hpad1 : -2 ^ 30 ≤ padn) (hpad2 : padn < 2 ^ 30)
    (hc : c.toNat < 2 ^ 63) (hstk : stk.length = 20)
    (hout : min (unumText cap b v padn padc).length
      (s0.regs.X1.toNat - c.toNat) ≤ out.length)
    (hol : out.length ≤ 2 ^ 64)
    (h_x3 : s0.regs.X3 = .ofNat v)
    (h_x4 : s0.regs.X4.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_x5 : s0.regs.X5.toBitVec.extractLsb' 0 8 = padc.toBitVec)
    (h_x6 : s0.regs.X6.toBitVec.extractLsb' 0 32 = BitVec.ofInt 32 padn)
    (h_x7 : s0.regs.X7.toBitVec.getLsbD 0 = cap)
    (h_mem : s0.dmem =⋆ Eq (p.toBytes.At s0.regs.X0.toBitVec) ⋆
      (Eq (c.toBytes.At s0.regs.X2.toBitVec) ⋆
        (Eq (out.At p.toBitVec) ⋆
          (Eq (stk.At (s0.regs.SP - 0x18).toBitVec) ⋆ R)))) :
    Eventually code.stepWp (fun s => s.pc = s0.regs.X30.toInt64 ∧
      ∃ x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 st m, ∃ stk' : List UInt8,
      s.data = { s0 with
        regs := { s0.regs with
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11
          X12 := x12
          X13 := x13 }
        status := st
        dmem := m } ∧
      m =⋆ Eq ((p + .ofNat (min (unumText cap b v padn padc).length
          (s0.regs.X1.toNat - c.toNat))).toBytes.At s0.regs.X0.toBitVec) ⋆
        (Eq ((c + .ofNat (unumText cap b v padn padc).length).toBytes.At
          s0.regs.X2.toBitVec) ⋆
          (Eq (((unumText cap b v padn padc).take
              (min (unumText cap b v padn padc).length
                (s0.regs.X1.toNat - c.toNat)) ++
            out.drop (min (unumText cap b v padn padc).length
              (s0.regs.X1.toNat - c.toNat))).At p.toBitVec) ⋆
            (Eq (stk'.At (s0.regs.SP - 0x18).toBitVec) ⋆ R))))
    ⟨s0, f⟩ := by
  instr "tst w7, #0x1" at f
  instr "sub sp, sp, #0x20" at f + 0x4
  instr "mov w7, #0x41" at f + 0x8
  instr "mov w8, #0x61" at f + 0xc
  instr "csel w8, w8, w7, eq" at f + 0x10
  instr "and w5, w5, #0xff" at f + 0x14
  instr "mov w4, w4" at f + 0x18
  instr "sub w9, w8, #0xa" at f + 0x1c
  instr "add x11, sp, #0x8" at f + 0x20
  instr "mov x7, #0x0" at f + 0x24
  simp only [unum_x4 _ b hb' h_x4, unum_x7]
  rw [show f + 36 + 4 = f + 0x28 by bv_decide]
  have hM := h_mem
  rw [sep_rot4] at hM
  refine eventually_trans _ _ _ _ (unum_digits code f h h_sym _ cap b v stk
    _ (s0.regs.SP - 0x18) hv hb hb' hstk h_x3 rfl rfl ?x9 ?bufp hM) ?_
  case x9 => exact unum_x9 _ cap h_x7
  case bufp => uint64_eq
  rintro ⟨d2, pc2⟩ ⟨rfl, B, hB0, hB20, hBD, x3, x8, x10, x12, x13, st, m,
    hm, rfl⟩
  instr "add w7, w7, #0x1" at f + 0x5c
  instr "sub w3, w6, w7" at f + 0x60
  have hDw : (unumDigits cap b v).length = B.length := by
    rw [hBD, List.length_reverse]
  have hTl := unumText_length cap b v padn padc
  rw [hDw] at hTl
  simp only [unum_len _ hB0 hB20, h_x6, unum_padcnt]
  rw [show f + 96 + 4 = f + 0x64 by bv_decide]
  rw [← sep_rot4] at hm
  refine eventually_trans _ _ _ _ (unum_pad code f h h_sym _ s0.regs.X0
    s0.regs.X2 p c s0.regs.X1 (unumText cap b v padn padc) out _ padc
    (padn - B.length) _ rfl (by omega) (by omega) (by omega) ?htext
    (by omega) hol (by omega) rfl rfl rfl rfl ?hx5 (UnumMem.zero hm)) ?_
  case htext =>
    intro i hi
    exact unumText_left cap b v padn padc i (by rw [hDw]; exact hi) _
  case hx5 => rw [unum_x5, h_x5]
  rintro ⟨d3, pc3⟩ ⟨rfl, x3', x4', st', m', hm', rfl⟩
  refine eventually_trans _ _ _ _ (unum_out code f h h_sym _ s0.regs.X0
    s0.regs.X2 p c s0.regs.X1 (unumText cap b v padn padc) out
    (B ++ stk.drop B.length) R (s0.regs.SP - 0x18) B.length
    (padn - B.length).toNat hB0 hB20 (by simp; omega) (by omega) ?hdig
    hout hol (by omega) rfl rfl rfl rfl ?x11 hm') ?_
  case x11 => uint64_eq
  case hdig =>
    intro i hi
    have := unumText_digit cap b v padn padc i (by omega) (by omega)
    simp only [hBD, List.length_reverse, List.getElem_reverse] at this
    rw [this, List.getElem_append_left]
  rintro ⟨d4, pc4⟩ ⟨rfl, x3'', x4'', x8', st'', m'', hm'', rfl⟩
  instr "add w6, w7, w6" at f + 0xb0
  simp only [h_x6, unum_negcnt]
  rw [show f + 176 + 4 = f + 0xb4 by bv_decide]
  refine eventually_trans _ _ _ _ (unum_neg code f h h_sym _ s0.regs.X0
    s0.regs.X2 p c s0.regs.X1 (unumText cap b v padn padc) out _ padc
    (padn + B.length) ((padn - B.length).toNat + B.length) _ rfl
    (by omega) (by omega) (by omega) ?htext2 hout hol (by omega) rfl rfl rfl
    rfl ?hx5' hm'') ?_
  case htext2 =>
    intro i hi
    have := unumText_right cap b v padn padc i (by omega)
    simp only [hDw] at this
    exact this
  case hx5' => rw [unum_x5, h_x5]
  rintro ⟨d5, pc5⟩ ⟨rfl, x3c, x6c, stc, mc, hmc, rfl⟩
  instr "add sp, sp, #0x20" at f + 0xb8
  instr "ret" at f + 0xbc
  rw [← hTl] at hmc
  unfold UnumMem unumWr at hmc
  exact .done _ ⟨rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    by state_eq, hmc⟩

