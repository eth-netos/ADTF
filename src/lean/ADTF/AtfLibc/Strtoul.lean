module

import ADTF.AtfLibc.Listing.strtoul_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strtoul` from TF-A's `libc/strtoul.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strtoul` in ATF's `strtoul.o`. -/
def strtoul_o : List Instr := objdumpAArch64(strtoul_o_dump)

/-- Whether `c` is a space for TF-A's `isspace` (in `stdlib.h`): `' '`,
`'\r'`, `'\n'`, `'\t'` or `'\b'`. -/
def isSpace (c : UInt8) : Bool :=
  c == 32 || c == 13 || c == 10 || c == 9 || c == 8

/-- The byte at index `k` of the string `str` with its terminating 0, or 0
after the end. -/
def byteAt (str : List UInt8) (k : Nat) : UInt8 := (str ++ [0]).getD k 0

/-- The number of white space (`ws`) bytes at the start of `str`. -/
def strtoWs (str : List UInt8) : Nat := (str.takeWhile isSpace).length

/-- Whether the number in `str` is negative (`neg`), i.e. has a `-`
sign. -/
def strtoNeg (str : List UInt8) : Bool := byteAt str (strtoWs str) == 45

/-- The length of the sign of the number in `str`: 1 if there is a `-` or
`+`, else 0. -/
def strtoSign (str : List UInt8) : Nat :=
  if byteAt str (strtoWs str) == 45 || byteAt str (strtoWs str) == 43 then 1
  else 0

/-- The register (`reg`) value of `b`: 1 or 0. -/
def boolReg (b : Bool) : UInt64 := if b then 1 else 0

/-- The register (`reg`) value after `ldrb` (load register byte) loads the
byte `b`. -/
def ldrbReg (b : UInt8) : UInt64 :=
  ⟨BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)⟩

theorem byteAt_eq (str : List UInt8) (k : Nat)
    (hk : k < (str ++ [0]).length) : byteAt str k = (str ++ [0])[k] :=
  (List.getElem_eq_getD 0).symm

/-- `BitVec.ofNat` of `i + 1`, for 64-bit vectors. -/
theorem ofNat_add_one64 (i : Nat) :
    BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem isSpace_le {c : UInt8} (h : isSpace c = true) : c.toNat ≤ 32 := by
  simp only [isSpace, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> decide

/-- The condition `hi` (unsigned higher) of `cmp` with an immediate (`imm`)
`k` on a 32-bit register into which `ldrb` loaded the byte `b`. -/
theorem ldrb_cmp_imm_hi_iff (b : UInt8) (k : BitVec 32) :
    ((↑(BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.zeroExtend 32 b.toBitVec)) - k).toNat : Int) ==
        ↑(BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.zeroExtend 32 b.toBitVec))).toNat - ↑k.toNat &&
      !(BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
          (BitVec.zeroExtend 32 b.toBitVec)) - k == BitVec.zero 32)) = true ↔
      k.toNat < b.toNat := by
  have e : BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) = BitVec.zeroExtend 32 b.toBitVec :=
    by bv_decide
  have hb : (BitVec.zeroExtend 32 b.toBitVec).toNat = b.toNat := by simp
  rw [e]
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, BitVec.zero_eq]
  rw [← hb]
  generalize BitVec.zeroExtend 32 b.toBitVec = r
  constructor
  · rintro ⟨h1, h2⟩
    bv_omega
  · intro h
    constructor <;> bv_omega

/-- The condition `eq` of `cmp` with an immediate (`imm`) `k` on a 32-bit
register into which `ldrb` loaded the byte `b`. -/
theorem ldrb_cmp_imm_eq_iff (b : UInt8) (k : BitVec 32) :
    (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) - k == BitVec.zero 32) = true ↔
      b.toNat = k.toNat := by
  have e : BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) = BitVec.zeroExtend 32 b.toBitVec :=
    by bv_decide
  have hb : (BitVec.zeroExtend 32 b.toBitVec).toNat = b.toNat := by simp
  rw [e, ← hb]
  simp only [beq_iff_eq, BitVec.zero_eq]
  generalize BitVec.zeroExtend 32 b.toBitVec = r
  constructor
  · intro h; bv_omega
  · intro h; bv_omega

/-- `ldrb_cmp_imm_eq_iff` with `=` instead of `==`. -/
theorem ldrb_cmp_imm_eq_iff' (b : UInt8) (k : BitVec 32) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) - k = BitVec.zero 32 ↔
      b.toNat = k.toNat := by
  rw [← ldrb_cmp_imm_eq_iff, beq_iff_eq]

/-- `strtoul` tests whether a byte is white space (`ws`) by looking up its
bit in the mask `0x100002700`. -/
theorem ws_bit_iff (b : UInt8) (hb : b.toNat ≤ 32) :
    (BitVec.extractLsb' 0 32 ((UInt64.toBitVec 4294977280).ushiftRight
      ((BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)).toNat % 64))
      ).getLsbD 0 = isSpace b := by
  have key : ∀ n, n < 33 → (BitVec.extractLsb' 0 32
      ((UInt64.toBitVec 4294977280).ushiftRight ((BitVec.zeroExtend 64
        (BitVec.zeroExtend 32 (UInt8.ofNat n).toBitVec)).toNat % 64))
      ).getLsbD 0 = isSpace (UInt8.ofNat n) := by decide
  simpa using key b.toNat (by omega)

/-- `strtoul` from its entry to `strtoul + 0x44`: it skips the white space
(`ws`) and the sign. -/
theorem strtoul_ws [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = strtoul + 0x44 ∧ ∃ x0 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X3 := ldrbReg (byteAt str (strtoWs str + strtoSign str))
          X4 := s0.regs.X0 + .ofNat (strtoWs str + strtoSign str + 1)
          X5 := 0x100002700
          X7 := s0.regs.X0
          X9 := boolReg (strtoNeg str) }
        status := st })
    ⟨s0, strtoul⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "mov x5, #0x2700" at strtoul
  instr "mov x7, x0" at strtoul + 0x4
  instr "mov x4, x0" at strtoul + 0x8
  instr "movk x5, #0x1, lsl #32" at strtoul + 0xc
  refine loop_rule (measure fun i => str.length + 1 - i).wf
    (fun i s => s.pc = strtoul + 0x10 ∧ i ≤ str.length ∧
      (∀ j (_ : j < i) (hj : j < str.length), isSpace str[j]) ∧
      ∃ x0 x3 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X3 := x3
          X4 := s0.regs.X0 + .ofNat i
          X5 := 0x100002700
          X7 := s0.regs.X0 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), _, _, _, by state_eq⟩ ?_
  rintro i ⟨d', pc⟩ ⟨rfl, hi, hsp, x0, x3, st, rfl⟩
  instr "mov x0, x4" at strtoul + 0x10
  instr "ldrb w3, [x4], #1" at strtoul + 0x14
  load_byte h_mem hw
  instr "cmp w3, #0x20" at strtoul + 0x18
  instr "b.hi 30 <strtoul+0x30>" at strtoul + 0x1c
  · intro hc
    rw [ldrb_cmp_imm_hi_iff] at hc
    simp at hc
    have hil : i < str.length := by
      refine Nat.lt_of_le_of_ne hi fun he => ?_
      simp [he] at hc
    have hws : strtoWs str = i :=
      List.length_takeWhile_eq hi (fun j hj => hsp j hj (by omega))
        (fun h' => Bool.eq_false_iff.mpr fun hs => by
          have := isSpace_le hs
          rw [List.getElem_append_left h'] at hc
          omega)
    instr "cmp w3, #0x2d" at strtoul + 0x30
    instr "b.ne 9c <strtoul+0x9c>" at strtoul + 0x34
    · intro hd
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        beq_eq_false_iff_ne, ne_eq] at hd
      rw [ldrb_cmp_imm_eq_iff'] at hd
      simp at hd
      rw [h_sym]
      instr "cmp w3, #0x2b" at strtoul + 0x9c
      instr "b.ne 28 <strtoul+0x28>" at strtoul + 0xa0
      · intro hp
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq] at hp
        rw [ldrb_cmp_imm_eq_iff'] at hp
        simp at hp
        have hb : byteAt str i ≠ 45 ∧ byteAt str i ≠ 43 := by
          rw [byteAt_eq _ _ (by simp; omega)]
          exact ⟨fun e => hd (by rw [e]; rfl), fun e => hp (by rw [e]; rfl)⟩
        have hsg : strtoSign str = 0 := by simp [strtoSign, hws, hb]
        have hng : strtoNeg str = false := by simp [strtoNeg, hws, hb]
        rw [h_sym]
        instr "mov w9, #0x0" at strtoul + 0x28
        instr "b 44 <strtoul+0x44>" at strtoul + 0x2c
        refine .done _ (.inr ⟨by rw [h_sym], ?x0a, ?sta, ?heqa⟩)
        case heqa =>
        rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
        simp only [boolReg, ldrbReg, Bool.false_eq_true, ite_false,
          Nat.add_zero]
        congr 2 <;> first | rfl | uint64_eq
      · intro hp
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          Bool.not_eq_false] at hp
        rw [ldrb_cmp_imm_eq_iff] at hp
        simp at hp
        have hb : byteAt str i = 43 := by
          rw [byteAt_eq _ _ (by simp; omega)]
          exact UInt8.toNat_inj.mp hp
        have hsg : strtoSign str = 1 := by simp [strtoSign, hws, hb]
        have hng : strtoNeg str = false := by simp [strtoNeg, hws, hb]
        instr "ldrb w3, [x4]" at strtoul + 0xa4
        simp only [ofNat_add_one64]
        load_byte h_mem hw
        instr "add x4, x0, #0x2" at strtoul + 0xa8
        instr "b 28 <strtoul+0x28>" at strtoul + 0xac
        rw [h_sym]
        instr "mov w9, #0x0" at strtoul + 0x28
        instr "b 44 <strtoul+0x44>" at strtoul + 0x2c
        refine .done _ (.inr ⟨by rw [h_sym], ?x0b, ?stb, ?heqb⟩)
        case heqb =>
        rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
        simp only [boolReg, ldrbReg, Bool.false_eq_true, ite_false]
        congr 2 <;> first | rfl | uint64_eq
    · intro hd
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.not_eq_false] at hd
      rw [ldrb_cmp_imm_eq_iff] at hd
      simp at hd
      have hb : byteAt str i = 45 := by
        rw [byteAt_eq _ _ (by simp; omega)]
        exact UInt8.toNat_inj.mp hd
      have hsg : strtoSign str = 1 := by simp [strtoSign, hws, hb]
      have hng : strtoNeg str = true := by simp [strtoNeg, hws, hb]
      instr "ldrb w3, [x4]" at strtoul + 0x38
      simp only [ofNat_add_one64]
      load_byte h_mem hw
      instr "add x4, x0, #0x2" at strtoul + 0x3c
      instr "mov w9, #0x1" at strtoul + 0x40
      refine .done _ (.inr ⟨by dsimp only; bv_decide, ?x0, ?st, ?heq⟩)
      case heq =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, ite_true]
      congr 2 <;> first | rfl | uint64_eq
  · intro hc
    rw [ldrb_cmp_imm_hi_iff] at hc
    simp at hc
    instr "lsr x0, x5, x3" at strtoul + 0x20
    instr "tbnz w0, #0, 10 <strtoul+0x10>" at strtoul + 0x24
    · intro hb
      rw [ws_bit_iff _ (by omega)] at hb
      have hil : i < str.length := by
        refine Nat.lt_of_le_of_ne hi fun he => ?_
        simp [he, isSpace] at hb
      refine .done _ (.inl ⟨i + 1, ?_, by rw [h_sym], hil,
        fun j hj hj' => ?_, ?x0c, ?x3c, ?stc, ?heqc⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hsp j hj hj'
        · rwa [List.getElem_append_left hj'] at hb
      case heqc => state_eq
    · intro hb
      simp only [Bool.not_eq_true] at hb
      rw [ws_bit_iff _ (by omega)] at hb
      have hws : strtoWs str = i :=
        List.length_takeWhile_eq hi (fun j hj => hsp j hj (by omega))
          (fun h' => by rwa [List.getElem_append_left h'] at hb)
      have hb' : byteAt str i ≠ 45 ∧ byteAt str i ≠ 43 := by
        rw [byteAt_eq _ _ (by simp; omega)]
        constructor <;> intro e <;> rw [e] at hc <;> simp at hc
      have hsg : strtoSign str = 0 := by simp [strtoSign, hws, hb']
      have hng : strtoNeg str = false := by simp [strtoNeg, hws, hb']
      instr "mov w9, #0x0" at strtoul + 0x28
      instr "b 44 <strtoul+0x44>" at strtoul + 0x2c
      refine .done _ (.inr ⟨by rw [h_sym], ?x0d, ?std, ?heqd⟩)
      case heqd =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, Bool.false_eq_true, ite_false,
        Nat.add_zero]
      congr 2 <;> first | rfl | uint64_eq

/-- The sign extension (`sext`) of a 32-bit `BitVec.ofNat b` with
`b < 2 ^ 31`. -/
theorem sext_ofNat32 (b : Nat) (hb : b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 b) = BitVec.ofNat 64 b := by
  have h1 : BitVec.ofNat 32 b < 0x80000000#32 := by
    rw [BitVec.lt_def]; simp; omega
  have h2 : BitVec.signExtend 64 (BitVec.ofNat 32 b) =
      BitVec.zeroExtend 64 (BitVec.ofNat 32 b) := by
    generalize BitVec.ofNat 32 b = v at h1 ⊢
    bv_decide
  rw [h2]
  apply BitVec.eq_of_toNat_eq
  simp
  omega

/-- `udiv` (unsigned divide) computes the cutoff `(2 ^ 64 - 1) / b`. -/
theorem udiv_cutoff (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 36) :
    (if (BitVec.ofNat 64 b == 0) = true then (0 : BitVec 64)
      else ~~~((0 &&& 65535#64) <<< 0) / BitVec.ofNat 64 b) =
      BitVec.ofNat 64 ((2 ^ 64 - 1) / b) := by
  have h0 : (BitVec.ofNat 64 b == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp at this
    omega
  rw [h0]
  simp only [Bool.false_eq_true, ite_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  simp
  rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  have := Nat.div_le_self 18446744073709551615 b
  generalize 18446744073709551615 / b = q at this ⊢
  omega

/-- `mvn` (move NOT) and `msub` compute the cut limit (`cutlim`)
`(2 ^ 64 - 1) % b`. -/
theorem mvn_cutlim (b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 36) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 0#64 |||
      ~~~BitVec.extractLsb' 0 32 (BitVec.ofNat 64 ((2 ^ 64 - 1) / b) *
        BitVec.ofNat 64 b + 0#64)) =
      BitVec.ofNat 64 ((2 ^ 64 - 1) % b) := by
  have hd := Nat.div_add_mod (2 ^ 64 - 1) b
  have hr := Nat.mod_lt (2 ^ 64 - 1) (by omega : b > 0)
  generalize (2 ^ 64 - 1) / b = q at hd ⊢
  generalize (2 ^ 64 - 1) % b = r at hd hr ⊢
  have hm : BitVec.ofNat 64 q * BitVec.ofNat 64 b =
      BitVec.ofNat 64 (b * q) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [hm]
  generalize b * q = m at hd
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_not]
  omega

/-- Proves a property of all bytes from the property of `UInt8.ofNat n` for
all `n < 256`, which `decide` can check. -/
theorem UInt8.forall_of_nat {P : UInt8 → Prop}
    (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ c, P c := by
  intro c
  simpa using h c.toNat c.toNat_lt

/-- The value (`val`) of the digit `c` in bases up to 36, or 36 if `c` is
not a digit. -/
def digitVal (c : UInt8) : Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat - 48
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat - 55
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c.toNat - 87
  else 36

/-- The length (`len`) of the digits in base `b` from index `start` of
`str`. -/
def digitsLen (str : List UInt8) (start b : Nat) : Nat :=
  ((str.drop start).takeWhile (fun c => decide (digitVal c < b))).length

/-- The value (`val`) of the first `k` digits in base `b` from index `start`
of `str`. -/
def digitsVal (str : List UInt8) (start b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => digitsVal str start b k * b + digitVal (byteAt str (start + k))

/-- What the registers `x0` and `x6` hold for the accumulated value (`acc`)
`v` after `k` digits: `x6` is 0 before the first digit, 1 after it, and
`0xffffffff` (-1) after an overflow; `x0` is `v` as long as there is no
overflow. -/
def strtoAcc (v k : Nat) (x0 x6 : UInt64) : Prop :=
  (k = 0 ∧ x0 = 0 ∧ x6 = 0) ∨ (0 < k ∧ v < 2 ^ 64 ∧ x0 = .ofNat v ∧ x6 = 1) ∨
    (0 < k ∧ 2 ^ 64 ≤ v ∧ x6 = 0xffffffff)

/-- The invariant (`inv`) of the digit loop of `strtoul` at
`strtoul + 0xe0`, after `k` digits from index `start` of the string at
`nptr`, in the state `d` before the loop. -/
def digitsInv (strtoul : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b k : Nat) (s : MachineState) : Prop :=
  s.pc = strtoul + 0xe0 ∧ start + k ≤ str.length ∧
  (∀ j < k, digitVal (byteAt str (start + j)) < b) ∧
  ∃ x0 x5 x6 st, strtoAcc (digitsVal str start b k) k x0 x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X3 := ldrbReg (byteAt str (start + k))
      X4 := nptr + .ofNat (start + k + 1)
      X5 := x5
      X6 := x6
      X8 := .ofNat ((2 ^ 64 - 1) / b)
      X10 := .ofNat b
      X11 := .ofNat ((2 ^ 64 - 1) % b) }
    status := st }

/-- The state after the digit loop of `strtoul`, at `strtoul + 0x15c`, for
the state `d` before the loop. -/
def digitsPost (strtoul : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (s : MachineState) : Prop :=
  s.pc = strtoul + 0x15c ∧
  ∃ x0 x3 x5 x6 st, strtoAcc (digitsVal str start b (digitsLen str start b))
    (digitsLen str start b) x0 x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X3 := x3
      X4 := nptr + .ofNat (start + digitsLen str start b + 1)
      X5 := x5
      X6 := x6
      X8 := .ofNat ((2 ^ 64 - 1) / b)
      X10 := .ofNat b
      X11 := .ofNat ((2 ^ 64 - 1) % b) }
    status := st }

/-- The condition `ls` (unsigned lower or same) of `cmp`. -/
theorem cmp_ls_eq (a c : BitVec 64) :
    (!((↑(a - c).toNat : Int) == ↑a.toNat - ↑c.toNat) ||
      a - c == BitVec.zero 64) = decide (a.toNat ≤ c.toNat) := by
  by_cases h : a.toNat ≤ c.toNat
  · simp only [h, decide_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, beq_iff_eq, BitVec.zero_eq]
    by_cases h' : a = c
    · exact .inr (by bv_omega)
    · exact .inl (by intro e; apply h'; bv_omega)
  · simp only [h, decide_false, Bool.or_eq_false_iff, Bool.not_eq_false',
      beq_iff_eq, beq_eq_false_iff_ne, BitVec.zero_eq, ne_eq]
    constructor <;> bv_omega

/-- The low 32 bits of a 64-bit `UInt64.ofNat v`. -/
theorem extract_ofNat64 (v : Nat) :
    BitVec.extractLsb' 0 32 (UInt64.ofNat v).toBitVec = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_mod_of_dvd v (by decide : 2 ^ 32 ∣ 2 ^ 64)]

/-- The condition `ge` (signed greater or equal) of `cmp` on small values. -/
theorem cmp_ge_iff (v b : Nat) (hv : v < 37) (hb : b < 37) :
    (BitVec.ofNat 32 v - BitVec.ofNat 32 b).msb =
      ((BitVec.ofNat 32 v - BitVec.ofNat 32 b).toInt !=
        (BitVec.ofNat 32 v).toInt - (BitVec.ofNat 32 b).toInt) ↔ b ≤ v :=
  (by decide +kernel : ∀ v < 37, ∀ b < 37,
    (BitVec.ofNat 32 v - BitVec.ofNat 32 b).msb =
      ((BitVec.ofNat 32 v - BitVec.ofNat 32 b).toInt !=
        (BitVec.ofNat 32 v).toInt - (BitVec.ofNat 32 b).toInt) ↔ b ≤ v)
    v hv b hb

/-- The condition `eq` of `cmp` on 64-bit registers. -/
theorem eq_of_not_sub_ne_zero (x y : BitVec 64)
    (h : ¬(!(x - y == BitVec.zero 64)) = true) : x = y := by
  simp only [BitVec.zero_eq] at h
  bv_decide

/-- The digit loop of `strtoul` from `strtoul + 0x134`, which loads the next
byte and goes back to the loop head. -/
theorem strtoul_next [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64)
    (hacc : strtoAcc (digitsVal str start b (k + 1)) (k + 1) x0 x6)
    (x3 x5 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        digitsInv strtoul d nptr str start b k' s') ∨
      digitsPost strtoul d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoul + 0x134⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "ldrb w3, [x4], #1" at strtoul + 0x134
  load_byte h_mem hw
  instr "b e0 <strtoul+0xe0>" at strtoul + 0x138
  refine .done _ (.inl ⟨k + 1, ?_, by rw [h_sym], by omega, hdig,
    x0, x5, x6, st, hacc, ?heq⟩)
  · simp only [InvImage, WellFoundedRelation.rel]; omega
  case heq =>
  simp only [← Nat.add_assoc, ofNat_add_one64]
  rw [byteAt_eq _ _ (by simp; omega)]
  simp only [ldrbReg]
  congr 2

/-- The condition `gt` (signed greater than) of `cmp` on small values. -/
theorem cmp_gt_iff (v r : Nat) (hv : v < 37) (hr : r < 37) :
    (!(BitVec.ofNat 32 v - BitVec.ofNat 32 r == BitVec.zero 32) &&
      (BitVec.ofNat 32 v - BitVec.ofNat 32 r).msb ==
        ((BitVec.ofNat 32 v - BitVec.ofNat 32 r).toInt !=
          (BitVec.ofNat 32 v).toInt - (BitVec.ofNat 32 r).toInt)) = true ↔
      r < v :=
  (by decide +kernel : ∀ v < 37, ∀ r < 37,
    (!(BitVec.ofNat 32 v - BitVec.ofNat 32 r == BitVec.zero 32) &&
      (BitVec.ofNat 32 v - BitVec.ofNat 32 r).msb ==
        ((BitVec.ofNat 32 v - BitVec.ofNat 32 r).toInt !=
          (BitVec.ofNat 32 v).toInt - (BitVec.ofNat 32 r).toInt)) = true ↔
      r < v)
    v hv r hr

/-- How the accumulator `V` compares with the cutoff `(2 ^ 64 - 1) / b`
decides whether `V * b + v` overflows. -/
theorem cutoff_lt (V v b : Nat) (hv : v < b) (h : V < (2 ^ 64 - 1) / b) :
    V * b + v < 2 ^ 64 := by
  have hd : (2 ^ 64 - 1) / b * b + (2 ^ 64 - 1) % b = 2 ^ 64 - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hm : V * b + b ≤ (2 ^ 64 - 1) / b * b := by
    have := Nat.mul_le_mul_right b (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  generalize (2 ^ 64 - 1) / b * b = qb at hd hm
  omega

theorem cutoff_eq_le (v b : Nat) (h : v ≤ (2 ^ 64 - 1) % b) :
    (2 ^ 64 - 1) / b * b + v < 2 ^ 64 := by
  have hd : (2 ^ 64 - 1) / b * b + (2 ^ 64 - 1) % b = 2 ^ 64 - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  generalize (2 ^ 64 - 1) / b * b = qb at hd ⊢
  generalize (2 ^ 64 - 1) % b = r at hd h
  omega

theorem cutoff_eq_gt (v b : Nat) (h : (2 ^ 64 - 1) % b < v) :
    2 ^ 64 ≤ (2 ^ 64 - 1) / b * b + v := by
  have hd : (2 ^ 64 - 1) / b * b + (2 ^ 64 - 1) % b = 2 ^ 64 - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  generalize (2 ^ 64 - 1) / b * b = qb at hd ⊢
  generalize (2 ^ 64 - 1) % b = r at hd h
  omega

theorem cutoff_gt (V v b : Nat) (hb : 0 < b) (h : (2 ^ 64 - 1) / b < V) :
    2 ^ 64 ≤ V * b + v := by
  have hd : (2 ^ 64 - 1) / b * b + (2 ^ 64 - 1) % b = 2 ^ 64 - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hr := Nat.mod_lt (2 ^ 64 - 1) hb
  have hm : (2 ^ 64 - 1) / b * b + b ≤ V * b := by
    have := Nat.mul_le_mul_right b (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  generalize (2 ^ 64 - 1) / b * b = qb at hd hm
  generalize (2 ^ 64 - 1) % b = r at hd hr
  omega

/-- The digit loop of `strtoul` from `strtoul + 0x154`, after an overflow
(`ovf`). -/
theorem strtoul_ovf [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hov : 2 ^ 64 ≤ digitsVal str start b (k + 1))
    (x0 x3 x5 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        digitsInv strtoul d nptr str start b k' s') ∨
      digitsPost strtoul d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoul + 0x154⟩ := by
  instr "mov w6, #0xffffffff" at strtoul + 0x154
  instr "b 134 <strtoul+0x134>" at strtoul + 0x158
  rw [h_sym]
  exact strtoul_next code strtoul h h_sym d nptr str R h_len start b h_mem k hk
    hdig _ _ (.inr (.inr ⟨Nat.succ_pos _, hov, rfl⟩)) _ _ _

/-- The digit loop of `strtoul` from `strtoul + 0x12c`, which accumulates the
digit with `madd` (multiply-add). -/
theorem strtoul_madd [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hok : digitsVal str start b (k + 1) < 2 ^ 64)
    (x3 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        digitsInv strtoul d nptr str start b k' s') ∨
      digitsPost strtoul d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := .ofNat (digitsVal str start b k)
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := .ofNat (digitVal (byteAt str (start + k)))
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoul + 0x12c⟩ := by
  instr "madd x0, x10, x0, x5" at strtoul + 0x12c
  instr "mov w6, #0x1" at strtoul + 0x130
  have e : (⟨(UInt64.ofNat b).toBitVec *
      (UInt64.ofNat (digitsVal str start b k)).toBitVec +
      (UInt64.ofNat (digitVal (byteAt str (start + k)))).toBitVec⟩ : UInt64)
      = .ofNat (digitsVal str start b (k + 1)) := by
    simp only [digitsVal]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_ofNat']
    rw [Nat.mul_comm]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  rw [e, show strtoul + 304 + 4 = strtoul + 0x134 by bv_decide]
  refine strtoul_next code strtoul h h_sym d nptr str R h_len start b h_mem k
    hk hdig _ _ (.inr (.inl ⟨Nat.succ_pos _, hok, rfl, ?h6⟩)) _ _ _
  case h6 => rfl

/-- The digit loop of `strtoul` stops at a byte that is not a digit in base
`b`. -/
theorem strtoul_stop (strtoul : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (k : Nat)
    (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (hge : b ≤ digitVal (byteAt str (start + k)))
    (x0 x3 x5 x6 : UInt64) (hacc : strtoAcc (digitsVal str start b k) k x0 x6)
    (st : StatusFlags) :
    digitsPost strtoul d nptr str start b ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoul + 0x15c⟩ := by
  have hlen : digitsLen str start b = k := by
    refine List.length_takeWhile_eq (by simp; omega)
      (fun j hj => ?_) (fun hi => ?_)
    · have := hdig j (by simpa using hj)
      rw [byteAt_eq _ _ (by simp; omega),
        List.getElem_append_left (by omega)] at this
      simpa using this
    · rw [byteAt_eq _ _ (by simp; omega),
        List.getElem_append_left (by simp at hi; omega)] at hge
      simpa using hge
  refine ⟨rfl, x0, x3, x5, x6, st, ?_, ?_⟩
  · rwa [hlen]
  · rw [hlen]

/-- One iteration of the digit loop of `strtoul` from `strtoul + 0x108`,
after the digit's value is computed. -/
theorem strtoul_digit [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64) (hacc : strtoAcc (digitsVal str start b k) k x0 x6)
    (x5 : UInt64)
    (hx5 : x5 = .ofNat (digitVal (byteAt str (start + k))))
    (hv : digitVal (byteAt str (start + k)) < 36) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        digitsInv strtoul d nptr str start b k' s') ∨
      digitsPost strtoul d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (start + k))
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoul + 0x108⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  subst hx5
  instr "cmp w5, w2" at strtoul + 0x108
  instr "b.ge 15c <strtoul+0x15c>" at strtoul + 0x10c
  · intro hge
    simp only [h_x2, extract_ofNat64] at hge
    rw [cmp_ge_iff _ _ (by omega) (by omega)] at hge
    rw [h_sym]
    exact .done _ (.inr (strtoul_stop _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc _))
  · intro hge
    simp only [h_x2, extract_ofNat64] at hge
    rw [cmp_ge_iff _ _ (by omega) (by omega), Nat.not_le] at hge
    have hk' : start + k < str.length := by
      refine Nat.lt_of_le_of_ne hk fun he => ?_
      rw [he, byteAt_eq _ _ (by simp)] at hge
      simp [digitVal] at hge
      omega
    have hdig' : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b := by
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hdig j hj
      · exact hge
    have hq : (2 ^ 64 - 1) / b < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    have hr : (2 ^ 64 - 1) % b < b := Nat.mod_lt _ (by omega)
    have hsmall : x6 ≠ 0xffffffff → digitsVal str start b k < 2 ^ 64 ∧
        x0 = .ofNat (digitsVal str start b k) := by
      intro h6
      rcases hacc with ⟨rfl, rfl, -⟩ | ⟨-, hV, rfl, -⟩ | ⟨-, -, h6'⟩
      · exact ⟨by simp [digitsVal], rfl⟩
      · exact ⟨hV, rfl⟩
      · exact absurd h6' h6
    instr "cmp x0, x8" at strtoul + 0x110
    instr "ccmn w6, #0x1, #0x4, ls" at strtoul + 0x114
    simp only [cmp_ls_eq]
    by_cases hls : x0.toBitVec.toNat ≤
        (UInt64.ofNat ((2 ^ 64 - 1) / b)).toBitVec.toNat
    · simp only [hls, decide_true, ↓reduceIte]
      instr "b.eq 154 <strtoul+0x154>" at strtoul + 0x118
      · intro heq
        rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hV, -⟩
        · exact absurd heq (by decide)
        · exact absurd heq (by decide)
        · rw [h_sym]
          refine strtoul_ovf code strtoul h h_sym d nptr str R h_len start b
              h_mem k hk' hdig' ?_ _ _ _ _ _
          show 2 ^ 64 ≤ digitsVal str start b k * b + _
          have := Nat.le_mul_of_pos_right (digitsVal str start b k) hb1
          omega
      · intro heq
        obtain ⟨hV, rfl⟩ := hsmall (by rintro rfl; exact heq (by decide))
        simp only [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hq] at hls
        instr "cmp x0, x8" at strtoul + 0x11c
        instr "b.ne 12c <strtoul+0x12c>" at strtoul + 0x120
        · intro hne
          have hne' : digitsVal str start b k ≠ (2 ^ 64 - 1) / b := by
            intro e; rw [e] at hne; simp at hne
          rw [h_sym]
          exact strtoul_madd code strtoul h h_sym d nptr str R h_len start b
            h_mem k hk' hdig'
            (cutoff_lt _ _ _ hge (by omega)) _ _ _
        · intro hne
          have e : digitsVal str start b k = (2 ^ 64 - 1) / b := by
            have := congrArg BitVec.toNat (show
              (UInt64.ofNat (digitsVal str start b k)).toBitVec =
                (UInt64.ofNat ((2 ^ 64 - 1) / b)).toBitVec by
              exact eq_of_not_sub_ne_zero _ _ hne)
            simpa [Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hq] using this
          instr "cmp w5, w11" at strtoul + 0x124
          instr "b.gt 154 <strtoul+0x154>" at strtoul + 0x128
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [h_sym]
            refine strtoul_ovf code strtoul h h_sym d nptr str R h_len start b
                h_mem k hk' hdig' ?_ _ _ _ _ _
            show 2 ^ 64 ≤ digitsVal str start b k * b + _
            rw [e]
            exact cutoff_eq_gt _ _ hgt
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [show strtoul + 296 + 4 = strtoul + 0x12c by bv_decide]
            refine strtoul_madd code strtoul h h_sym d nptr str R h_len start b
                h_mem k hk' hdig' ?_ _ _ _
            show digitsVal str start b k * b + _ < 2 ^ 64
            rw [e]
            exact cutoff_eq_le _ _ (by omega)
    · simp only [hls, decide_false, Bool.false_eq_true, ↓reduceIte]
      instr "b.eq 154 <strtoul+0x154>" at strtoul + 0x118
      · intro heq
        rw [h_sym]
        refine strtoul_ovf code strtoul h h_sym d nptr str R h_len start b
            h_mem k hk' hdig' ?_ _ _ _ _ _
        show 2 ^ 64 ≤ digitsVal str start b k * b + _
        by_cases h6 : x6 = 0xffffffff
        · rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hV, -⟩
          · exact absurd h6 (by decide)
          · exact absurd h6 (by decide)
          · have := Nat.le_mul_of_pos_right (digitsVal str start b k) hb1
            omega
        · obtain ⟨hV, rfl⟩ := hsmall h6
          simp only [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hq] at hls
          exact cutoff_gt _ _ _ (by omega) (by omega)
      · intro heq
        exact absurd (by decide) heq

/-- The digit loop of `strtoul`, from `strtoul + 0xc4` to `strtoul + 0x15c`.
-/
theorem strtoul_digits [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (h_start : start ≤ str.length) (hb1 : 1 ≤ b) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_x3 : d.regs.X3 = ldrbReg (byteAt str start))
    (h_x4 : d.regs.X4 = nptr + .ofNat (start + 1))
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R) :
    Eventually code.stepWp (digitsPost strtoul d nptr str start b)
    ⟨d, strtoul + 0xc4⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "sxtw x10, w2" at strtoul + 0xc4
  instr "mov x8, #0xffffffffffffffff" at strtoul + 0xc8
  instr "mov w6, #0x0" at strtoul + 0xcc
  instr "mov x0, #0x0" at strtoul + 0xd0
  instr "udiv x8, x8, x10" at strtoul + 0xd4
  instr "mul x11, x8, x10" at strtoul + 0xd8
  instr "mvn w11, w11" at strtoul + 0xdc
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, ge_iff_le,
    Nat.zero_le, ↓reduceIte, BitVec.ushiftRight_zero, h_x2,
    sext_ofNat32 b (by omega), udiv_cutoff b hb1 hb, mvn_cutlim b hb1 hb]
  refine loop_rule (measure fun k => str.length + 1 - k).wf
    (digitsInv strtoul d nptr str start b) _
    0 _ ⟨by dsimp only; bv_decide, by omega, fun _ h => absurd h
      (Nat.not_lt_zero _),
      ?x0i, ?x5i, ?x6i, ?sti, ?acci, ?eqi⟩ ?_
  case eqi =>
    rw [Nat.add_zero, ← h_x3, ← h_x4]
    state_eq
  case acci => exact .inl ⟨rfl, rfl, by decide⟩
  rintro k ⟨d', pc⟩ ⟨rfl, hk, hdig, x0, x5, x6, st, hacc, rfl⟩
  instr "sub w5, w3, #0x30" at strtoul + 0xe0
  instr "and x5, x5, #0xff" at strtoul + 0xe4
  instr "cmp w5, #0x9" at strtoul + 0xe8
  instr "b.ls 108 <strtoul+0x108>" at strtoul + 0xec
  · intro hA
    rw [h_sym]
    refine strtoul_digit code strtoul h h_sym d nptr str R h_len start b hb1 hb
        h_x2 h_mem k hk hdig x0 x6 hacc _ ?hxA ?hvA _
    case hxA =>
      revert hA
      generalize byteAt str (start + k) = c
      revert c
      apply UInt8.forall_of_nat
      simp only [ldrbReg, digitVal]
      decide +kernel
    case hvA =>
      revert hA
      generalize byteAt str (start + k) = c
      revert c
      apply UInt8.forall_of_nat
      simp only [ldrbReg, digitVal]
      decide +kernel
  · intro hA
    instr "sub w5, w3, #0x41" at strtoul + 0xf0
    instr "and w5, w5, #0xff" at strtoul + 0xf4
    instr "cmp w5, #0x19" at strtoul + 0xf8
    instr "b.hi 13c <strtoul+0x13c>" at strtoul + 0xfc
    · intro hB
      rw [h_sym]
      instr "sub w5, w3, #0x61" at strtoul + 0x13c
      instr "and w5, w5, #0xff" at strtoul + 0x140
      instr "cmp w5, #0x19" at strtoul + 0x144
      instr "b.hi 15c <strtoul+0x15c>" at strtoul + 0x148
      · intro hC
        have hge : b ≤ digitVal (byteAt str (start + k)) := by
          have : digitVal (byteAt str (start + k)) = 36 := by
            revert hA hB hC
            generalize byteAt str (start + k) = c
            revert c
            apply UInt8.forall_of_nat
            simp only [ldrbReg, digitVal]
            decide +kernel
          omega
        rw [h_sym]
        exact .done _
          (.inr (strtoul_stop _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc _))
      · intro hC
        instr "sub w5, w3, #0x57" at strtoul + 0x14c
        instr "b 104 <strtoul+0x104>" at strtoul + 0x150
        rw [h_sym]
        instr "and x5, x5, #0xff" at strtoul + 0x104
        rw [show strtoul + 260 + 4 = strtoul + 0x108 by bv_decide]
        refine strtoul_digit code strtoul h h_sym d nptr str R h_len start b
            hb1 hb h_x2 h_mem k hk hdig x0 x6 hacc _ ?hxC ?hvC _
        case hxC =>
              revert hA hB hC
              generalize byteAt str (start + k) = c
              revert c
              apply UInt8.forall_of_nat
              simp only [ldrbReg, digitVal]
              decide +kernel
        case hvC =>
              revert hA hB hC
              generalize byteAt str (start + k) = c
              revert c
              apply UInt8.forall_of_nat
              simp only [ldrbReg, digitVal]
              decide +kernel
    · intro hB
      instr "sub w5, w3, #0x37" at strtoul + 0x100
      instr "and x5, x5, #0xff" at strtoul + 0x104
      rw [show strtoul + 260 + 4 = strtoul + 0x108 by bv_decide]
      refine strtoul_digit code strtoul h h_sym d nptr str R h_len start b hb1
          hb h_x2 h_mem k hk hdig x0 x6 hacc _ ?hxB ?hvB _
      case hxB =>
            revert hA hB
            generalize byteAt str (start + k) = c
            revert c
            apply UInt8.forall_of_nat
            simp only [ldrbReg, digitVal]
            decide +kernel
      case hvB =>
            revert hA hB
            generalize byteAt str (start + k) = c
            revert c
            apply UInt8.forall_of_nat
            simp only [ldrbReg, digitVal]
            decide +kernel

/-- A nonzero byte is inside the string. -/
theorem lt_of_byteAt_ne_zero {str : List UInt8} {k : Nat}
    (h : byteAt str k ≠ 0) : k < str.length := by
  refine Nat.lt_of_not_le fun hk => h ?_
  unfold byteAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hk]
  rcases Nat.eq_zero_or_pos (k - str.length) with e | e
  · simp [e]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

/-- The position (`pos`) of the number in `str`, after the white space and
the sign. -/
def strtoPos (str : List UInt8) : Nat := strtoWs str + strtoSign str

/-- Whether `c` is a hexadecimal digit. -/
def isHexDigit (c : UInt8) : Bool := digitVal c < 16

/-- Whether `strtoul` skips a `0x` or `0X` prefix (`hex`): only for the base
0 or 16, and only if a hexadecimal digit follows. -/
def strtoHex (str : List UInt8) (base : Nat) : Bool :=
  (base == 0 || base == 16) && byteAt str (strtoPos str) == 48 &&
  (byteAt str (strtoPos str + 1) == 88 ||
    byteAt str (strtoPos str + 1) == 120) &&
  isHexDigit (byteAt str (strtoPos str + 2))

/-- The index of the first digit in `str`. -/
def strtoStart (str : List UInt8) (base : Nat) : Nat :=
  if strtoHex str base then strtoPos str + 2 else strtoPos str

/-- The base that `strtoul` uses when there is no `0x` prefix: `base`, or 8 or
10 if `base` is 0, depending on whether the number starts with `0`. -/
def strtoBaseNoHex (str : List UInt8) (base : Nat) : Nat :=
  if base = 0 then (if byteAt str (strtoPos str) = 48 then 8 else 10)
  else base

/-- The base that `strtoul` uses. -/
def strtoBase (str : List UInt8) (base : Nat) : Nat :=
  if strtoHex str base then 16 else strtoBaseNoHex str base

/-- The state of `strtoul` at `strtoul + 0xc4`, after the prefix (white
space, sign and `0x`), when the digits start at index `start` and the base
is `b`. -/
def prefixPost (strtoul : Int64) (s0 : MachineData) (str : List UInt8)
    (start b : Nat) (s : MachineState) : Prop :=
  s.pc = strtoul + 0xc4 ∧ ∃ x0 x2 x5 x6 st,
  x2.toBitVec.extractLsb' 0 32 = .ofNat 32 b ∧
  s.data = { s0 with
    regs := { s0.regs with
      X0 := x0
      X2 := x2
      X3 := ldrbReg (byteAt str start)
      X4 := s0.regs.X0 + .ofNat (start + 1)
      X5 := x5
      X6 := x6
      X7 := s0.regs.X0
      X9 := boolReg (strtoNeg str) }
    status := st }

/-- `csel` (conditional select) picks the base 10 if there is no leading
`0`. -/
theorem csel_base (c : UInt8) (hc : ¬c = 48) :
    BitVec.extractLsb' 0 32
        (BitVec.zeroExtend 64
          (if (!BitVec.extractLsb' 0 32 (ldrbReg c).toBitVec -
                BitVec.ofInt 32 (BitVec.toInt (48 : BitVec 64)) ==
                BitVec.zero 32) = true
          then BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
            ((BitVec.ofInt 32 (BitVec.toInt (10 : BitVec 64)) &&& 65535#32) <<<
                0))
          else BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
            ((BitVec.ofInt 32 (BitVec.toInt (8 : BitVec 64)) &&& 65535#32)
              <<< 0)))) = 10#32 := by
  revert c
  apply UInt8.forall_of_nat
  simp only [ldrbReg]
  decide +kernel

/-- `strtoul` from `strtoul + 0xb0`, which picks the base if there is no
`0x` prefix and the base is 0 (`b0`) or 16. -/
theorem strtoul_b0 [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str : List UInt8)
    (base : Nat) (hbase : base = 0 ∨ base = 16)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 x5 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (prefixPost strtoul s0 str (strtoPos str)
      (strtoBaseNoHex str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (strtoPos str))
        X4 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X5 := x5
        X6 := x6
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoul + 0xb0⟩ := by
  instr "cbnz w2, 94 <strtoul+0x94>" at strtoul + 0xb0
  · intro hnz
    rw [h_x2] at hnz
    have h16 : base = 16 := by
      rcases hbase with rfl | rfl
      · exact absurd rfl hnz
      · rfl
    subst h16
    rw [h_sym]
    instr "mov w2, #0x10" at strtoul + 0x94
    instr "b c4 <strtoul+0xc4>" at strtoul + 0x98
    refine .done _ ⟨by rw [h_sym], x0, ?x2a, x5, x6, st, ?ext1, ?eq1⟩
    case eq1 => state_eq
    case ext1 => simp [strtoBaseNoHex]
  · intro hz
    rw [h_x2] at hz
    have h0 : base = 0 := by
      rcases hbase with rfl | rfl
      · rfl
      · exact absurd hz (by decide)
    subst h0
    instr "cmp w3, #0x30" at strtoul + 0xb4
    instr "mov w2, #0xa" at strtoul + 0xb8
    instr "mov w0, #0x8" at strtoul + 0xbc
    instr "csel w2, w2, w0, ne" at strtoul + 0xc0
    refine .done _ ⟨by dsimp only; bv_decide, ?x0b, ?x2b, x5, x6, ?stb, ?ext2,
      ?eq2⟩
    case eq2 => state_eq
    case ext2 =>
      simp only [strtoBaseNoHex, ↓reduceIte]
      by_cases hc : byteAt str (strtoPos str) = 48
      · simp only [hc, ↓reduceIte]
        rfl
      · simp only [hc, ↓reduceIte]
        exact csel_base _ hc

/-- `tst` (test bits) checks whether the base is 0 or 16. -/
theorem tst_base : ∀ base < 37,
    ¬(!(BitVec.ofNat 32 base &&&
      BitVec.ofInt 32 (BitVec.toInt (4294967279 : BitVec 64)) ==
        BitVec.zero 32)) = true ↔ base = 0 ∨ base = 16 := by
  decide +kernel

/-- `strtoul` from `strtoul + 0x8c`, which skips a `0x` prefix (`hex`) that
starts at index `P`. -/
theorem strtoul_hex [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str : List UInt8) (P : Nat)
    (x0 x3 x5 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (prefixPost strtoul s0 str (P + 2) 16)
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := x3
        X4 := s0.regs.X0 + .ofNat (P + 1)
        X5 := x5
        X6 := ldrbReg (byteAt str (P + 2))
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoul + 0x8c⟩ := by
  instr "add x4, x4, #0x2" at strtoul + 0x8c
  instr "mov w3, w6" at strtoul + 0x90
  instr "mov w2, #0x10" at strtoul + 0x94
  instr "b c4 <strtoul+0xc4>" at strtoul + 0x98
  refine .done _ ⟨by rw [h_sym], x0, ?x2h, x5, ?x6h, st, ?exth, ?eqh⟩
  case eqh =>
    simp only [ldrbReg]
    congr 2 <;> first | rfl | uint64_eq
  case exth => rfl

/-- `strtoul` from `strtoul + 0x44` to `strtoul + 0xc4`, through the prefix
(the `0x` and the choice of the base). -/
theorem strtoul_prefix [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R)
    (base : Nat) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (prefixPost strtoul s0 str (strtoStart str base)
      (strtoBase str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (strtoPos str))
        X4 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X5 := 0x100002700
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoul + 0x44⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "tst w2, #0xffffffef" at strtoul + 0x44
  instr "b.ne c4 <strtoul+0xc4>" at strtoul + 0x48
  · intro hne
    simp only [h_x2] at hne
    have hbase : ¬(base = 0 ∨ base = 16) := by
      rw [← tst_base base (by omega)]
      simpa using hne
    have hnh : strtoHex str base = false := by
      simp only [strtoHex]
      rcases Nat.lt_or_ge base 37 with _ | _ <;>
        simp_all
    rw [strtoStart, strtoBase, hnh]
    simp only [Bool.false_eq_true, ↓reduceIte, strtoBaseNoHex]
    have hb0 : base ≠ 0 := fun e => hbase (.inl e)
    simp only [hb0, ↓reduceIte]
    rw [h_sym]
    refine .done _ ⟨rfl, x0, ?x2p, ?x5p, ?x6p, ?stp, ?extp, ?eqp⟩
    case eqp => rfl
    case extp => exact h_x2
  · intro hne
    simp only [h_x2] at hne
    have hbase : base = 0 ∨ base = 16 := (tst_base base (by omega)).mp hne
    instr "cmp w3, #0x30" at strtoul + 0x4c
    instr "b.ne b0 <strtoul+0xb0>" at strtoul + 0x50
    · intro h0
      have hb0 : byteAt str (strtoPos str) ≠ 48 := by
        revert h0
        generalize byteAt str (strtoPos str) = c
        revert c
        apply UInt8.forall_of_nat
        simp only [ldrbReg]
        decide +kernel
      have hnh : strtoHex str base = false := by simp [strtoHex, hb0]
      rw [strtoStart, strtoBase, hnh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h_sym]
      exact strtoul_b0 code strtoul h h_sym s0 str base hbase h_x2 _ _ _ _
    · intro h0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.not_eq_false] at h0
      rw [ldrbReg, ldrb_cmp_imm_eq_iff] at h0
      simp at h0
      have hb0 : byteAt str (strtoPos str) = 48 := UInt8.toNat_inj.mp h0
      have hp0 := lt_of_byteAt_ne_zero (by rw [hb0]; decide)
      instr "ldrb w0, [x4]" at strtoul + 0x54
      load_byte h_mem hw
      instr "and w0, w0, #0xffffffdf" at strtoul + 0x58
      instr "and w0, w0, #0xff" at strtoul + 0x5c
      instr "cmp w0, #0x58" at strtoul + 0x60
      instr "b.ne b0 <strtoul+0xb0>" at strtoul + 0x64
      · intro hx
        rw [← byteAt_eq _ _ (by simp; omega)] at hx
        have hb1 : byteAt str (strtoPos str + 1) ≠ 88 ∧
            byteAt str (strtoPos str + 1) ≠ 120 := by
          revert hx
          generalize byteAt str (strtoPos str + 1) = c
          revert c
          apply UInt8.forall_of_nat
          decide +kernel
        have hnh : strtoHex str base = false := by simp [strtoHex, hb1]
        rw [strtoStart, strtoBase, hnh]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h_sym]
        exact strtoul_b0 code strtoul h h_sym s0 str base hbase h_x2 _ _ _ _
      · intro hx
        have hb1 : byteAt str (strtoPos str + 1) = 88 ∨
            byteAt str (strtoPos str + 1) = 120 := by
          rw [← byteAt_eq _ _ (by simp; omega)] at hx
          revert hx
          generalize byteAt str (strtoPos str + 1) = c
          revert c
          apply UInt8.forall_of_nat
          decide +kernel
        have hp1 := lt_of_byteAt_ne_zero
          (by rcases hb1 with e | e <;> rw [e] <;> decide)
        instr "ldrb w6, [x4, #1]" at strtoul + 0x68
        simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat',
          BitVec.add_assoc,
          ofNat_add_one64]
        load_byte h_mem hw
        instr "sub w0, w6, #0x30" at strtoul + 0x6c
        instr "and w0, w0, #0xff" at strtoul + 0x70
        instr "cmp w0, #0x36" at strtoul + 0x74
        instr "b.hi b0 <strtoul+0xb0>" at strtoul + 0x78
        · intro hhi
          rw [← byteAt_eq _ _ (by simp; omega)] at hhi
          have hd : isHexDigit (byteAt str (strtoPos str + 2)) = false := by
            revert hhi
            generalize byteAt str (strtoPos str + 2) = c
            revert c
            apply UInt8.forall_of_nat
            simp only [isHexDigit, digitVal]
            decide +kernel
          have hnh : strtoHex str base = false := by simp [strtoHex, hd]
          rw [strtoStart, strtoBase, hnh]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [h_sym]
          exact strtoul_b0 code strtoul h h_sym s0 str base hbase h_x2 _ _ _ _
        · intro hhi
          instr "mov x5, #0x7e0000007e0000" at strtoul + 0x7c
          instr "movk x5, #0x3ff" at strtoul + 0x80
          instr "lsr x0, x5, x0" at strtoul + 0x84
          instr "tbz w0, #0, b0 <strtoul+0xb0>" at strtoul + 0x88
          · intro hbit
            rw [← byteAt_eq _ _ (by simp; omega)] at hhi hbit
            have hd : isHexDigit (byteAt str (strtoPos str + 2)) = false := by
              revert hhi hbit
              generalize byteAt str (strtoPos str + 2) = c
              revert c
              apply UInt8.forall_of_nat
              simp only [isHexDigit, digitVal]
              decide +kernel
            have hnh : strtoHex str base = false := by simp [strtoHex, hd]
            rw [strtoStart, strtoBase, hnh]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [h_sym]
            exact strtoul_b0 code strtoul h h_sym s0 str base hbase h_x2 _ _ _ _
          · intro hbit
            have e2 := byteAt_eq str (strtoPos str + 2) (by simp; omega)
            have hd : isHexDigit (byteAt str (strtoPos str + 2)) = true := by
              rw [← e2] at hhi hbit
              revert hhi hbit
              generalize byteAt str (strtoPos str + 2) = c
              revert c
              apply UInt8.forall_of_nat
              simp only [isHexDigit, digitVal]
              decide +kernel
            have hhex : strtoHex str base = true := by
              simp only [strtoHex, hb0, hd]
              rcases hbase with rfl | rfl <;> rcases hb1 with e | e <;>
                simp [e]
            rw [strtoStart, strtoBase, hhex]
            simp only [↓reduceIte]
            rw [← e2, show strtoul + 136 + 4 = strtoul + 0x8c by bv_decide]
            exact strtoul_hex code strtoul h h_sym s0 str _ _ _ _ _

/-- The value that `strtoul` returns for the accumulated value `V` of the
digits and the sign `neg`. -/
def strtoRet (V : Nat) (neg : Bool) : UInt64 :=
  if 2 ^ 64 ≤ V then -1 else if neg then -(.ofNat V) else .ofNat V

/-- The pointer that `strtoul` stores to `*endptr`: `nptr` if there are no
digits (`n = 0`), else `q`, the pointer after the digits. -/
def strtoEnd (n : Nat) (nptr q : UInt64) : UInt64 := if n = 0 then nptr else q

/-- The state after the epilogue (`epi`) of `strtoul`, after `ret`, for the
state `d` at the start of the epilogue: `x0` is `r`, and if `endptr`
(`x1`) is not NULL, `*endptr` is `e` in the frame `R`. -/
def epiPost (d : MachineData) (r e : UInt64) (R : DataMem → Prop)
    (s : MachineState) : Prop :=
  s.pc = d.regs.X30.toInt64 ∧ ∃ x7 st m,
  s.data = { d with
    regs := { d.regs with X0 := r, X7 := x7 }
    status := st
    dmem := m } ∧
  (d.regs.X1 = 0 ∧ m = d.dmem ∨
    d.regs.X1 ≠ 0 ∧ m =⋆ Eq (e.toBytes.At d.regs.X1.toBitVec) ⋆ R)

/-- `strtoul` from `strtoul + 0x178`, which stores `x7` to `*endptr` and
returns. -/
theorem strtoul_str [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o) (d : MachineData)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ m, s.data = { d with dmem := m } ∧
      m =⋆ Eq (d.regs.X7.toBytes.At d.regs.X1.toBitVec) ⋆ R)
    ⟨d, strtoul + 0x178⟩ := by
  instr "str x7, [x1]" at strtoul + 0x178
  simp (disch := first | rfl | simp [h_old]) only
    [MachineData.store_of_sep64_zero h_mem, Effects.All, MemWidth.bytes]
  have hL := Mem.storeInt_sep _ 8 _ _ _ ⟨h_mem, h_old⟩
    d.regs.X7.toBitVec.toInt
  rw [show Int.toBytes 8 d.regs.X7.toBitVec.toInt = d.regs.X7.toBytes
    from rfl] at hL
  instr "ret" at strtoul + 0x17c
  exact .done _ ⟨rfl, _, rfl, hL⟩

/-- `epiPost` holds for any state with the same registers except `x0`. -/
theorem epiPost_of {d d' : MachineData} {r e : UInt64}
    {R : DataMem → Prop} {s : MachineState}
    (hd : ∃ a, d'.regs = { d.regs with X0 := a }) (hm : d'.dmem = d.dmem)
    (h : epiPost d' r e R s) : epiPost d r e R s := by
  obtain ⟨a, ha⟩ := hd
  rcases d' with ⟨regs', st', dm'⟩
  simp only at ha hm
  subst ha hm
  exact h

/-- `strtoul` from `strtoul + 0x174`, which stores the pointer after the
digits to `*endptr` and returns. -/
theorem strtoul_174 [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o) (d : MachineData) (q : UInt64)
    (h_x4 : d.regs.X4 = q + 1) (hX1 : d.regs.X1 ≠ 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (epiPost d d.regs.X0 q R)
      ⟨d, strtoul + 0x174⟩ := by
  instr "sub x7, x4, #0x1" at strtoul + 0x174
  rw [show strtoul + 372 + 4 = strtoul + 0x178 by bv_decide]
  refine eventually_weaken _ _ _ _ ?_
    (strtoul_str code strtoul h _ old R h_old h_mem)
  rintro s ⟨hpc, m, hs, hm⟩
  refine ⟨hpc, ⟨d.regs.X4.toBitVec - 1⟩, d.status, m, hs.trans rfl,
    .inr ⟨hX1, ?_⟩⟩
  have hq : (⟨d.regs.X4.toBitVec - 1⟩ : UInt64) = q := by
    rw [h_x4]; apply UInt64.toBitVec_inj.mp; simp [BitVec.add_sub_cancel]
  rw [← hq]
  exact hm

/-- `strtoul` from `strtoul + 0x16c`, which stores to `*endptr` if it is not
NULL and returns. -/
theorem strtoul_16c [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul) (d : MachineData) (n : Nat)
    (q : UInt64) (h_x4 : d.regs.X4 = q + 1)
    (h_w6 : BitVec.extractLsb' 0 32 d.regs.X6.toBitVec = 0 ↔ n = 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (epiPost d d.regs.X0 (strtoEnd n d.regs.X7 q) R)
      ⟨d, strtoul + 0x16c⟩ := by
  instr "cbz x1, 17c <strtoul+0x17c>" at strtoul + 0x16c
  · intro hz
    rw [h_sym]
    instr "ret" at strtoul + 0x17c
    exact .done _ ⟨rfl, d.regs.X7, d.status, d.dmem, rfl,
      .inl ⟨by simpa [← UInt64.toBitVec_inj] using hz, rfl⟩⟩
  · intro hz
    have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
    instr "cbz w6, 178 <strtoul+0x178>" at strtoul + 0x170
    · intro h6
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtoul_str code strtoul h d old R h_old (h_mem hX1))
      rintro s ⟨hpc, m, hs, hm⟩
      refine ⟨hpc, d.regs.X7, d.status, m, hs.trans rfl, .inr ⟨hX1, ?_⟩⟩
      simp only [strtoEnd, h_w6.mp h6, ↓reduceIte]
      exact hm
    · intro h6
      have hn : ¬n = 0 := fun h0 => h6 (h_w6.mpr h0)
      simp only [strtoEnd, hn, ↓reduceIte]
      rw [show strtoul + 368 + 4 = strtoul + 0x174 by bv_decide]
      exact strtoul_174 code strtoul h d q h_x4 hX1 old R h_old (h_mem hX1)

/-- The epilogue (`epi`) of `strtoul`, from `strtoul + 0x15c`, after `n`
digits with the value `V`, where `q` is the pointer after the digits. -/
theorem strtoul_epi [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (d : MachineData) (neg : Bool) (V n : Nat) (q x0 x6 : UInt64)
    (hacc : strtoAcc V n x0 x6) (hV0 : n = 0 → V = 0)
    (h_x0 : d.regs.X0 = x0) (h_x4 : d.regs.X4 = q + 1)
    (h_x6 : d.regs.X6 = x6) (h_x9 : d.regs.X9 = boolReg neg)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (epiPost d (strtoRet V neg) (strtoEnd n d.regs.X7 q) R)
      ⟨d, strtoul + 0x15c⟩ := by
  instr "cmn w6, #0x1" at strtoul + 0x15c
  instr "b.eq 180 <strtoul+0x180>" at strtoul + 0x160
  · intro heq
    rw [h_x6] at heq
    rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨hk, hv, rfl⟩
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    have hret : strtoRet V neg = ⟨~~~((0 &&& 65535#64) <<< 0)⟩ := by
      simp only [strtoRet, hv, ↓reduceIte]; decide
    have hend : strtoEnd n d.regs.X7 q = q := by
      simp only [strtoEnd, show ¬n = 0 by omega, ↓reduceIte]
    rw [hret, hend, h_sym]
    instr "mov x0, #0xffffffffffffffff" at strtoul + 0x180
    instr "cbnz x1, 174 <strtoul+0x174>" at strtoul + 0x184
    · intro hz
      have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtoul_174 code strtoul h _ q (by exact h_x4) (by exact hX1) old R
          h_old (by exact h_mem hX1))
      exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs
    · intro hz
      instr "b 17c <strtoul+0x17c>" at strtoul + 0x188
      rw [h_sym]
      instr "ret" at strtoul + 0x17c
      exact .done _ ⟨rfl, d.regs.X7, _, d.dmem, rfl,
        .inl ⟨by simpa [← UInt64.toBitVec_inj] using hz, rfl⟩⟩
  · intro heq
    rw [h_x6] at heq
    have hacc' : n = 0 ∧ x0 = 0 ∧ x6 = 0 ∨
        0 < n ∧ V < 2 ^ 64 ∧ x0 = .ofNat V ∧ x6 = 1 := by
      rcases hacc with h1 | h2 | ⟨-, -, rfl⟩
      · exact .inl h1
      · exact .inr h2
      · exact absurd heq (by decide)
    have hret : strtoRet V neg = if neg then -x0 else x0 := by
      rcases hacc' with ⟨h0, rfl, -⟩ | ⟨-, hv, rfl, -⟩
      · cases hV0 h0; cases neg <;> simp [strtoRet]
      · simp [strtoRet, show ¬2 ^ 64 ≤ V by omega]
    have h_w6 : BitVec.extractLsb' 0 32 d.regs.X6.toBitVec = 0 ↔ n = 0 := by
      rw [h_x6]
      rcases hacc' with ⟨h0, -, rfl⟩ | ⟨hk, -, -, rfl⟩
      · simp only [h0, iff_true]; decide
      · simp only [show ¬n = 0 by omega, iff_false]; decide
    rw [hret, ← h_x0]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      instr "cbz w9, 16c <strtoul+0x16c>" at strtoul + 0x164
      · intro hz
        rw [h_sym]
        refine eventually_weaken _ _ _ _ ?_
          (strtoul_16c code strtoul h h_sym _ n q (by exact h_x4)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
    · simp only [↓reduceIte]
      instr "cbz w9, 16c <strtoul+0x16c>" at strtoul + 0x164
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
      · intro hz
        instr "neg x0, x0" at strtoul + 0x168
        rw [show strtoul + 360 + 4 = strtoul + 0x16c by bv_decide,
          show -d.regs.X0 = ⟨0#64 - d.regs.X0.toBitVec⟩ from
            UInt64.toBitVec_inj.mp (by simp)]
        refine eventually_weaken _ _ _ _ ?_
          (strtoul_16c code strtoul h h_sym _ n q (by exact h_x4)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs

/-- The number starts inside the string. -/
theorem strtoPos_le (str : List UInt8) : strtoPos str ≤ str.length := by
  unfold strtoPos strtoSign
  split
  · rename_i hs
    have : byteAt str (strtoWs str) ≠ 0 := by
      intro h0; simp [h0] at hs
    have := lt_of_byteAt_ne_zero this
    omega
  · simp only [Nat.add_zero, strtoWs]
    exact (List.takeWhile_prefix _).length_le

/-- The digits start inside the string. -/
theorem strtoStart_le (str : List UInt8) (base : Nat) :
    strtoStart str base ≤ str.length := by
  unfold strtoStart
  split
  · rename_i hh
    simp only [strtoHex, isHexDigit, Bool.and_eq_true, decide_eq_true_eq]
      at hh
    have : byteAt str (strtoPos str + 2) ≠ 0 := by
      intro h0; rw [h0] at hh; exact absurd hh.2 (by decide)
    have := lt_of_byteAt_ne_zero this
    omega
  · exact strtoPos_le str

/-- The base that `strtoul` uses is between 1 and 36. -/
theorem strtoBase_range (str : List UInt8) (base : Nat) (hb : base ≤ 36) :
    1 ≤ strtoBase str base ∧ strtoBase str base ≤ 36 := by
  unfold strtoBase strtoBaseNoHex
  split <;> (try split) <;> (try split) <;> omega

/-- The number of digits that `strtoul` converts. -/
def strtoDigits (str : List UInt8) (base : Nat) : Nat :=
  digitsLen str (strtoStart str base) (strtoBase str base)

/-- The value (`val`) that `strtoul` returns for the string `str` and the
base `base`: the value of the digits, negated if there is a `-`, or
`ULONG_MAX` if that overflows. -/
def strtoulVal (str : List UInt8) (base : Nat) : UInt64 :=
  strtoRet (digitsVal str (strtoStart str base) (strtoBase str base)
    (strtoDigits str base)) (strtoNeg str)

/-- The offset (`ofs`) from `nptr` of the pointer that `strtoul` stores to
`*endptr`: after the digits, or 0 if there are none. -/
def strtoEndOfs (str : List UInt8) (base : Nat) : Nat :=
  if strtoDigits str base = 0 then 0
  else strtoStart str base + strtoDigits str base

/-- `strtoul` for both a NULL and a non-NULL `endptr` (general, `gen`). -/
theorem strtoul_gen [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str old : List UInt8) (base : Nat)
    (R R' : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_old : old.length = 8)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R)
    (h_end : s0.regs.X1 ≠ 0 →
      s0.dmem =⋆ Eq (old.At s0.regs.X1.toBitVec) ⋆ R') :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11 }
        status := st
        dmem := m } ∧
      (s0.regs.X1 = 0 ∧ m = s0.dmem ∨ s0.regs.X1 ≠ 0 ∧
        m =⋆ Eq ((s0.regs.X0 + .ofNat (strtoEndOfs str base)).toBytes.At
          s0.regs.X1.toBitVec) ⋆ R'))
    ⟨s0, strtoul⟩ := by
  obtain ⟨hb1, hb36⟩ := strtoBase_range str base h_base
  refine eventually_trans _ _ _ _
    (strtoul_ws code strtoul h h_sym s0 str R h_len h_mem) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, st, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtoul_prefix code strtoul h h_sym s0 str
    R h_len h_mem base h_base h_x2 x0 st) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, x2, x5, x6, st, hx2, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtoul_digits code strtoul h h_sym _
    s0.regs.X0 str R h_len _ _ (strtoStart_le str base) hb1 hb36 hx2 rfl rfl
    h_mem) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, x3, x5, x6, st, hacc, hs⟩
  simp only at hpc hs
  subst hpc hs
  have hx4 : s0.regs.X0 + .ofNat (strtoStart str base +
        digitsLen str (strtoStart str base) (strtoBase str base) + 1) =
      s0.regs.X0 + .ofNat (strtoStart str base +
        digitsLen str (strtoStart str base) (strtoBase str base)) + 1 := by
    apply UInt64.toBitVec_inj.mp
    simp [UInt64.toBitVec_add, BitVec.add_assoc]
  have hE : strtoEnd (digitsLen str (strtoStart str base) (strtoBase str base))
      s0.regs.X0 (s0.regs.X0 + .ofNat (strtoStart str base +
        digitsLen str (strtoStart str base) (strtoBase str base))) =
      s0.regs.X0 + .ofNat (strtoEndOfs str base) := by
    unfold strtoEnd strtoEndOfs strtoDigits
    split <;> simp_all
  refine eventually_weaken _ _ _ _ ?_ (strtoul_epi code strtoul h h_sym _
    (strtoNeg str) _ _ _ x0 x6 hacc (fun h0 => by rw [h0]; rfl) rfl
    (by exact hx4) rfl rfl old R' h_old (by exact h_end))
  rintro s ⟨hpc, x7, st', m, hs, hm⟩
  refine ⟨hpc, x2, x3, _, x5, x6, x7, _, _, _, _, st', m, hs.trans rfl,
    hm.imp id fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  rw [← hE]
  exact h2

/-- Swaps the first two parts of a separating conjunction (`sep`). -/
theorem sep_swap (a b r : DataMem → Prop) : a ⋆ (b ⋆ r) = b ⋆ (a ⋆ r) := by
  ac_rfl

/-- `strtoul (nptr, endptr, base)` with `nptr` in `x0` pointing to `str`,
a non-NULL `endptr` in `x1`, and `base ≤ 36` in `w2`. It returns
`strtoulVal str base`, and stores `nptr + strtoEndOfs str base` to
`*endptr`. -/
theorem strtoul_spec [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str old : List UInt8) (base : Nat)
    (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 ≠ 0) (h_old : old.length = 8)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
      (Eq (old.At s0.regs.X1.toBitVec) ⋆ R)) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11 }
        status := st
        dmem := m } ∧
      m =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
        (Eq ((s0.regs.X0 + .ofNat (strtoEndOfs str base)).toBytes.At
          s0.regs.X1.toBitVec) ⋆ R))
    ⟨s0, strtoul⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtoul_gen code strtoul h h_sym s0 str
    old base _ _ h_len h_base h_x2 h_old h_mem
    (fun _ => by rw [← sep_swap]; exact h_mem))
  rintro s ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, st, m, hs,
    ⟨h1, -⟩ | ⟨-, hm⟩⟩
  · exact absurd h1 h_x1
  · refine ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, st, m, hs, ?_⟩
    rw [sep_swap]
    exact hm

/-- `strtoul (nptr, NULL, base)` with `nptr` in `x0` pointing to `str` and
`base ≤ 36` in `w2`. It returns `strtoulVal str base`. -/
theorem strtoul_spec_null [Labels] (code : Code) (strtoul : Int64)
    (h : Loaded code strtoul strtoul_o)
    (h_sym : label "strtoul" = strtoul)
    (s0 : MachineData) (str : List UInt8) (base : Nat) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 = 0)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11 }
        status := st })
    ⟨s0, strtoul⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtoul_gen code strtoul h h_sym s0 str
    (List.replicate 8 0) base R R h_len h_base h_x2 (by simp) h_mem
    (fun h1 => absurd h_x1 h1))
  rintro s ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, st, m, hs,
    ⟨-, rfl⟩ | ⟨h1, -⟩⟩
  · exact ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, st, hs⟩
  · exact absurd h_x1 h1
