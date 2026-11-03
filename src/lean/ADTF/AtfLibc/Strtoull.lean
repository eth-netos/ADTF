module

import ADTF.AtfLibc.Listing.strtoull_o
import ADTF.AtfLibc.Strtoul
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strtoull` from TF-A's `libc/strtoull.o`

The code is that of `strtoul` (`ADTF.AtfLibc.Strtoul`) with other
registers and one more overflow check, so the proofs follow those of
`strtoul`.

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strtoull` in ATF's `strtoull.o`. -/
def strtoull_o : List Instr := objdumpAArch64(strtoull_o_dump)

/-- `strtoull` from its entry to `strtoull + 0x44`: it skips the white space
(`ws`) and the sign. -/
theorem strtoull_ws [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = strtoull + 0x44 ∧ ∃ x0 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X4 := ldrbReg (byteAt str (strtoWs str + strtoSign str))
          X5 := s0.regs.X0 + .ofNat (strtoWs str + strtoSign str + 1)
          X3 := 0x100002700
          X7 := s0.regs.X0
          X9 := boolReg (strtoNeg str) }
        status := st })
    ⟨s0, strtoull⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "mov x3, #0x2700" at strtoull
  instr "mov x7, x0" at strtoull + 0x4
  instr "mov x5, x0" at strtoull + 0x8
  instr "movk x3, #0x1, lsl #32" at strtoull + 0xc
  refine loop_rule (measure fun i => str.length + 1 - i).wf
    (fun i s => s.pc = strtoull + 0x10 ∧ i ≤ str.length ∧
      (∀ j (_ : j < i) (hj : j < str.length), isSpace str[j]) ∧
      ∃ x0 x4 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X4 := x4
          X5 := s0.regs.X0 + .ofNat i
          X3 := 0x100002700
          X7 := s0.regs.X0 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), _, _, _, by state_eq⟩ ?_
  rintro i ⟨d', pc⟩ ⟨rfl, hi, hsp, x0, x4, st, rfl⟩
  instr "mov x0, x5" at strtoull + 0x10
  instr "ldrb w4, [x5], #1" at strtoull + 0x14
  load_byte h_mem hw
  instr "cmp w4, #0x20" at strtoull + 0x18
  instr "b.hi 30 <strtoull+0x30>" at strtoull + 0x1c
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
    instr "cmp w4, #0x2d" at strtoull + 0x30
    instr "b.ne 9c <strtoull+0x9c>" at strtoull + 0x34
    · intro hd
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        beq_eq_false_iff_ne, ne_eq] at hd
      rw [ldrb_cmp_imm_eq_iff'] at hd
      simp at hd
      rw [h_sym]
      instr "cmp w4, #0x2b" at strtoull + 0x9c
      instr "b.ne 28 <strtoull+0x28>" at strtoull + 0xa0
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
        instr "mov w9, #0x0" at strtoull + 0x28
        instr "b 44 <strtoull+0x44>" at strtoull + 0x2c
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
        instr "ldrb w4, [x5]" at strtoull + 0xa4
        simp only [ofNat_add_one64]
        load_byte h_mem hw
        instr "add x5, x0, #0x2" at strtoull + 0xa8
        instr "b 28 <strtoull+0x28>" at strtoull + 0xac
        rw [h_sym]
        instr "mov w9, #0x0" at strtoull + 0x28
        instr "b 44 <strtoull+0x44>" at strtoull + 0x2c
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
      instr "ldrb w4, [x5]" at strtoull + 0x38
      simp only [ofNat_add_one64]
      load_byte h_mem hw
      instr "add x5, x0, #0x2" at strtoull + 0x3c
      instr "mov w9, #0x1" at strtoull + 0x40
      refine .done _ (.inr ⟨by dsimp only; bv_decide, ?x0, ?st, ?heq⟩)
      case heq =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, ite_true]
      congr 2 <;> first | rfl | uint64_eq
  · intro hc
    rw [ldrb_cmp_imm_hi_iff] at hc
    simp at hc
    instr "lsr x0, x3, x4" at strtoull + 0x20
    instr "tbnz w0, #0, 10 <strtoull+0x10>" at strtoull + 0x24
    · intro hb
      rw [ws_bit_iff _ (by omega)] at hb
      have hil : i < str.length := by
        refine Nat.lt_of_le_of_ne hi fun he => ?_
        simp [he, isSpace] at hb
      refine .done _ (.inl ⟨i + 1, ?_, by rw [h_sym], hil,
        fun j hj hj' => ?_, ?x0c, ?x4c, ?stc, ?heqc⟩)
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
      instr "mov w9, #0x0" at strtoull + 0x28
      instr "b 44 <strtoull+0x44>" at strtoull + 0x2c
      refine .done _ (.inr ⟨by rw [h_sym], ?x0d, ?std, ?heqd⟩)
      case heqd =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, Bool.false_eq_true, ite_false,
        Nat.add_zero]
      congr 2 <;> first | rfl | uint64_eq

/-- The invariant (`inv`) of the digit loop of `strtoull` at
`strtoull + 0xe0`, after `k` digits from index `start` of the string at
`nptr`, in the state `d` before the loop. -/
def strtoullDigitsInv (strtoull : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b k : Nat) (s : MachineState) : Prop :=
  s.pc = strtoull + 0xe0 ∧ start + k ≤ str.length ∧
  (∀ j < k, digitVal (byteAt str (start + j)) < b) ∧
  ∃ x0 x3 x6 st, strtoAcc (digitsVal str start b k) k x0 x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X4 := ldrbReg (byteAt str (start + k))
      X5 := nptr + .ofNat (start + k + 1)
      X3 := x3
      X6 := x6
      X8 := .ofNat ((2 ^ 64 - 1) / b)
      X10 := .ofNat b
      X11 := .ofNat ((2 ^ 64 - 1) % b) }
    status := st }

/-- The state after the digit loop of `strtoull`, at `strtoull + 0x170`, for
the state `d` before the loop. -/
def strtoullDigitsPost (strtoull : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (s : MachineState) : Prop :=
  s.pc = strtoull + 0x170 ∧
  ∃ x0 x4 x3 x6 st, strtoAcc (digitsVal str start b (digitsLen str start b))
    (digitsLen str start b) x0 x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X4 := x4
      X5 := nptr + .ofNat (start + digitsLen str start b + 1)
      X3 := x3
      X6 := x6
      X8 := .ofNat ((2 ^ 64 - 1) / b)
      X10 := .ofNat b
      X11 := .ofNat ((2 ^ 64 - 1) % b) }
    status := st }

/-- The digit loop of `strtoull` from `strtoull + 0x148`, which loads the next
byte and goes back to the loop head. -/
theorem strtoull_next [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64)
    (hacc : strtoAcc (digitsVal str start b (k + 1)) (k + 1) x0 x6)
    (x4 x3 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtoullDigitsInv strtoull d nptr str start b k' s') ∨
      strtoullDigitsPost strtoull d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X4 := x4
        X5 := nptr + .ofNat (start + k + 1)
        X3 := x3
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoull + 0x148⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "ldrb w4, [x5], #1" at strtoull + 0x148
  load_byte h_mem hw
  instr "b e0 <strtoull+0xe0>" at strtoull + 0x14c
  refine .done _ (.inl ⟨k + 1, ?_, by rw [h_sym], by omega, hdig,
    x0, x3, x6, st, hacc, ?heq⟩)
  · simp only [InvImage, WellFoundedRelation.rel]; omega
  case heq =>
  simp only [← Nat.add_assoc, ofNat_add_one64]
  rw [byteAt_eq _ _ (by simp; omega)]
  simp only [ldrbReg]
  congr 2

/-- The digit loop of `strtoull` from `strtoull + 0x168`, after an overflow
(`ovf`). -/
theorem strtoull_ovf [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hov : 2 ^ 64 ≤ digitsVal str start b (k + 1))
    (x0 x4 x3 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtoullDigitsInv strtoull d nptr str start b k' s') ∨
      strtoullDigitsPost strtoull d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X4 := x4
        X5 := nptr + .ofNat (start + k + 1)
        X3 := x3
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoull + 0x168⟩ := by
  instr "mov w6, #0xffffffff" at strtoull + 0x168
  instr "b 148 <strtoull+0x148>" at strtoull + 0x16c
  rw [h_sym]
  exact strtoull_next code strtoull h h_sym d nptr str R h_len start b h_mem k
    hk
    hdig _ _ (.inr (.inr ⟨Nat.succ_pos _, hov, rfl⟩)) _ _ _

/-- The low 64 bits of the product that `mul` computes. -/
theorem mul_lo (V b : Nat) :
    (UInt64.ofNat V).toBitVec * (UInt64.ofNat b).toBitVec + 0#64 =
      BitVec.ofNat 64 (V * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

/-- The sum that `adds` computes. -/
theorem adds_val (V v b : Nat) :
    (UInt64.ofNat v).toBitVec + BitVec.ofNat 64 (V * b) =
      BitVec.ofNat 64 (V * b + v) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_comm]

/-- `adds` does not set the carry flag if the sum fits in 64 bits. -/
theorem adds_carry (V v b : Nat) (h : V * b + v < 2 ^ 64) :
    (↑((UInt64.ofNat v).toBitVec + BitVec.ofNat 64 (V * b)).toNat !=
      (↑(UInt64.ofNat v).toBitVec.toNat : Int) +
        ↑(BitVec.ofNat 64 (V * b)).toNat) = false := by
  have h1 : v < 2 ^ 64 := by omega
  have h2 : V * b < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt (show v + V * b < 2 ^ 64 by omega)]

/-- `umulh` (unsigned multiply high) gives 0 if the product fits in 64
bits. -/
theorem umulh_zero (V b : Nat) (h : V * b < 2 ^ 64) :
    BitVec.extractLsb' 64 64 (BitVec.ofInt (64 + 64)
      ((↑(UInt64.ofNat V).toBitVec.toNat : Int) *
        ↑(UInt64.ofNat b).toBitVec.toNat)) = 0 := by
  have e : ((↑(UInt64.ofNat V).toBitVec.toNat : Int) *
      ↑(UInt64.ofNat b).toBitVec.toNat) = ((V * b : Nat) : Int) := by
    rcases Nat.eq_zero_or_pos V with rfl | hV
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simp
    have hb : b < 2 ^ 64 := by
      have := Nat.le_mul_of_pos_left b hV; omega
    have hV' : V < 2 ^ 64 := by
      have := Nat.le_mul_of_pos_right V hb0; omega
    simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hV']
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  rw [show ((↑V * ↑b : Int) % 340282366920938463463374607431768211456).toNat =
    V * b by omega]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_of_lt h]

/-- The digit loop of `strtoull` from `strtoull + 0x12c`, which accumulates
(`acc`) the digit with `mul`, `umulh` (unsigned multiply high) and `adds`,
and checks again that this does not overflow. -/
theorem strtoull_acc [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hok : digitsVal str start b (k + 1) < 2 ^ 64)
    (x4 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtoullDigitsInv strtoull d nptr str start b k' s') ∨
      strtoullDigitsPost strtoull d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := .ofNat (digitsVal str start b k)
        X4 := x4
        X5 := nptr + .ofNat (start + k + 1)
        X3 := .ofNat (digitVal (byteAt str (start + k)))
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoull + 0x12c⟩ := by
  instr "mul x6, x0, x10" at strtoull + 0x12c
  instr "umulh x4, x0, x10" at strtoull + 0x130
  instr "adds x3, x3, x6" at strtoull + 0x134
  instr "cinc x4, x4, cs" at strtoull + 0x138
  have hok' : digitsVal str start b k * b + digitVal (byteAt str (start + k)) <
      2 ^ 64 := hok
  simp only [mul_lo]
  have hhi := umulh_zero (digitsVal str start b k) b (by omega)
  simp only [adds_carry _ _ _ hok', hhi, Bool.not_false, ↓reduceIte]
  simp only [adds_val]
  instr "cbnz x4, 168 <strtoull+0x168>" at strtoull + 0x13c
  · intro hnz
    exact absurd trivial hnz
  · intro hz
    instr "mov x0, x3" at strtoull + 0x140
    instr "mov w6, #0x1" at strtoull + 0x144
    have e : (⟨0#64 ||| BitVec.ofNat 64 (digitsVal str start b k * b +
        digitVal (byteAt str (start + k)))⟩ : UInt64) =
        .ofNat (digitsVal str start b (k + 1)) := by
      apply UInt64.toBitVec_inj.mp
      simp only [digitsVal, UInt64.toBitVec_ofNat', BitVec.zero_or]
    rw [e, show strtoull + 324 + 4 = strtoull + 0x148 by bv_decide]
    refine strtoull_next code strtoull h h_sym d nptr str R h_len start b h_mem
      k hk hdig _ _ (.inr (.inl ⟨Nat.succ_pos _, hok, rfl, ?h6⟩)) _ _ _
    case h6 => rfl

/-- The digit loop of `strtoull` stops at a byte that is not a digit in base
`b`. -/
theorem strtoull_stop (strtoull : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (k : Nat)
    (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (hge : b ≤ digitVal (byteAt str (start + k)))
    (x0 x4 x3 x6 : UInt64) (hacc : strtoAcc (digitsVal str start b k) k x0 x6)
    (st : StatusFlags) :
    strtoullDigitsPost strtoull d nptr str start b ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X4 := x4
        X5 := nptr + .ofNat (start + k + 1)
        X3 := x3
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoull + 0x170⟩ := by
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
  refine ⟨rfl, x0, x4, x3, x6, st, ?_, ?_⟩
  · rwa [hlen]
  · rw [hlen]

/-- One iteration of the digit loop of `strtoull` from `strtoull + 0x108`,
after the digit's value is computed. -/
theorem strtoull_digit [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64) (hacc : strtoAcc (digitsVal str start b k) k x0 x6)
    (x3 : UInt64)
    (hx5 : x3 = .ofNat (digitVal (byteAt str (start + k))))
    (hv : digitVal (byteAt str (start + k)) < 36) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtoullDigitsInv strtoull d nptr str start b k' s') ∨
      strtoullDigitsPost strtoull d nptr str start b s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X4 := ldrbReg (byteAt str (start + k))
        X5 := nptr + .ofNat (start + k + 1)
        X3 := x3
        X6 := x6
        X8 := .ofNat ((2 ^ 64 - 1) / b)
        X10 := .ofNat b
        X11 := .ofNat ((2 ^ 64 - 1) % b) }
      status := st }, strtoull + 0x108⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  subst hx5
  instr "cmp w3, w2" at strtoull + 0x108
  instr "b.ge 170 <strtoull+0x170>" at strtoull + 0x10c
  · intro hge
    simp only [h_x2, extract_ofNat64] at hge
    rw [cmp_ge_iff _ _ (by omega) (by omega)] at hge
    rw [h_sym]
    exact .done _ (.inr (strtoull_stop _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc
        _))
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
    instr "cmp x0, x8" at strtoull + 0x110
    instr "ccmn w6, #0x1, #0x4, ls" at strtoull + 0x114
    simp only [cmp_ls_eq]
    by_cases hls : x0.toBitVec.toNat ≤
        (UInt64.ofNat ((2 ^ 64 - 1) / b)).toBitVec.toNat
    · simp only [hls, decide_true, ↓reduceIte]
      instr "b.eq 168 <strtoull+0x168>" at strtoull + 0x118
      · intro heq
        rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hV, -⟩
        · exact absurd heq (by decide)
        · exact absurd heq (by decide)
        · rw [h_sym]
          refine strtoull_ovf code strtoull h h_sym d nptr str R h_len start b
              h_mem k hk' hdig' ?_ _ _ _ _ _
          show 2 ^ 64 ≤ digitsVal str start b k * b + _
          have := Nat.le_mul_of_pos_right (digitsVal str start b k) hb1
          omega
      · intro heq
        obtain ⟨hV, rfl⟩ := hsmall (by rintro rfl; exact heq (by decide))
        simp only [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hq] at hls
        instr "cmp x0, x8" at strtoull + 0x11c
        instr "b.ne 12c <strtoull+0x12c>" at strtoull + 0x120
        · intro hne
          have hne' : digitsVal str start b k ≠ (2 ^ 64 - 1) / b := by
            intro e; rw [e] at hne; simp at hne
          rw [h_sym]
          exact strtoull_acc code strtoull h h_sym d nptr str R h_len start b
            h_mem k hk' hdig'
            (cutoff_lt _ _ _ hge (by omega)) _ _ _
        · intro hne
          have e : digitsVal str start b k = (2 ^ 64 - 1) / b := by
            have := congrArg BitVec.toNat (show
              (UInt64.ofNat (digitsVal str start b k)).toBitVec =
                (UInt64.ofNat ((2 ^ 64 - 1) / b)).toBitVec by
              exact eq_of_not_sub_ne_zero _ _ hne)
            simpa [Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hq] using this
          instr "cmp w3, w11" at strtoull + 0x124
          instr "b.gt 168 <strtoull+0x168>" at strtoull + 0x128
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [h_sym]
            refine strtoull_ovf code strtoull h h_sym d nptr str R h_len start b
                h_mem k hk' hdig' ?_ _ _ _ _ _
            show 2 ^ 64 ≤ digitsVal str start b k * b + _
            rw [e]
            exact cutoff_eq_gt _ _ hgt
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [show strtoull + 296 + 4 = strtoull + 0x12c by bv_decide]
            refine strtoull_acc code strtoull h h_sym d nptr str R h_len start b
                h_mem k hk' hdig' ?_ _ _ _
            show digitsVal str start b k * b + _ < 2 ^ 64
            rw [e]
            exact cutoff_eq_le _ _ (by omega)
    · simp only [hls, decide_false, Bool.false_eq_true, ↓reduceIte]
      instr "b.eq 168 <strtoull+0x168>" at strtoull + 0x118
      · intro heq
        rw [h_sym]
        refine strtoull_ovf code strtoull h h_sym d nptr str R h_len start b
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

/-- The digit loop of `strtoull`, from `strtoull + 0xc4` to `strtoull + 0x170`.
-/
theorem strtoull_digits [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (h_start : start ≤ str.length) (hb1 : 1 ≤ b) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_x4 : d.regs.X4 = ldrbReg (byteAt str start))
    (h_x5 : d.regs.X5 = nptr + .ofNat (start + 1))
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R) :
    Eventually code.stepWp (strtoullDigitsPost strtoull d nptr str start b)
    ⟨d, strtoull + 0xc4⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "sxtw x10, w2" at strtoull + 0xc4
  instr "mov x8, #0xffffffffffffffff" at strtoull + 0xc8
  instr "mov w6, #0x0" at strtoull + 0xcc
  instr "mov x0, #0x0" at strtoull + 0xd0
  instr "udiv x8, x8, x10" at strtoull + 0xd4
  instr "mul x11, x8, x10" at strtoull + 0xd8
  instr "mvn w11, w11" at strtoull + 0xdc
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, ge_iff_le,
    Nat.zero_le, ↓reduceIte, BitVec.ushiftRight_zero, h_x2,
    sext_ofNat32 b (by omega), udiv_cutoff b hb1 hb, mvn_cutlim b hb1 hb]
  refine loop_rule (measure fun k => str.length + 1 - k).wf
    (strtoullDigitsInv strtoull d nptr str start b) _
    0 _ ⟨by dsimp only; bv_decide, by omega, fun _ h => absurd h
      (Nat.not_lt_zero _),
      ?x0i, ?x3i, ?x6i, ?sti, ?acci, ?eqi⟩ ?_
  case eqi =>
    rw [Nat.add_zero, ← h_x4, ← h_x5]
    state_eq
  case acci => exact .inl ⟨rfl, rfl, by decide⟩
  rintro k ⟨d', pc⟩ ⟨rfl, hk, hdig, x0, x3, x6, st, hacc, rfl⟩
  instr "sub w3, w4, #0x30" at strtoull + 0xe0
  instr "and x3, x3, #0xff" at strtoull + 0xe4
  instr "cmp w3, #0x9" at strtoull + 0xe8
  instr "b.ls 108 <strtoull+0x108>" at strtoull + 0xec
  · intro hA
    rw [h_sym]
    refine strtoull_digit code strtoull h h_sym d nptr str R h_len start b hb1
        hb
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
    instr "sub w3, w4, #0x41" at strtoull + 0xf0
    instr "and w3, w3, #0xff" at strtoull + 0xf4
    instr "cmp w3, #0x19" at strtoull + 0xf8
    instr "b.hi 150 <strtoull+0x150>" at strtoull + 0xfc
    · intro hB
      rw [h_sym]
      instr "sub w3, w4, #0x61" at strtoull + 0x150
      instr "and w3, w3, #0xff" at strtoull + 0x154
      instr "cmp w3, #0x19" at strtoull + 0x158
      instr "b.hi 170 <strtoull+0x170>" at strtoull + 0x15c
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
          (.inr (strtoull_stop _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc _))
      · intro hC
        instr "sub w3, w4, #0x57" at strtoull + 0x160
        instr "b 104 <strtoull+0x104>" at strtoull + 0x164
        rw [h_sym]
        instr "and x3, x3, #0xff" at strtoull + 0x104
        rw [show strtoull + 260 + 4 = strtoull + 0x108 by bv_decide]
        refine strtoull_digit code strtoull h h_sym d nptr str R h_len start b
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
      instr "sub w3, w4, #0x37" at strtoull + 0x100
      instr "and x3, x3, #0xff" at strtoull + 0x104
      rw [show strtoull + 260 + 4 = strtoull + 0x108 by bv_decide]
      refine strtoull_digit code strtoull h h_sym d nptr str R h_len start b hb1
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

/-- The state of `strtoull` at `strtoull + 0xc4`, after the prefix (white
space, sign and `0x`), when the digits start at index `start` and the base
is `b`. -/
def strtoullPrefixPost (strtoull : Int64) (s0 : MachineData) (str : List UInt8)
    (start b : Nat) (s : MachineState) : Prop :=
  s.pc = strtoull + 0xc4 ∧ ∃ x0 x2 x3 x6 st,
  x2.toBitVec.extractLsb' 0 32 = .ofNat 32 b ∧
  s.data = { s0 with
    regs := { s0.regs with
      X0 := x0
      X2 := x2
      X4 := ldrbReg (byteAt str start)
      X5 := s0.regs.X0 + .ofNat (start + 1)
      X3 := x3
      X6 := x6
      X7 := s0.regs.X0
      X9 := boolReg (strtoNeg str) }
    status := st }

/-- `strtoull` from `strtoull + 0xb0`, which picks the base if there is no
`0x` prefix and the base is 0 (`b0`) or 16. -/
theorem strtoull_b0 [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str : List UInt8)
    (base : Nat) (hbase : base = 0 ∨ base = 16)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 x3 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtoullPrefixPost strtoull s0 str (strtoPos str)
      (strtoBaseNoHex str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X4 := ldrbReg (byteAt str (strtoPos str))
        X5 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X3 := x3
        X6 := x6
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoull + 0xb0⟩ := by
  instr "cbnz w2, 94 <strtoull+0x94>" at strtoull + 0xb0
  · intro hnz
    rw [h_x2] at hnz
    have h16 : base = 16 := by
      rcases hbase with rfl | rfl
      · exact absurd rfl hnz
      · rfl
    subst h16
    rw [h_sym]
    instr "mov w2, #0x10" at strtoull + 0x94
    instr "b c4 <strtoull+0xc4>" at strtoull + 0x98
    refine .done _ ⟨by rw [h_sym], x0, ?x2a, x3, x6, st, ?ext1, ?eq1⟩
    case eq1 => state_eq
    case ext1 => simp [strtoBaseNoHex]
  · intro hz
    rw [h_x2] at hz
    have h0 : base = 0 := by
      rcases hbase with rfl | rfl
      · rfl
      · exact absurd hz (by decide)
    subst h0
    instr "cmp w4, #0x30" at strtoull + 0xb4
    instr "mov w2, #0xa" at strtoull + 0xb8
    instr "mov w0, #0x8" at strtoull + 0xbc
    instr "csel w2, w2, w0, ne" at strtoull + 0xc0
    refine .done _ ⟨by dsimp only; bv_decide, ?x0b, ?x2b, x3, x6, ?stb, ?ext2,
      ?eq2⟩
    case eq2 => state_eq
    case ext2 =>
      simp only [strtoBaseNoHex, ↓reduceIte]
      by_cases hc : byteAt str (strtoPos str) = 48
      · simp only [hc, ↓reduceIte]
        rfl
      · simp only [hc, ↓reduceIte]
        exact csel_base _ hc

/-- `strtoull` from `strtoull + 0x8c`, which skips a `0x` prefix (`hex`) that
starts at index `P`. -/
theorem strtoull_hex [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str : List UInt8) (P : Nat)
    (x0 x4 x3 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtoullPrefixPost strtoull s0 str (P + 2) 16)
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X4 := x4
        X5 := s0.regs.X0 + .ofNat (P + 1)
        X3 := x3
        X6 := ldrbReg (byteAt str (P + 2))
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoull + 0x8c⟩ := by
  instr "add x5, x5, #0x2" at strtoull + 0x8c
  instr "mov w4, w6" at strtoull + 0x90
  instr "mov w2, #0x10" at strtoull + 0x94
  instr "b c4 <strtoull+0xc4>" at strtoull + 0x98
  refine .done _ ⟨by rw [h_sym], x0, ?x2h, x3, ?x6h, st, ?exth, ?eqh⟩
  case eqh =>
    simp only [ldrbReg]
    congr 2 <;> first | rfl | uint64_eq
  case exth => rfl

/-- `strtoull` from `strtoull + 0x44` to `strtoull + 0xc4`, through the prefix
(the `0x` and the choice of the base). -/
theorem strtoull_prefix [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R)
    (base : Nat) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtoullPrefixPost strtoull s0 str (strtoStart str
      base)
      (strtoBase str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X4 := ldrbReg (byteAt str (strtoPos str))
        X5 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X3 := 0x100002700
        X7 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtoull + 0x44⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "tst w2, #0xffffffef" at strtoull + 0x44
  instr "b.ne c4 <strtoull+0xc4>" at strtoull + 0x48
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
    refine .done _ ⟨rfl, x0, ?x2p, ?x3p, ?x6p, ?stp, ?extp, ?eqp⟩
    case eqp => rfl
    case extp => exact h_x2
  · intro hne
    simp only [h_x2] at hne
    have hbase : base = 0 ∨ base = 16 := (tst_base base (by omega)).mp hne
    instr "cmp w4, #0x30" at strtoull + 0x4c
    instr "b.ne b0 <strtoull+0xb0>" at strtoull + 0x50
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
      exact strtoull_b0 code strtoull h h_sym s0 str base hbase h_x2 _ _ _ _
    · intro h0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.not_eq_false] at h0
      rw [ldrbReg, ldrb_cmp_imm_eq_iff] at h0
      simp at h0
      have hb0 : byteAt str (strtoPos str) = 48 := UInt8.toNat_inj.mp h0
      have hp0 := lt_of_byteAt_ne_zero (by rw [hb0]; decide)
      instr "ldrb w0, [x5]" at strtoull + 0x54
      load_byte h_mem hw
      instr "and w0, w0, #0xffffffdf" at strtoull + 0x58
      instr "and w0, w0, #0xff" at strtoull + 0x5c
      instr "cmp w0, #0x58" at strtoull + 0x60
      instr "b.ne b0 <strtoull+0xb0>" at strtoull + 0x64
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
        exact strtoull_b0 code strtoull h h_sym s0 str base hbase h_x2 _ _ _ _
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
        instr "ldrb w6, [x5, #1]" at strtoull + 0x68
        simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat',
          BitVec.add_assoc,
          ofNat_add_one64]
        load_byte h_mem hw
        instr "sub w0, w6, #0x30" at strtoull + 0x6c
        instr "and w0, w0, #0xff" at strtoull + 0x70
        instr "cmp w0, #0x36" at strtoull + 0x74
        instr "b.hi b0 <strtoull+0xb0>" at strtoull + 0x78
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
          exact strtoull_b0 code strtoull h h_sym s0 str base hbase h_x2 _ _ _ _
        · intro hhi
          instr "mov x3, #0x7e0000007e0000" at strtoull + 0x7c
          instr "movk x3, #0x3ff" at strtoull + 0x80
          instr "lsr x0, x3, x0" at strtoull + 0x84
          instr "tbz w0, #0, b0 <strtoull+0xb0>" at strtoull + 0x88
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
            exact strtoull_b0 code strtoull h h_sym s0 str base hbase h_x2 _ _
                _ _
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
            rw [← e2, show strtoull + 136 + 4 = strtoull + 0x8c by bv_decide]
            exact strtoull_hex code strtoull h h_sym s0 str _ _ _ _ _

/-- `strtoull` from `strtoull + 0x18c`, which stores `x7` to `*endptr` and
returns. -/
theorem strtoull_str [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o) (d : MachineData)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ m, s.data = { d with dmem := m } ∧
      m =⋆ Eq (d.regs.X7.toBytes.At d.regs.X1.toBitVec) ⋆ R)
    ⟨d, strtoull + 0x18c⟩ := by
  instr "str x7, [x1]" at strtoull + 0x18c
  simp (disch := first | rfl | simp [h_old]) only
    [MachineData.store_of_sep64_zero h_mem, Effects.All, MemWidth.bytes]
  have hL := Mem.storeInt_sep _ 8 _ _ _ ⟨h_mem, h_old⟩
    d.regs.X7.toBitVec.toInt
  rw [show Int.toBytes 8 d.regs.X7.toBitVec.toInt = d.regs.X7.toBytes
    from rfl] at hL
  instr "ret" at strtoull + 0x190
  exact .done _ ⟨rfl, _, rfl, hL⟩

/-- `strtoull` from `strtoull + 0x188`, which stores the pointer after the
digits to `*endptr` and returns. -/
theorem strtoull_188 [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o) (d : MachineData) (q : UInt64)
    (h_x5 : d.regs.X5 = q + 1) (hX1 : d.regs.X1 ≠ 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (epiPost d d.regs.X0 q R)
      ⟨d, strtoull + 0x188⟩ := by
  instr "sub x7, x5, #0x1" at strtoull + 0x188
  rw [show strtoull + 392 + 4 = strtoull + 0x18c by bv_decide]
  refine eventually_weaken _ _ _ _ ?_
    (strtoull_str code strtoull h _ old R h_old h_mem)
  rintro s ⟨hpc, m, hs, hm⟩
  refine ⟨hpc, ⟨d.regs.X5.toBitVec - 1⟩, d.status, m, hs.trans rfl,
    .inr ⟨hX1, ?_⟩⟩
  have hq : (⟨d.regs.X5.toBitVec - 1⟩ : UInt64) = q := by
    rw [h_x5]; apply UInt64.toBitVec_inj.mp; simp [BitVec.add_sub_cancel]
  rw [← hq]
  exact hm

/-- `strtoull` from `strtoull + 0x180`, which stores to `*endptr` if it is not
NULL and returns. -/
theorem strtoull_180 [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull) (d : MachineData) (n : Nat)
    (q : UInt64) (h_x5 : d.regs.X5 = q + 1)
    (h_w6 : BitVec.extractLsb' 0 32 d.regs.X6.toBitVec = 0 ↔ n = 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (epiPost d d.regs.X0 (strtoEnd n d.regs.X7 q) R)
      ⟨d, strtoull + 0x180⟩ := by
  instr "cbz x1, 190 <strtoull+0x190>" at strtoull + 0x180
  · intro hz
    rw [h_sym]
    instr "ret" at strtoull + 0x190
    exact .done _ ⟨rfl, d.regs.X7, d.status, d.dmem, rfl,
      .inl ⟨by simpa [← UInt64.toBitVec_inj] using hz, rfl⟩⟩
  · intro hz
    have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
    instr "cbz w6, 18c <strtoull+0x18c>" at strtoull + 0x184
    · intro h6
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtoull_str code strtoull h d old R h_old (h_mem hX1))
      rintro s ⟨hpc, m, hs, hm⟩
      refine ⟨hpc, d.regs.X7, d.status, m, hs.trans rfl, .inr ⟨hX1, ?_⟩⟩
      simp only [strtoEnd, h_w6.mp h6, ↓reduceIte]
      exact hm
    · intro h6
      have hn : ¬n = 0 := fun h0 => h6 (h_w6.mpr h0)
      simp only [strtoEnd, hn, ↓reduceIte]
      rw [show strtoull + 388 + 4 = strtoull + 0x188 by bv_decide]
      exact strtoull_188 code strtoull h d q h_x5 hX1 old R h_old (h_mem hX1)

/-- The epilogue (`epi`) of `strtoull`, from `strtoull + 0x170`, after `n`
digits with the value `V`, where `q` is the pointer after the digits. -/
theorem strtoull_epi [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (d : MachineData) (neg : Bool) (V n : Nat) (q x0 x6 : UInt64)
    (hacc : strtoAcc V n x0 x6) (hV0 : n = 0 → V = 0)
    (h_x0 : d.regs.X0 = x0) (h_x5 : d.regs.X5 = q + 1)
    (h_x6 : d.regs.X6 = x6) (h_x9 : d.regs.X9 = boolReg neg)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (epiPost d (strtoRet V neg) (strtoEnd n d.regs.X7 q) R)
      ⟨d, strtoull + 0x170⟩ := by
  instr "cmn w6, #0x1" at strtoull + 0x170
  instr "b.eq 194 <strtoull+0x194>" at strtoull + 0x174
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
    instr "mov x0, #0xffffffffffffffff" at strtoull + 0x194
    instr "cbnz x1, 188 <strtoull+0x188>" at strtoull + 0x198
    · intro hz
      have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtoull_188 code strtoull h _ q (by exact h_x5) (by exact hX1) old R
          h_old (by exact h_mem hX1))
      exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs
    · intro hz
      instr "b 190 <strtoull+0x190>" at strtoull + 0x19c
      rw [h_sym]
      instr "ret" at strtoull + 0x190
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
      instr "cbz w9, 180 <strtoull+0x180>" at strtoull + 0x178
      · intro hz
        rw [h_sym]
        refine eventually_weaken _ _ _ _ ?_
          (strtoull_180 code strtoull h h_sym _ n q (by exact h_x5)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
    · simp only [↓reduceIte]
      instr "cbz w9, 180 <strtoull+0x180>" at strtoull + 0x178
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
      · intro hz
        instr "neg x0, x0" at strtoull + 0x17c
        rw [show strtoull + 380 + 4 = strtoull + 0x180 by bv_decide,
          show -d.regs.X0 = ⟨0#64 - d.regs.X0.toBitVec⟩ from
            UInt64.toBitVec_inj.mp (by simp)]
        refine eventually_weaken _ _ _ _ ?_
          (strtoull_180 code strtoull h h_sym _ n q (by exact h_x5)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => epiPost_of ⟨_, rfl⟩ rfl hs

/-- `strtoull` for both a NULL and a non-NULL `endptr` (general, `gen`). -/
theorem strtoull_gen [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
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
      ∃ x2 x4 x5 x3 x6 x7 x8 x9 x10 x11 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X4 := x4
          X5 := x5
          X3 := x3
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
    ⟨s0, strtoull⟩ := by
  obtain ⟨hb1, hb36⟩ := strtoBase_range str base h_base
  refine eventually_trans _ _ _ _
    (strtoull_ws code strtoull h h_sym s0 str R h_len h_mem) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, st, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtoull_prefix code strtoull h h_sym s0 str
    R h_len h_mem base h_base h_x2 x0 st) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, x2, x3, x6, st, hx2, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtoull_digits code strtoull h h_sym _
    s0.regs.X0 str R h_len _ _ (strtoStart_le str base) hb1 hb36 hx2 rfl rfl
    h_mem) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, x4, x3, x6, st, hacc, hs⟩
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
  refine eventually_weaken _ _ _ _ ?_ (strtoull_epi code strtoull h h_sym _
    (strtoNeg str) _ _ _ x0 x6 hacc (fun h0 => by rw [h0]; rfl) rfl
    (by exact hx4) rfl rfl old R' h_old (by exact h_end))
  rintro s ⟨hpc, x7, st', m, hs, hm⟩
  refine ⟨hpc, x2, x4, _, x3, x6, x7, _, _, _, _, st', m, hs.trans rfl,
    hm.imp id fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  rw [← hE]
  exact h2

/-- `strtoull (nptr, endptr, base)` with `nptr` in `x0` pointing to `str`,
a non-NULL `endptr` in `x1`, and `base ≤ 36` in `w2`. It returns
`strtoulVal str base`, and stores `nptr + strtoEndOfs str base` to
`*endptr`. -/
theorem strtoull_spec [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str old : List UInt8) (base : Nat)
    (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 ≠ 0) (h_old : old.length = 8)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
      (Eq (old.At s0.regs.X1.toBitVec) ⋆ R)) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x4 x5 x3 x6 x7 x8 x9 x10 x11 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X4 := x4
          X5 := x5
          X3 := x3
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
    ⟨s0, strtoull⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtoull_gen code strtoull h h_sym s0 str
    old base _ _ h_len h_base h_x2 h_old h_mem
    (fun _ => by rw [← sep_swap]; exact h_mem))
  rintro s ⟨hpc, x2, x4, x5, x3, x6, x7, x8, x9, x10, x11, st, m, hs,
    ⟨h1, -⟩ | ⟨-, hm⟩⟩
  · exact absurd h1 h_x1
  · refine ⟨hpc, x2, x4, x5, x3, x6, x7, x8, x9, x10, x11, st, m, hs, ?_⟩
    rw [sep_swap]
    exact hm

/-- `strtoull (nptr, NULL, base)` with `nptr` in `x0` pointing to `str` and
`base ≤ 36` in `w2`. It returns `strtoulVal str base`. -/
theorem strtoull_spec_null [Labels] (code : Code) (strtoull : Int64)
    (h : Loaded code strtoull strtoull_o)
    (h_sym : label "strtoull" = strtoull)
    (s0 : MachineData) (str : List UInt8) (base : Nat) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 = 0)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x4 x5 x3 x6 x7 x8 x9 x10 x11 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtoulVal str base
          X2 := x2
          X4 := x4
          X5 := x5
          X3 := x3
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11 }
        status := st })
    ⟨s0, strtoull⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtoull_gen code strtoull h h_sym s0 str
    (List.replicate 8 0) base R R h_len h_base h_x2 (by simp) h_mem
    (fun h1 => absurd h_x1 h1))
  rintro s ⟨hpc, x2, x4, x5, x3, x6, x7, x8, x9, x10, x11, st, m, hs,
    ⟨-, rfl⟩ | ⟨h1, -⟩⟩
  · exact ⟨hpc, x2, x4, x5, x3, x6, x7, x8, x9, x10, x11, st, hs⟩
  · exact absurd h_x1 h1
