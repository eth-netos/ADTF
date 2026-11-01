module

public import ADTF.AtfLibc.Listing.strtol_o
public import ADTF.AtfLibc.Strtoul
public import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strtol` from TF-A's `libc/strtol.o`

The code is that of `strtoul` (`ADTF.AtfLibc.Strtoul`) with other
registers, a limit that depends on the sign, and another epilogue, so most
proofs are those of `strtoul`, generalized to the limit `strtolMax`.

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

@[expose] public section

/-- The instructions of `strtol` in ATF's `strtol.o`. -/
def strtol_o : List Instr := objdumpAArch64(strtol_o_dump)

/-- `strtol` from its entry to `strtol + 0x44`: it skips the white space
(`ws`) and the sign. -/
theorem strtol_ws [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = strtol + 0x44 ∧ ∃ x0 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X3 := ldrbReg (byteAt str (strtoWs str + strtoSign str))
          X4 := s0.regs.X0 + .ofNat (strtoWs str + strtoSign str + 1)
          X5 := 0x100002700
          X8 := s0.regs.X0
          X9 := boolReg (strtoNeg str) }
        status := st })
    ⟨s0, strtol⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "mov x5, #0x2700" at strtol
  instr "mov x8, x0" at strtol + 0x4
  instr "mov x4, x0" at strtol + 0x8
  instr "movk x5, #0x1, lsl #32" at strtol + 0xc
  refine loop_rule (measure fun i => str.length + 1 - i).wf
    (fun i s => s.pc = strtol + 0x10 ∧ i ≤ str.length ∧
      (∀ j (_ : j < i) (hj : j < str.length), isSpace str[j]) ∧
      ∃ x0 x3 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X3 := x3
          X4 := s0.regs.X0 + .ofNat i
          X5 := 0x100002700
          X8 := s0.regs.X0 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), _, _, _, by state_eq⟩ ?_
  rintro i ⟨d', pc⟩ ⟨rfl, hi, hsp, x0, x3, st, rfl⟩
  instr "mov x0, x4" at strtol + 0x10
  instr "ldrb w3, [x4], #1" at strtol + 0x14
  load_byte h_mem hw
  instr "cmp w3, #0x20" at strtol + 0x18
  instr "b.hi 30 <strtol+0x30>" at strtol + 0x1c
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
    instr "cmp w3, #0x2d" at strtol + 0x30
    instr "b.ne 9c <strtol+0x9c>" at strtol + 0x34
    · intro hd
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        beq_eq_false_iff_ne, ne_eq] at hd
      rw [ldrb_cmp_imm_eq_iff'] at hd
      simp at hd
      rw [h_sym]
      instr "cmp w3, #0x2b" at strtol + 0x9c
      instr "b.ne 28 <strtol+0x28>" at strtol + 0xa0
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
        instr "mov w9, #0x0" at strtol + 0x28
        instr "b 44 <strtol+0x44>" at strtol + 0x2c
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
        instr "ldrb w3, [x4]" at strtol + 0xa4
        simp only [ofNat_add_one64]
        load_byte h_mem hw
        instr "add x4, x0, #0x2" at strtol + 0xa8
        instr "b 28 <strtol+0x28>" at strtol + 0xac
        rw [h_sym]
        instr "mov w9, #0x0" at strtol + 0x28
        instr "b 44 <strtol+0x44>" at strtol + 0x2c
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
      instr "ldrb w3, [x4]" at strtol + 0x38
      simp only [ofNat_add_one64]
      load_byte h_mem hw
      instr "add x4, x0, #0x2" at strtol + 0x3c
      instr "mov w9, #0x1" at strtol + 0x40
      refine .done _ (.inr ⟨by dsimp only; bv_decide, ?x0, ?st, ?heq⟩)
      case heq =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, ite_true]
      congr 2 <;> first | rfl | uint64_eq
  · intro hc
    rw [ldrb_cmp_imm_hi_iff] at hc
    simp at hc
    instr "lsr x0, x5, x3" at strtol + 0x20
    instr "tbnz w0, #0, 10 <strtol+0x10>" at strtol + 0x24
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
      instr "mov w9, #0x0" at strtol + 0x28
      instr "b 44 <strtol+0x44>" at strtol + 0x2c
      refine .done _ (.inr ⟨by rw [h_sym], ?x0d, ?std, ?heqd⟩)
      case heqd =>
      rw [hws, hsg, hng, byteAt_eq _ _ (by simp; omega)]
      simp only [boolReg, ldrbReg, Bool.false_eq_true, ite_false,
        Nat.add_zero]
      congr 2 <;> first | rfl | uint64_eq

/-- The largest absolute value (`max`) that `strtol` can return without an
overflow: `LONG_MAX`, or the absolute value of `LONG_MIN` if the number is
negative (`neg`). -/
def strtolMax (neg : Bool) : Nat := if neg then 2 ^ 63 else 2 ^ 63 - 1

/-- `strtolMax neg` is less than (`lt`) `2 ^ 64`. -/
theorem strtolMax_lt (neg : Bool) : strtolMax neg < 2 ^ 64 := by
  cases neg <;> decide

/-- `sxtw` (sign-extend word) of a flag. -/
theorem sxtw_boolReg (neg : Bool) :
    BitVec.signExtend 64 (BitVec.extractLsb' 0 32 (boolReg neg).toBitVec) =
      (boolReg neg).toBitVec := by
  cases neg <;> decide

/-- `mov` and `add` compute `strtolMax neg` from the flag `neg`. -/
theorem add_strtolMax (neg : Bool) :
    (boolReg neg).toBitVec + ~~~((32768 &&& 65535#64) <<< 48) =
      BitVec.ofNat 64 (strtolMax neg) := by
  cases neg <;> decide

/-- `udiv` (unsigned divide) computes the cutoff `M / b` for the limit
(`lim`) `M`. -/
theorem udiv_limCutoff (M b : Nat) (hM : M < 2 ^ 64) (hb1 : 1 ≤ b)
    (hb : b ≤ 36) :
    (if (BitVec.ofNat 64 b == 0) = true then (0 : BitVec 64)
      else BitVec.ofNat 64 M / BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (M / b) := by
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
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hM)]

/-- `msub` (multiply-subtract) computes the cut limit (`cutlim`) `M % b`
for the limit (`lim`) `M`. -/
theorem msub_limCutlim (M b : Nat) (hb1 : 1 ≤ b) (hb : b ≤ 36) :
    BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 M) -
      BitVec.extractLsb' 0 32 (BitVec.ofNat 64 (M / b)) *
        BitVec.extractLsb' 0 32 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 (M % b) := by
  have e : ∀ n, BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n) =
      BitVec.ofNat 32 n := by
    intro n
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_mod_of_dvd n (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  rw [e, e, e]
  have hd := Nat.div_add_mod' M b
  have hs : BitVec.ofNat 32 M = BitVec.ofNat 32 (M / b) * BitVec.ofNat 32 b +
      BitVec.ofNat 32 (M % b) := by
    have h1 : BitVec.ofNat 32 M = BitVec.ofNat 32 (M / b * b + M % b) := by
      rw [hd]
    rw [h1]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  rw [hs, BitVec.add_comm, BitVec.add_sub_cancel]
  apply BitVec.eq_of_toNat_eq
  have := Nat.mod_lt M (by omega : b > 0)
  simp
  omega

/-- What the registers `x0` and `x6` hold for the accumulated value (`acc`)
`v` after `k` digits, with the limit `M`: `x6` is 0 before the first digit,
1 after it, and `0xffffffff` (-1) after an overflow; `x0` is `v` as long as
there is no overflow. -/
def strtolAcc (M v k : Nat) (x0 x6 : UInt64) : Prop :=
  (k = 0 ∧ x0 = 0 ∧ x6 = 0) ∨ (0 < k ∧ v ≤ M ∧ x0 = .ofNat v ∧ x6 = 1) ∨
    (0 < k ∧ M < v ∧ x6 = 0xffffffff)

/-- How the accumulator `V` compares with the cutoff `M / b` for the limit
(`lim`) `M` decides whether `V * b + v` exceeds `M`, for a digit `v < b`:
here `V` is less than (`lt`) the cutoff. -/
theorem limCutoff_lt (M V v b : Nat) (hv : v < b) (h : V < M / b) :
    V * b + v ≤ M := by
  have hd : M / b * b + M % b = M := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hm : V * b + b ≤ M / b * b := by
    have := Nat.mul_le_mul_right b (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  generalize M / b * b = qb at hd hm
  omega

/-- An accumulator equal (`eq`) to the cutoff for the limit (`lim`) `M`, and
a digit `v` less than or equal (`le`) to the cut limit `M % b`, do not exceed
`M`. -/
theorem limCutoff_eq_le (M v b : Nat) (h : v ≤ M % b) : M / b * b + v ≤ M := by
  have hd : M / b * b + M % b = M := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  generalize M / b * b = qb at hd ⊢
  generalize M % b = r at hd h
  omega

/-- An accumulator equal (`eq`) to the cutoff for the limit (`lim`) `M`, and
a digit `v` greater than (`gt`) the cut limit `M % b`, exceed `M`. -/
theorem limCutoff_eq_gt (M v b : Nat) (h : M % b < v) : M < M / b * b + v := by
  have hd : M / b * b + M % b = M := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  generalize M / b * b = qb at hd ⊢
  generalize M % b = r at hd h
  omega

/-- An accumulator `V` greater than (`gt`) the cutoff for the limit (`lim`)
`M` exceeds `M`. -/
theorem limCutoff_gt (M V v b : Nat) (hb : 0 < b) (h : M / b < V) :
    M < V * b + v := by
  have hd : M / b * b + M % b = M := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hr := Nat.mod_lt M hb
  have hm : M / b * b + b ≤ V * b := by
    have := Nat.mul_le_mul_right b (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  generalize M / b * b = qb at hd hm
  generalize M % b = r at hd hr
  omega

/-- The invariant (`inv`) of the digit loop of `strtol` at
`strtol + 0xe4`, after `k` digits from index `start` of the string at
`nptr`, in the state `d` before the loop. -/
def strtolDigitsInv (strtol : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (neg : Bool) (k : Nat) (s :
        MachineState) : Prop :=
  s.pc = strtol + 0xe4 ∧ start + k ≤ str.length ∧
  (∀ j < k, digitVal (byteAt str (start + j)) < b) ∧
  ∃ x0 x5 x6 st, strtolAcc (strtolMax neg) (digitsVal str start b k) k x0 x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X3 := ldrbReg (byteAt str (start + k))
      X4 := nptr + .ofNat (start + k + 1)
      X5 := x5
      X6 := x6
      X12 := .ofNat ((strtolMax neg) / b)
      X10 := boolReg neg
      X11 := .ofNat b
      X7 := .ofNat ((strtolMax neg) % b) }
    status := st }

/-- The state after the digit loop of `strtol`, at `strtol + 0x160`, for
the state `d` before the loop. -/
def strtolDigitsPost (strtol : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (neg : Bool) (s : MachineState) : Prop :=
  s.pc = strtol + 0x160 ∧
  ∃ x0 x3 x5 x6 st, strtolAcc (strtolMax neg)
    (digitsVal str start b (digitsLen str start b)) (digitsLen str start b) x0
    x6 ∧
  s.data = { d with
    regs := { d.regs with
      X0 := x0
      X3 := x3
      X4 := nptr + .ofNat (start + digitsLen str start b + 1)
      X5 := x5
      X6 := x6
      X12 := .ofNat ((strtolMax neg) / b)
      X10 := boolReg neg
      X11 := .ofNat b
      X7 := .ofNat ((strtolMax neg) % b) }
    status := st }

/-- The digit loop of `strtol` from `strtol + 0x138`, which loads the next
byte and goes back to the loop head. -/
theorem strtol_next [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (neg : Bool)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64)
    (hacc : strtolAcc (strtolMax neg) (digitsVal str start b (k + 1)) (k + 1)
        x0 x6)
    (x3 x5 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtolDigitsInv strtol d nptr str start b neg k' s') ∨
      strtolDigitsPost strtol d nptr str start b neg s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X12 := .ofNat ((strtolMax neg) / b)
        X10 := boolReg neg
        X11 := .ofNat b
        X7 := .ofNat ((strtolMax neg) % b) }
      status := st }, strtol + 0x138⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "ldrb w3, [x4], #1" at strtol + 0x138
  load_byte h_mem hw
  instr "b e4 <strtol+0xe4>" at strtol + 0x13c
  refine .done _ (.inl ⟨k + 1, ?_, by rw [h_sym], by omega, hdig,
    x0, x5, x6, st, hacc, ?heq⟩)
  · simp only [InvImage, WellFoundedRelation.rel]; omega
  case heq =>
  simp only [← Nat.add_assoc, ofNat_add_one64]
  rw [byteAt_eq _ _ (by simp; omega)]
  simp only [ldrbReg]
  congr 2

/-- The digit loop of `strtol` from `strtol + 0x158`, after an overflow
(`ovf`). -/
theorem strtol_ovf [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (neg : Bool)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hov : strtolMax neg < digitsVal str start b (k + 1))
    (x0 x3 x5 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtolDigitsInv strtol d nptr str start b neg k' s') ∨
      strtolDigitsPost strtol d nptr str start b neg s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X12 := .ofNat ((strtolMax neg) / b)
        X10 := boolReg neg
        X11 := .ofNat b
        X7 := .ofNat ((strtolMax neg) % b) }
      status := st }, strtol + 0x158⟩ := by
  instr "mov w6, #0xffffffff" at strtol + 0x158
  instr "b 138 <strtol+0x138>" at strtol + 0x15c
  rw [h_sym]
  exact strtol_next code strtol h h_sym d nptr str R h_len start b neg h_mem k
    hk
    hdig _ _ (.inr (.inr ⟨Nat.succ_pos _, hov, rfl⟩)) _ _ _

/-- The digit loop of `strtol` from `strtol + 0x130`, which accumulates the
digit with `madd` (multiply-add). -/
theorem strtol_madd [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (neg : Bool)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k < str.length)
    (hdig : ∀ j < k + 1, digitVal (byteAt str (start + j)) < b)
    (hok : digitsVal str start b (k + 1) ≤ strtolMax neg)
    (x3 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtolDigitsInv strtol d nptr str start b neg k' s') ∨
      strtolDigitsPost strtol d nptr str start b neg s')
    ⟨{ d with
      regs := { d.regs with
        X0 := .ofNat (digitsVal str start b k)
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := .ofNat (digitVal (byteAt str (start + k)))
        X6 := x6
        X12 := .ofNat ((strtolMax neg) / b)
        X10 := boolReg neg
        X11 := .ofNat b
        X7 := .ofNat ((strtolMax neg) % b) }
      status := st }, strtol + 0x130⟩ := by
  instr "madd x0, x11, x0, x5" at strtol + 0x130
  instr "mov w6, #0x1" at strtol + 0x134
  have e : (⟨(UInt64.ofNat b).toBitVec *
      (UInt64.ofNat (digitsVal str start b k)).toBitVec +
      (UInt64.ofNat (digitVal (byteAt str (start + k)))).toBitVec⟩ : UInt64)
      = .ofNat (digitsVal str start b (k + 1)) := by
    simp only [digitsVal]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_ofNat']
    rw [Nat.mul_comm]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
  rw [e, show strtol + 308 + 4 = strtol + 0x138 by bv_decide]
  refine strtol_next code strtol h h_sym d nptr str R h_len start b neg h_mem k
    hk hdig _ _ (.inr (.inl ⟨Nat.succ_pos _, hok, rfl, ?h6⟩)) _ _ _
  case h6 => rfl

/-- The digit loop of `strtol` stops at a byte that is not a digit in base
`b`. -/
theorem strtol_stop (strtol : Int64) (d : MachineData) (nptr : UInt64)
    (str : List UInt8) (start b : Nat) (neg : Bool) (k : Nat)
    (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (hge : b ≤ digitVal (byteAt str (start + k)))
    (x0 x3 x5 x6 : UInt64) (hacc : strtolAcc (strtolMax neg) (digitsVal str
        start b k) k x0 x6)
    (st : StatusFlags) :
    strtolDigitsPost strtol d nptr str start b neg ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := x3
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X12 := .ofNat ((strtolMax neg) / b)
        X10 := boolReg neg
        X11 := .ofNat b
        X7 := .ofNat ((strtolMax neg) % b) }
      status := st }, strtol + 0x160⟩ := by
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

/-- One iteration of the digit loop of `strtol` from `strtol + 0x10c`,
after the digit's value is computed. -/
theorem strtol_digit [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (neg : Bool) (hb1 : 1 ≤ b) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R)
    (k : Nat) (hk : start + k ≤ str.length)
    (hdig : ∀ j < k, digitVal (byteAt str (start + j)) < b)
    (x0 x6 : UInt64) (hacc : strtolAcc (strtolMax neg) (digitsVal str start b
        k) k x0 x6)
    (x5 : UInt64)
    (hx5 : x5 = .ofNat (digitVal (byteAt str (start + k))))
    (hv : digitVal (byteAt str (start + k)) < 36) (st : StatusFlags) :
    Eventually code.stepWp (fun s' =>
      (∃ k', (measure fun k => str.length + 1 - k).rel k' k ∧
        strtolDigitsInv strtol d nptr str start b neg k' s') ∨
      strtolDigitsPost strtol d nptr str start b neg s')
    ⟨{ d with
      regs := { d.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (start + k))
        X4 := nptr + .ofNat (start + k + 1)
        X5 := x5
        X6 := x6
        X12 := .ofNat ((strtolMax neg) / b)
        X10 := boolReg neg
        X11 := .ofNat b
        X7 := .ofNat ((strtolMax neg) % b) }
      status := st }, strtol + 0x10c⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  subst hx5
  instr "cmp w5, w2" at strtol + 0x10c
  instr "b.ge 160 <strtol+0x160>" at strtol + 0x110
  · intro hge
    simp only [h_x2, extract_ofNat64] at hge
    rw [cmp_ge_iff _ _ (by omega) (by omega)] at hge
    rw [h_sym]
    exact .done _ (.inr (strtol_stop _ _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc
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
    have hq : (strtolMax neg) / b < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (strtolMax_lt neg)
    have hr : (strtolMax neg) % b < b := Nat.mod_lt _ (by omega)
    have hsmall : x6 ≠ 0xffffffff → digitsVal str start b k ≤ strtolMax neg ∧
        x0 = .ofNat (digitsVal str start b k) := by
      intro h6
      rcases hacc with ⟨rfl, rfl, -⟩ | ⟨-, hV, rfl, -⟩ | ⟨-, -, h6'⟩
      · exact ⟨by simp [digitsVal], rfl⟩
      · exact ⟨hV, rfl⟩
      · exact absurd h6' h6
    instr "cmp x0, x12" at strtol + 0x114
    instr "ccmn w6, #0x1, #0x4, ls" at strtol + 0x118
    simp only [cmp_ls_eq]
    by_cases hls : x0.toBitVec.toNat ≤
        (UInt64.ofNat ((strtolMax neg) / b)).toBitVec.toNat
    · simp only [hls, decide_true, ↓reduceIte]
      instr "b.eq 158 <strtol+0x158>" at strtol + 0x11c
      · intro heq
        rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hV, -⟩
        · exact absurd heq (by decide)
        · exact absurd heq (by decide)
        · rw [h_sym]
          refine strtol_ovf code strtol h h_sym d nptr str R h_len start b neg
              h_mem k hk' hdig' ?_ _ _ _ _ _
          show strtolMax neg < digitsVal str start b k * b + _
          have := Nat.le_mul_of_pos_right (digitsVal str start b k) hb1
          omega
      · intro heq
        obtain ⟨hV, rfl⟩ := hsmall (by rintro rfl; exact heq (by decide))
        simp only [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hV (strtolMax_lt neg)),
              Nat.mod_eq_of_lt hq] at hls
        instr "cmp x0, x12" at strtol + 0x120
        instr "b.ne 130 <strtol+0x130>" at strtol + 0x124
        · intro hne
          have hne' : digitsVal str start b k ≠ (strtolMax neg) / b := by
            intro e; rw [e] at hne; simp at hne
          rw [h_sym]
          exact strtol_madd code strtol h h_sym d nptr str R h_len start b neg
            h_mem k hk' hdig'
            (limCutoff_lt _ _ _ _ hge (by omega)) _ _ _
        · intro hne
          have e : digitsVal str start b k = (strtolMax neg) / b := by
            have := congrArg BitVec.toNat (show
              (UInt64.ofNat (digitsVal str start b k)).toBitVec =
                (UInt64.ofNat ((strtolMax neg) / b)).toBitVec by
              exact eq_of_not_sub_ne_zero _ _ hne)
            simpa [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hV (strtolMax_lt neg)),
                Nat.mod_eq_of_lt hq] using this
          instr "cmp w5, w7" at strtol + 0x128
          instr "b.gt 158 <strtol+0x158>" at strtol + 0x12c
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [h_sym]
            refine strtol_ovf code strtol h h_sym d nptr str R h_len start b neg
                h_mem k hk' hdig' ?_ _ _ _ _ _
            show strtolMax neg < digitsVal str start b k * b + _
            rw [e]
            exact limCutoff_eq_gt _ _ _ hgt
          · intro hgt
            simp only [extract_ofNat64] at hgt
            rw [cmp_gt_iff _ _ (by omega) (by omega)] at hgt
            rw [show strtol + 300 + 4 = strtol + 0x130 by bv_decide]
            refine strtol_madd code strtol h h_sym d nptr str R h_len start b
                neg
                h_mem k hk' hdig' ?_ _ _ _
            show digitsVal str start b k * b + _ ≤ strtolMax neg
            rw [e]
            exact limCutoff_eq_le _ _ _ (by omega)
    · simp only [hls, decide_false, Bool.false_eq_true, ↓reduceIte]
      instr "b.eq 158 <strtol+0x158>" at strtol + 0x11c
      · intro heq
        rw [h_sym]
        refine strtol_ovf code strtol h h_sym d nptr str R h_len start b neg
            h_mem k hk' hdig' ?_ _ _ _ _ _
        show strtolMax neg < digitsVal str start b k * b + _
        by_cases h6 : x6 = 0xffffffff
        · rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, hV, -⟩
          · exact absurd h6 (by decide)
          · exact absurd h6 (by decide)
          · have := Nat.le_mul_of_pos_right (digitsVal str start b k) hb1
            omega
        · obtain ⟨hV, rfl⟩ := hsmall h6
          simp only [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hV (strtolMax_lt neg)),
                Nat.mod_eq_of_lt hq] at hls
          exact limCutoff_gt _ _ _ _ (by omega) (by omega)
      · intro heq
        exact absurd (by decide) heq

/-- `strtol` from `strtol + 0xc4`, which computes the limit (`lim`)
`strtolMax neg` and the base. -/
theorem strtol_lim [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (d : MachineData) (b : Nat) (neg : Bool) (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_x9 : d.regs.X9 = boolReg neg) :
    Eventually code.stepWp (fun s => s = ⟨{ d with
      regs := { d.regs with
        X5 := .ofNat (strtolMax neg)
        X10 := boolReg neg
        X11 := .ofNat b } }, strtol + 0xd4⟩)
    ⟨d, strtol + 0xc4⟩ := by
  instr "sxtw x10, w9" at strtol + 0xc4
  instr "sxtw x11, w2" at strtol + 0xc8
  instr "mov x5, #0x7fffffffffffffff" at strtol + 0xcc
  instr "add x5, x10, x5" at strtol + 0xd0
  refine .done _ ?_
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, ge_iff_le,
    Nat.zero_le, ↓reduceIte, BitVec.ushiftRight_zero, h_x2, h_x9, sext_ofNat32
        b (by omega), sxtw_boolReg,
    add_strtolMax]
  rw [show strtol + 208 + 4 = strtol + 0xd4 by bv_decide]
  state_eq

/-- `strtol` from `strtol + 0xd4`, which computes the cutoff (`cut`) and the
cut limit for the limit `M`. -/
theorem strtol_cut [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (d : MachineData) (b M : Nat) (hM : M < 2 ^ 64) (hb1 : 1 ≤ b)
    (hb : b ≤ 36)
    (h_x5 : d.regs.X5 = .ofNat M) (h_x11 : d.regs.X11 = .ofNat b) :
    Eventually code.stepWp (fun s => s = ⟨{ d with
      regs := { d.regs with
        X0 := 0
        X6 := 0
        X7 := .ofNat (M % b)
        X12 := .ofNat (M / b) } }, strtol + 0xe4⟩)
    ⟨d, strtol + 0xd4⟩ := by
  instr "mov w6, #0x0" at strtol + 0xd4
  instr "mov x0, #0x0" at strtol + 0xd8
  instr "udiv x12, x5, x11" at strtol + 0xdc
  instr "msub w7, w12, w11, w5" at strtol + 0xe0
  refine .done _ ?_
  simp only [h_x5, h_x11, UInt64.toBitVec_ofNat', udiv_limCutoff M b hM hb1 hb,
    msub_limCutlim M b hb1 hb]
  rw [show strtol + 224 + 4 = strtol + 0xe4 by bv_decide]
  state_eq

/-- The digit loop of `strtol`, from `strtol + 0xc4` to `strtol + 0x160`.
-/
theorem strtol_digits [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (nptr : UInt64) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (start b : Nat) (neg : Bool) (h_start : start ≤ str.length) (hb1 : 1 ≤ b)
        (hb : b ≤ 36)
    (h_x2 : d.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 b)
    (h_x3 : d.regs.X3 = ldrbReg (byteAt str start))
    (h_x4 : d.regs.X4 = nptr + .ofNat (start + 1))
    (h_x9 : d.regs.X9 = boolReg neg)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At nptr.toBitVec) ⋆ R) :
    Eventually code.stepWp (strtolDigitsPost strtol d nptr str start b neg)
    ⟨d, strtol + 0xc4⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  refine eventually_trans _ _ _ _ (strtol_lim code strtol h d b neg hb h_x2
    h_x9) ?_
  rintro _ rfl
  refine eventually_trans _ _ _ _ (strtol_cut code strtol h _ b (strtolMax neg)
    (strtolMax_lt neg) hb1 hb rfl rfl) ?_
  rintro _ rfl
  refine loop_rule (measure fun k => str.length + 1 - k).wf
    (strtolDigitsInv strtol d nptr str start b neg) _
    0 _ ⟨rfl, by omega, fun _ h => absurd h
      (Nat.not_lt_zero _),
      ?x0i, ?x5i, ?x6i, ?sti, ?acci, ?eqi⟩ ?_
  case eqi =>
    rw [Nat.add_zero, ← h_x3, ← h_x4]
  case acci => exact .inl ⟨rfl, rfl, by decide⟩
  rintro k ⟨d', pc⟩ ⟨rfl, hk, hdig, x0, x5, x6, st, hacc, rfl⟩
  instr "sub w5, w3, #0x30" at strtol + 0xe4
  instr "and x5, x5, #0xff" at strtol + 0xe8
  instr "cmp w5, #0x9" at strtol + 0xec
  instr "b.ls 10c <strtol+0x10c>" at strtol + 0xf0
  · intro hA
    rw [h_sym]
    refine strtol_digit code strtol h h_sym d nptr str R h_len start b neg hb1
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
    instr "sub w5, w3, #0x41" at strtol + 0xf4
    instr "and w5, w5, #0xff" at strtol + 0xf8
    instr "cmp w5, #0x19" at strtol + 0xfc
    instr "b.hi 140 <strtol+0x140>" at strtol + 0x100
    · intro hB
      rw [h_sym]
      instr "sub w5, w3, #0x61" at strtol + 0x140
      instr "and w5, w5, #0xff" at strtol + 0x144
      instr "cmp w5, #0x19" at strtol + 0x148
      instr "b.hi 160 <strtol+0x160>" at strtol + 0x14c
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
          (.inr (strtol_stop _ _ _ _ _ _ _ _ hk hdig hge _ _ _ _ hacc _))
      · intro hC
        instr "sub w5, w3, #0x57" at strtol + 0x150
        instr "b 108 <strtol+0x108>" at strtol + 0x154
        rw [h_sym]
        instr "and x5, x5, #0xff" at strtol + 0x108
        rw [show strtol + 264 + 4 = strtol + 0x10c by bv_decide]
        refine strtol_digit code strtol h h_sym d nptr str R h_len start b neg
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
      instr "sub w5, w3, #0x37" at strtol + 0x104
      instr "and x5, x5, #0xff" at strtol + 0x108
      rw [show strtol + 264 + 4 = strtol + 0x10c by bv_decide]
      refine strtol_digit code strtol h h_sym d nptr str R h_len start b neg hb1
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

/-- The state of `strtol` at `strtol + 0xc4`, after the prefix (white
space, sign and `0x`), when the digits start at index `start` and the base
is `b`. -/
def strtolPrefixPost (strtol : Int64) (s0 : MachineData) (str : List UInt8)
    (start b : Nat) (s : MachineState) : Prop :=
  s.pc = strtol + 0xc4 ∧ ∃ x0 x2 x5 x6 st,
  x2.toBitVec.extractLsb' 0 32 = .ofNat 32 b ∧
  s.data = { s0 with
    regs := { s0.regs with
      X0 := x0
      X2 := x2
      X3 := ldrbReg (byteAt str start)
      X4 := s0.regs.X0 + .ofNat (start + 1)
      X5 := x5
      X6 := x6
      X8 := s0.regs.X0
      X9 := boolReg (strtoNeg str) }
    status := st }

/-- `strtol` from `strtol + 0xb0`, which picks the base if there is no
`0x` prefix and the base is 0 (`b0`) or 16. -/
theorem strtol_b0 [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str : List UInt8)
    (base : Nat) (hbase : base = 0 ∨ base = 16)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 x5 x6 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtolPrefixPost strtol s0 str (strtoPos str)
      (strtoBaseNoHex str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (strtoPos str))
        X4 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X5 := x5
        X6 := x6
        X8 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtol + 0xb0⟩ := by
  instr "cbnz w2, 94 <strtol+0x94>" at strtol + 0xb0
  · intro hnz
    rw [h_x2] at hnz
    have h16 : base = 16 := by
      rcases hbase with rfl | rfl
      · exact absurd rfl hnz
      · rfl
    subst h16
    rw [h_sym]
    instr "mov w2, #0x10" at strtol + 0x94
    instr "b c4 <strtol+0xc4>" at strtol + 0x98
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
    instr "cmp w3, #0x30" at strtol + 0xb4
    instr "mov w2, #0xa" at strtol + 0xb8
    instr "mov w0, #0x8" at strtol + 0xbc
    instr "csel w2, w2, w0, ne" at strtol + 0xc0
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

/-- `strtol` from `strtol + 0x8c`, which skips a `0x` prefix (`hex`) that
starts at index `P`. -/
theorem strtol_hex [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str : List UInt8) (P : Nat)
    (x0 x3 x5 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtolPrefixPost strtol s0 str (P + 2) 16)
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := x3
        X4 := s0.regs.X0 + .ofNat (P + 1)
        X5 := x5
        X6 := ldrbReg (byteAt str (P + 2))
        X8 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtol + 0x8c⟩ := by
  instr "add x4, x4, #0x2" at strtol + 0x8c
  instr "mov w3, w6" at strtol + 0x90
  instr "mov w2, #0x10" at strtol + 0x94
  instr "b c4 <strtol+0xc4>" at strtol + 0x98
  refine .done _ ⟨by rw [h_sym], x0, ?x2h, x5, ?x6h, st, ?exth, ?eqh⟩
  case eqh =>
    simp only [ldrbReg]
    congr 2 <;> first | rfl | uint64_eq
  case exth => rfl

/-- `strtol` from `strtol + 0x44` to `strtol + 0xc4`, through the prefix
(the `0x` and the choice of the base). -/
theorem strtol_prefix [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R)
    (base : Nat) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (x0 : UInt64) (st : StatusFlags) :
    Eventually code.stepWp (strtolPrefixPost strtol s0 str (strtoStart str base)
      (strtoBase str base))
    ⟨{ s0 with
      regs := { s0.regs with
        X0 := x0
        X3 := ldrbReg (byteAt str (strtoPos str))
        X4 := s0.regs.X0 + .ofNat (strtoPos str + 1)
        X5 := 0x100002700
        X8 := s0.regs.X0
        X9 := boolReg (strtoNeg str) }
      status := st }, strtol + 0x44⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "tst w2, #0xffffffef" at strtol + 0x44
  instr "b.ne c4 <strtol+0xc4>" at strtol + 0x48
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
    instr "cmp w3, #0x30" at strtol + 0x4c
    instr "b.ne b0 <strtol+0xb0>" at strtol + 0x50
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
      exact strtol_b0 code strtol h h_sym s0 str base hbase h_x2 _ _ _ _
    · intro h0
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.not_eq_false] at h0
      rw [ldrbReg, ldrb_cmp_imm_eq_iff] at h0
      simp at h0
      have hb0 : byteAt str (strtoPos str) = 48 := UInt8.toNat_inj.mp h0
      have hp0 := lt_of_byteAt_ne_zero (by rw [hb0]; decide)
      instr "ldrb w0, [x4]" at strtol + 0x54
      load_byte h_mem hw
      instr "and w0, w0, #0xffffffdf" at strtol + 0x58
      instr "and w0, w0, #0xff" at strtol + 0x5c
      instr "cmp w0, #0x58" at strtol + 0x60
      instr "b.ne b0 <strtol+0xb0>" at strtol + 0x64
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
        exact strtol_b0 code strtol h h_sym s0 str base hbase h_x2 _ _ _ _
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
        instr "ldrb w6, [x4, #1]" at strtol + 0x68
        simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat',
          BitVec.add_assoc,
          ofNat_add_one64]
        load_byte h_mem hw
        instr "sub w0, w6, #0x30" at strtol + 0x6c
        instr "and w0, w0, #0xff" at strtol + 0x70
        instr "cmp w0, #0x36" at strtol + 0x74
        instr "b.hi b0 <strtol+0xb0>" at strtol + 0x78
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
          exact strtol_b0 code strtol h h_sym s0 str base hbase h_x2 _ _ _ _
        · intro hhi
          instr "mov x5, #0x7e0000007e0000" at strtol + 0x7c
          instr "movk x5, #0x3ff" at strtol + 0x80
          instr "lsr x0, x5, x0" at strtol + 0x84
          instr "tbz w0, #0, b0 <strtol+0xb0>" at strtol + 0x88
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
            exact strtol_b0 code strtol h h_sym s0 str base hbase h_x2 _ _ _ _
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
            rw [← e2, show strtol + 136 + 4 = strtol + 0x8c by bv_decide]
            exact strtol_hex code strtol h h_sym s0 str _ _ _ _ _

/-- The value that `strtol` returns for the accumulated value `V` of the
digits and the sign `neg`: `LONG_MIN` or `LONG_MAX` if `V` exceeds
`strtolMax neg`. -/
def strtolRet (V : Nat) (neg : Bool) : UInt64 :=
  if strtolMax neg < V then (if neg then 0x8000000000000000
    else 0x7fffffffffffffff)
  else if neg then -(.ofNat V) else .ofNat V

/-- The state after the epilogue (`epi`) of `strtol`, after `ret`, for the
state `d` at the start of the epilogue: `x0` is `r`, and if `endptr`
(`x1`) is not NULL, `*endptr` is `e` in the frame `R`. -/
def strtolEpiPost (d : MachineData) (r e : UInt64) (R : DataMem → Prop)
    (s : MachineState) : Prop :=
  s.pc = d.regs.X30.toInt64 ∧ ∃ x8 x10 st m,
  s.data = { d with
    regs := { d.regs with X0 := r, X8 := x8, X10 := x10 }
    status := st
    dmem := m } ∧
  (d.regs.X1 = 0 ∧ m = d.dmem ∨
    d.regs.X1 ≠ 0 ∧ m =⋆ Eq (e.toBytes.At d.regs.X1.toBitVec) ⋆ R)

/-- `strtol` from `strtol + 0x18c`, which stores `x8` to `*endptr` and
returns. -/
theorem strtol_str [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol) (d : MachineData)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ m, s.data = { d with dmem := m } ∧
      m =⋆ Eq (d.regs.X8.toBytes.At d.regs.X1.toBitVec) ⋆ R)
    ⟨d, strtol + 0x18c⟩ := by
  instr "str x8, [x1]" at strtol + 0x18c
  simp (disch := first | rfl | simp [h_old]) only
    [MachineData.store_of_sep64_zero h_mem, Effects.All, MemWidth.bytes]
  have hL := Mem.storeInt_sep _ 8 _ _ _ ⟨h_mem, h_old⟩
    d.regs.X8.toBitVec.toInt
  rw [show Int.toBytes 8 d.regs.X8.toBitVec.toInt = d.regs.X8.toBytes
    from rfl] at hL
  instr "b 174 <strtol+0x174>" at strtol + 0x190
  rw [h_sym]
  instr "ret" at strtol + 0x174
  exact .done _ ⟨rfl, _, rfl, hL⟩

/-- `strtolEpiPost` holds for any state with the same registers except `x0`
and `x10`. -/
theorem strtolEpiPost_of {d d' : MachineData} {r e : UInt64}
    {R : DataMem → Prop} {s : MachineState}
    (hd : ∃ a c, d'.regs = { d.regs with X0 := a, X10 := c })
    (hm : d'.dmem = d.dmem)
    (h : strtolEpiPost d' r e R s) : strtolEpiPost d r e R s := by
  obtain ⟨a, c, ha⟩ := hd
  rcases d' with ⟨regs', st', dm'⟩
  simp only at ha hm
  subst ha hm
  obtain ⟨hpc, x8, x10, st, m, hs, hm⟩ := h
  exact ⟨hpc, x8, x10, st, m, hs, hm⟩

/-- `strtol` from `strtol + 0x188`, which stores the pointer after the
digits to `*endptr` and returns. -/
theorem strtol_188 [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol) (d : MachineData) (q : UInt64)
    (h_x4 : d.regs.X4 = q + 1) (hX1 : d.regs.X1 ≠ 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (strtolEpiPost d d.regs.X0 q R)
      ⟨d, strtol + 0x188⟩ := by
  instr "sub x8, x4, #0x1" at strtol + 0x188
  rw [show strtol + 392 + 4 = strtol + 0x18c by bv_decide]
  refine eventually_weaken _ _ _ _ ?_
    (strtol_str code strtol h h_sym _ old R h_old h_mem)
  rintro s ⟨hpc, m, hs, hm⟩
  refine ⟨hpc, ⟨d.regs.X4.toBitVec - 1⟩, d.regs.X10, d.status, m,
    hs.trans rfl, .inr ⟨hX1, ?_⟩⟩
  have hq : (⟨d.regs.X4.toBitVec - 1⟩ : UInt64) = q := by
    rw [h_x4]; apply UInt64.toBitVec_inj.mp; simp [BitVec.add_sub_cancel]
  rw [← hq]
  exact hm

/-- `strtol` from `strtol + 0x180`, which stores to `*endptr` if it is not
NULL and returns. -/
theorem strtol_180 [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol) (d : MachineData) (n : Nat)
    (q : UInt64) (h_x4 : d.regs.X4 = q + 1)
    (h_w6 : BitVec.extractLsb' 0 32 d.regs.X6.toBitVec = 0 ↔ n = 0)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (strtolEpiPost d d.regs.X0 (strtoEnd n d.regs.X8 q) R)
      ⟨d, strtol + 0x180⟩ := by
  instr "cbz x1, 174 <strtol+0x174>" at strtol + 0x180
  · intro hz
    rw [h_sym]
    instr "ret" at strtol + 0x174
    exact .done _ ⟨rfl, d.regs.X8, d.regs.X10, d.status, d.dmem, rfl,
      .inl ⟨by simpa [← UInt64.toBitVec_inj] using hz, rfl⟩⟩
  · intro hz
    have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
    instr "cbz w6, 18c <strtol+0x18c>" at strtol + 0x184
    · intro h6
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtol_str code strtol h h_sym d old R h_old (h_mem hX1))
      rintro s ⟨hpc, m, hs, hm⟩
      refine ⟨hpc, d.regs.X8, d.regs.X10, d.status, m, hs.trans rfl,
        .inr ⟨hX1, ?_⟩⟩
      simp only [strtoEnd, h_w6.mp h6, ↓reduceIte]
      exact hm
    · intro h6
      have hn : ¬n = 0 := fun h0 => h6 (h_w6.mpr h0)
      simp only [strtoEnd, hn, ↓reduceIte]
      rw [show strtol + 388 + 4 = strtol + 0x188 by bv_decide]
      exact strtol_188 code strtol h h_sym d q h_x4 hX1 old R h_old
        (h_mem hX1)

/-- `neg` and `eor` (exclusive or) compute `LONG_MIN` or `LONG_MAX` from the
flag `neg`. -/
theorem eor_strtolRet (neg : Bool) (V : Nat) (hv : strtolMax neg < V)
    (c : BitVec 64) (hc : c.toNat = 2 ^ 63 - 1) :
    (⟨(0#64 - (boolReg neg).toBitVec) ^^^ c⟩ : UInt64) = strtolRet V neg := by
  have e : c = BitVec.ofNat 64 (2 ^ 63 - 1) :=
    BitVec.eq_of_toNat_eq (by simp [hc])
  subst e
  simp only [strtolRet, hv, ↓reduceIte]
  cases neg <;> decide

/-- The epilogue (`epi`) of `strtol`, from `strtol + 0x160`, after `n`
digits with the value `V`, where `q` is the pointer after the digits. -/
theorem strtol_epi [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (d : MachineData) (neg : Bool) (V n : Nat) (q x0 x6 : UInt64)
    (hacc : strtolAcc (strtolMax neg) V n x0 x6) (hV0 : n = 0 → V = 0)
    (h_x0 : d.regs.X0 = x0) (h_x4 : d.regs.X4 = q + 1)
    (h_x6 : d.regs.X6 = x6) (h_x9 : d.regs.X9 = boolReg neg)
    (h_x10 : d.regs.X10 = boolReg neg)
    (old : List UInt8) (R : DataMem → Prop) (h_old : old.length = 8)
    (h_mem : d.regs.X1 ≠ 0 → d.dmem =⋆ Eq (old.At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp
      (strtolEpiPost d (strtolRet V neg) (strtoEnd n d.regs.X8 q) R)
      ⟨d, strtol + 0x160⟩ := by
  instr "cmn w6, #0x1" at strtol + 0x160
  instr "b.ne 178 <strtol+0x178>" at strtol + 0x164
  · intro heq
    rw [h_x6] at heq
    have hacc' : n = 0 ∧ x0 = 0 ∧ x6 = 0 ∨
        0 < n ∧ V ≤ strtolMax neg ∧ x0 = .ofNat V ∧ x6 = 1 := by
      rcases hacc with h1 | h2 | ⟨-, -, rfl⟩
      · exact .inl h1
      · exact .inr h2
      · exact absurd heq (by decide)
    have hret : strtolRet V neg = if neg then -x0 else x0 := by
      rcases hacc' with ⟨h0, rfl, -⟩ | ⟨-, hv, rfl, -⟩
      · cases hV0 h0; cases neg <;> simp [strtolRet]
      · simp [strtolRet, show ¬strtolMax neg < V by omega]
    have h_w6 : BitVec.extractLsb' 0 32 d.regs.X6.toBitVec = 0 ↔ n = 0 := by
      rw [h_x6]
      rcases hacc' with ⟨h0, -, rfl⟩ | ⟨hk, -, -, rfl⟩
      · simp only [h0, iff_true]; decide
      · simp only [show ¬n = 0 by omega, iff_false]; decide
    rw [hret, ← h_x0, h_sym]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte]
      instr "cbz w9, 180 <strtol+0x180>" at strtol + 0x178
      · intro hz
        rw [h_sym]
        refine eventually_weaken _ _ _ _ ?_
          (strtol_180 code strtol h h_sym _ n q (by exact h_x4)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => strtolEpiPost_of ⟨_, _, rfl⟩ rfl hs
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
    · simp only [↓reduceIte]
      instr "cbz w9, 180 <strtol+0x180>" at strtol + 0x178
      · intro hz
        rw [h_x9] at hz
        exact absurd hz (by decide)
      · intro hz
        instr "neg x0, x0" at strtol + 0x17c
        rw [show strtol + 380 + 4 = strtol + 0x180 by bv_decide,
          show -d.regs.X0 = ⟨0#64 - d.regs.X0.toBitVec⟩ from
            UInt64.toBitVec_inj.mp (by simp)]
        refine eventually_weaken _ _ _ _ ?_
          (strtol_180 code strtol h h_sym _ n q (by exact h_x4)
            (by exact h_w6) old R h_old (by exact h_mem))
        exact fun s hs => strtolEpiPost_of ⟨_, _, rfl⟩ rfl hs
  · intro heq
    rw [h_x6] at heq
    rcases hacc with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨hk, hv, rfl⟩
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    have hend : strtoEnd n d.regs.X8 q = q := by
      simp only [strtoEnd, show ¬n = 0 by omega, ↓reduceIte]
    rw [hend]
    instr "neg x10, x10" at strtol + 0x168
    instr "eor x0, x10, #0x7fffffffffffffff" at strtol + 0x16c
    rw [h_x10, eor_strtolRet neg V hv _ (by decide)]
    instr "cbnz x1, 188 <strtol+0x188>" at strtol + 0x170
    · intro hz
      have hX1 : d.regs.X1 ≠ 0 := fun h' => hz (by simp [h'])
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_
        (strtol_188 code strtol h h_sym _ q (by exact h_x4) (by exact hX1) old
          R h_old (by exact h_mem hX1))
      exact fun s hs => strtolEpiPost_of ⟨_, _, rfl⟩ rfl hs
    · intro hz
      instr "ret" at strtol + 0x174
      exact .done _ ⟨rfl, d.regs.X8, _, _, d.dmem, rfl,
        .inl ⟨by simpa [← UInt64.toBitVec_inj] using hz, rfl⟩⟩

/-- The value (`val`) that `strtol` returns for the string `str` and the
base `base`: the value of the digits, negated if there is a `-`, or
`LONG_MIN` or `LONG_MAX` if that overflows. -/
def strtolVal (str : List UInt8) (base : Nat) : UInt64 :=
  strtolRet (digitsVal str (strtoStart str base) (strtoBase str base)
    (strtoDigits str base)) (strtoNeg str)

/-- `strtol` for both a NULL and a non-NULL `endptr` (general, `gen`). -/
theorem strtol_gen [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
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
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtolVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11
          X12 := x12 }
        status := st
        dmem := m } ∧
      (s0.regs.X1 = 0 ∧ m = s0.dmem ∨ s0.regs.X1 ≠ 0 ∧
        m =⋆ Eq ((s0.regs.X0 + .ofNat (strtoEndOfs str base)).toBytes.At
          s0.regs.X1.toBitVec) ⋆ R'))
    ⟨s0, strtol⟩ := by
  obtain ⟨hb1, hb36⟩ := strtoBase_range str base h_base
  refine eventually_trans _ _ _ _
    (strtol_ws code strtol h h_sym s0 str R h_len h_mem) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, st, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtol_prefix code strtol h h_sym s0 str
    R h_len h_mem base h_base h_x2 x0 st) ?_
  rintro ⟨d, pc⟩ ⟨hpc, x0, x2, x5, x6, st, hx2, hs⟩
  simp only at hpc hs
  subst hpc hs
  refine eventually_trans _ _ _ _ (strtol_digits code strtol h h_sym _
    s0.regs.X0 str R h_len _ _ _ (strtoStart_le str base) hb1 hb36 hx2 rfl rfl
    rfl h_mem) ?_
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
  refine eventually_weaken _ _ _ _ ?_ (strtol_epi code strtol h h_sym _
    (strtoNeg str) _ _ _ x0 x6 hacc (fun h0 => by rw [h0]; rfl) rfl
    (by exact hx4) rfl rfl rfl old R' h_old (by exact h_end))
  rintro s ⟨hpc, x8, x10, st', m, hs, hm⟩
  refine ⟨hpc, x2, x3, _, x5, x6, _, x8, _, x10, _, _, st', m, hs.trans rfl,
    hm.imp id fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  rw [← hE]
  exact h2

/-- `strtol (nptr, endptr, base)` with `nptr` in `x0` pointing to `str`,
a non-NULL `endptr` in `x1`, and `base ≤ 36` in `w2`. It returns
`strtolVal str base`, and stores `nptr + strtoEndOfs str base` to
`*endptr`. -/
theorem strtol_spec [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str old : List UInt8) (base : Nat)
    (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 ≠ 0) (h_old : old.length = 8)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
      (Eq (old.At s0.regs.X1.toBitVec) ⋆ R)) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 st m,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtolVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11
          X12 := x12 }
        status := st
        dmem := m } ∧
      m =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
        (Eq ((s0.regs.X0 + .ofNat (strtoEndOfs str base)).toBytes.At
          s0.regs.X1.toBitVec) ⋆ R))
    ⟨s0, strtol⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtol_gen code strtol h h_sym s0 str
    old base _ _ h_len h_base h_x2 h_old h_mem
    (fun _ => by rw [← sep_swap]; exact h_mem))
  rintro s ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, st, m, hs,
    ⟨h1, -⟩ | ⟨-, hm⟩⟩
  · exact absurd h1 h_x1
  · refine ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, st, m, hs, ?_⟩
    rw [sep_swap]
    exact hm

/-- `strtol (nptr, NULL, base)` with `nptr` in `x0` pointing to `str` and
`base ≤ 36` in `w2`. It returns `strtolVal str base`. -/
theorem strtol_spec_null [Labels] (code : Code) (strtol : Int64)
    (h : Loaded code strtol strtol_o)
    (h_sym : label "strtol" = strtol)
    (s0 : MachineData) (str : List UInt8) (base : Nat) (R : DataMem → Prop)
    (h_len : str.length < 2 ^ 64) (h_base : base ≤ 36)
    (h_x2 : s0.regs.X2.toBitVec.extractLsb' 0 32 = BitVec.ofNat 32 base)
    (h_x1 : s0.regs.X1 = 0)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      ∃ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 st,
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtolVal str base
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7
          X8 := x8
          X9 := x9
          X10 := x10
          X11 := x11
          X12 := x12 }
        status := st })
    ⟨s0, strtol⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (strtol_gen code strtol h h_sym s0 str
    (List.replicate 8 0) base R R h_len h_base h_x2 (by simp) h_mem
    (fun h1 => absurd h_x1 h1))
  rintro s ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, st, m, hs,
    ⟨-, rfl⟩ | ⟨h1, -⟩⟩
  · exact ⟨hpc, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, st, hs⟩
  · exact absurd h_x1 h1
