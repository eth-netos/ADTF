module

import ADTF.AtfLibc.Listing.strtok_r_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strtok_r` from TF-A's `libc/strtok.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strtok_r` in ATF's `strtok.o`. -/
def strtok_r_o : List Instr := objdumpAArch64(strtok_r_o_dump)

/-- The number of delimiters before the token that `strtok_r` returns for
the string `str` (without its terminating 0) and the delimiters `delim`. -/
def strtokSpan (str delim : List UInt8) : Nat :=
  (str.takeWhile (· ∈ delim)).length

/-- The length of the token that `strtok_r` returns. -/
def strtokTok (str delim : List UInt8) : Nat :=
  ((str.drop (strtokSpan str delim)).takeWhile (· ∉ delim)).length

/-- Whether `strtok_r` reaches the end of the string: when it consists only of
delimiters, or when the token ends at the end of the string. -/
def strtokEnd (str delim : List UInt8) : Prop :=
  strtokSpan str delim = str.length ∨
    strtokSpan str delim + strtokTok str delim = str.length

instance (str delim : List UInt8) : Decidable (strtokEnd str delim) := by
  unfold strtokEnd; infer_instance

/-- The return value of `strtok_r` for a string at `p`: the token's address,
or 0 if there is no token. -/
def strtokRet (p : UInt64) (str delim : List UInt8) : UInt64 :=
  if strtokSpan str delim = str.length then 0
  else p + .ofNat (strtokSpan str delim)

/-- The pointer that `strtok_r` stores into its third argument: the address
after the delimiter that ends the token, or 0 if the end of the string was
reached. -/
def strtokLast (p : UInt64) (str delim : List UInt8) : UInt64 :=
  if strtokEnd str delim then 0
  else p + .ofNat (strtokSpan str delim + strtokTok str delim + 1)

/-- The string after `strtok_r`, with its terminating 0: the delimiter that
ends the token, if any, is overwritten with 0. -/
def strtokStr (str delim : List UInt8) : List UInt8 :=
  if strtokEnd str delim then str ++ [0]
  else (str ++ [0]).set (strtokSpan str delim + strtokTok str delim) 0

/-- The loops of `strtok_r` that scan the token, entered at `strtok_r + 0x4c`
after the first byte `str[i]` of the token. -/
theorem strtok_r_tok [Labels] (code : Code) (strtok_r : Int64)
    (h : Loaded code strtok_r strtok_r_o)
    (h_sym : label "strtok_r" = strtok_r)
    (d : MachineData) (p : UInt64) (str delim : List UInt8)
    {l : UInt64} (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_dnz : 0 ∉ delim) (h_len : str.length < 2 ^ 64)
    (h_dlen : delim.length < 2 ^ 64) (i : Nat) (hi : i < str.length)
    (hspan : strtokSpan str delim = i) (hc : str[i] ∉ delim)
    (h_x3 : d.regs.X3 = p + .ofNat (i + 1))
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At p.toBitVec) ⋆
      (Eq ((delim ++ [0]).At d.regs.X1.toBitVec) ⋆
        (Eq ((UInt64.toBytes l).At d.regs.X2.toBitVec) ⋆ R))) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ x3 x4 x5 x6 x7 st m,
      (m =⋆ Eq ((strtokStr str delim).At p.toBitVec) ⋆
        (Eq ((delim ++ [0]).At d.regs.X1.toBitVec) ⋆
          (Eq ((strtokLast p str delim).toBytes.At d.regs.X2.toBitVec) ⋆
            R))) ∧
      s.data = { d with
        regs := { d.regs with
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7 }
        status := st
        dmem := m })
    ⟨d, strtok_r + 0x4c⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  have hdw : (delim ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  have hD := h_mem
  rw [Std.ExtHashMap.sep_comm_l] at hD
  have hL := h_mem
  rw [show ∀ a b c (r : DataMem → Prop), a ⋆ (b ⋆ (c ⋆ r)) =
    c ⋆ (a ⋆ (b ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL
  refine loop_rule (measure fun q => str.length + 1 - q).wf
    (fun q s => s.pc = strtok_r + 0x4c ∧ i < q ∧ q ≤ str.length ∧
      (∀ j (_ : i ≤ j) (_ : j < q) (hj : j < str.length), str[j] ∉ delim) ∧
      ∃ x4 x5 x6 x7 st,
      s.data = { d with
        regs := { d.regs with
          X3 := p + .ofNat q
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7 }
        status := st })
    _ (i + 1) _ ⟨rfl, Nat.lt_succ_self _, hi, fun j hj hj' _ => ?_,
      d.regs.X4, d.regs.X5, d.regs.X6, d.regs.X7, d.status,
      by rw [← h_x3]⟩ ?_
  · obtain rfl : j = i := by omega
    exact hc
  rintro q ⟨d', pc⟩ ⟨rfl, hiq, hq, hsq, x4, x5, x6, x7, st, rfl⟩
  instr "mov x7, x3" at strtok_r + 0x4c
  instr "ldrb w6, [x3], #1" at strtok_r + 0x50
  load_byte h_mem hw
  instr "mov x5, x1" at strtok_r + 0x54
  refine loop_rule (measure fun k => delim.length + 1 - k).wf
    (fun k s => s.pc = strtok_r + 0x58 ∧ k ≤ delim.length ∧
      (∀ m (_ : m < k) (hm : m < delim.length),
        delim[m] ≠ (str ++ [0])[q]'(by simp; omega)) ∧ ∃ x4 st,
      s.data = { d with
        regs := { d.regs with
          X3 := p + .ofNat (q + 1)
          X4 := x4
          X5 := d.regs.X1 + .ofNat k
          X6 := ⟨BitVec.zeroExtend 64
            (BitVec.zeroExtend 32 ((str ++ [0])[q]'(by simp; omega)).toBitVec)⟩
          X7 := p + .ofNat q }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), _, _, by state_eq⟩ ?_
  rintro k ⟨d', pc⟩ ⟨rfl, hk, hne, x4, st', rfl⟩
  instr "ldrb w4, [x5], #1" at strtok_r + 0x58
  load_byte hD hdw
  instr "cmp w6, w4" at strtok_r + 0x5c
  instr "b.ne 48 <strtok_r+0x48>" at strtok_r + 0x60
  · intro hc'
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hc'
    rw [ldrb_cmp_ldrb_eq_iff] at hc'
    rw [h_sym]
    instr "cbnz w4, 58 <strtok_r+0x58>" at strtok_r + 0x48
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      have hkl : k < delim.length := by
        refine Nat.lt_of_le_of_ne hk fun he => h_b ?_
        simp [he]
      refine .done _ (.inl ⟨k + 1, ?_, by rw [h_sym], hkl,
        fun m hm hm' => ?_, _, _, by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
        · exact hne m hm hm'
        · rw [List.getElem_append_left hm'] at hc'
          exact fun h => hc' h.symm
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      have hkl : k = delim.length := by
        refine Nat.le_antisymm hk (Nat.not_lt.mp fun hlt => h_dnz ?_)
        rw [List.getElem_append_left hlt] at h_b
        exact h_b ▸ List.getElem_mem hlt
      subst hkl
      have hql : q < str.length := by
        refine Nat.lt_of_le_of_ne hq fun he => hc' ?_
        simp [he]
      refine .done _ (.inr (.inl ⟨q + 1, ?_, by dsimp only; bv_decide,
        by omega, hql,
        fun j hj hj' hj'' => ?_, _, _, _, _, _, by state_eq⟩))
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact hsq j hj hj' hj''
        · intro hm
          obtain ⟨m, hm1, hm2⟩ := List.getElem_of_mem hm
          exact hne m hm1 hm1 (by rw [hm2, List.getElem_append_left hj''])
  · intro hc'
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      Decidable.not_not] at hc'
    rw [ldrb_cmp_ldrb_eq_iff] at hc'
    have htok : (∀ hq' : q < str.length, str[q] ∈ delim) →
        strtokTok str delim = q - i := by
      intro hq'
      unfold strtokTok
      rw [hspan]
      refine List.length_takeWhile_eq (by simp; omega) (fun j hj => ?_)
        (fun h' => ?_)
      · simp only [List.getElem_drop, decide_eq_true_eq]
        exact hsq (i + j) (by omega) (by omega) _
      · 
        simp only [List.getElem_drop, decide_eq_false_iff_not,
          Decidable.not_not]
        have := hq' (by simp at h'; omega)
        simpa [show i + (q - i) = q by omega] using this
    instr "cbz w6, 40 <strtok_r+0x40>" at strtok_r + 0x64
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      have hql : q = str.length := by
        refine Nat.le_antisymm hq (Nat.not_lt.mp fun hlt => h_nz ?_)
        rw [List.getElem_append_left hlt] at h_b
        exact h_b ▸ List.getElem_mem hlt
      have hend : strtokEnd str delim :=
        .inr (by rw [hspan, htok (fun h => absurd h (by omega))]; omega)
      rw [h_sym]
      instr "mov x3, #0x0" at strtok_r + 0x40
      instr "b 6c <strtok_r+0x6c>" at strtok_r + 0x44
      rw [h_sym]
      instr "str x3, [x2]" at strtok_r + 0x6c
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hL, Effects.All, MemWidth.bytes]
      have hL' := Mem.storeInt_sep _ 8 _ _ _ ⟨hL, UInt64.toBytes_length _⟩
        ((0 &&& 65535#64) <<< 0).toInt
      rw [show Int.toBytes 8 ((0 &&& 65535#64) <<< 0).toInt =
          (0 : UInt64).toBytes from rfl,
        show ∀ a b c (r : DataMem → Prop), c ⋆ (a ⋆ (b ⋆ r)) =
          a ⋆ (b ⋆ (c ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL'
      instr "b 30 <strtok_r+0x30>" at strtok_r + 0x70
      rw [h_sym]
      instr "ret" at strtok_r + 0x30
      refine .done _ (.inr (.inr
        ⟨rfl, ?x3, ?x4, ?x5, ?x6, ?x7, ?st, ?m, ?hm, ?hs⟩))
      case hs => state_eq
      case hm => simpa [strtokStr, strtokLast, hend] using hL'
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      have hql : q < str.length :=
        Nat.lt_of_le_of_ne hq fun he => h_b (by simp [he])
      have hkl : k < delim.length := by
        refine Nat.lt_of_le_of_ne hk fun he => h_b ?_
        rw [hc']
        simp [he]
      have hmem : str[q] ∈ delim := by
        rw [List.getElem_append_left hql, List.getElem_append_left hkl] at hc'
        exact hc' ▸ List.getElem_mem hkl
      have ht := htok (fun _ => hmem)
      have hend : ¬strtokEnd str delim := by
        unfold strtokEnd
        omega
      instr "strb wzr, [x7]" at strtok_r + 0x68
      store_byte h_mem
      have hz : (BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 0#64)).toInt =
          (0 : UInt8).toBitVec.toInt := by decide
      rw [hz]
      have hm' := Mem.storeInt_byte_sep _ _ q _ _ h_mem (by simp; omega) hw 0
      rw [show ∀ a b c (r : DataMem → Prop), a ⋆ (b ⋆ (c ⋆ r)) =
        c ⋆ (a ⋆ (b ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hm'
      instr "str x3, [x2]" at strtok_r + 0x6c
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hm', Effects.All, MemWidth.bytes]
      have hL' := Mem.storeInt_sep _ 8 _ _ _ ⟨hm', UInt64.toBytes_length _⟩
        (p + .ofNat (q + 1)).toBitVec.toInt
      rw [show Int.toBytes 8 (p + .ofNat (q + 1)).toBitVec.toInt =
          (p + .ofNat (q + 1)).toBytes from rfl,
        show ∀ a b c (r : DataMem → Prop), c ⋆ (a ⋆ (b ⋆ r)) =
          a ⋆ (b ⋆ (c ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL'
      instr "b 30 <strtok_r+0x30>" at strtok_r + 0x70
      rw [h_sym]
      instr "ret" at strtok_r + 0x30
      refine .done _ (.inr (.inr
        ⟨rfl, ?y3, ?y4, ?y5, ?y6, ?y7, ?st', ?m', ?hm', ?hs'⟩))
      case hs' => state_eq
      case hm' =>
        simpa [strtokStr, strtokLast, hend, hspan, ht,
          show i + (q - i) = q by omega] using hL'

/-- `strtok_r` from `strtok_r + 0x10`, with the string at `p` in `x3`. -/
theorem strtok_r_from [Labels] (code : Code) (strtok_r : Int64)
    (h : Loaded code strtok_r strtok_r_o)
    (h_sym : label "strtok_r" = strtok_r)
    (d : MachineData) (p : UInt64) (str delim : List UInt8)
    {l : UInt64} (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_dnz : 0 ∉ delim) (h_len : str.length < 2 ^ 64)
    (h_dlen : delim.length < 2 ^ 64) (h_x3 : d.regs.X3 = p)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At p.toBitVec) ⋆
      (Eq ((delim ++ [0]).At d.regs.X1.toBitVec) ⋆
        (Eq ((UInt64.toBytes l).At d.regs.X2.toBitVec) ⋆ R))) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ x3 x4 x5 x6 x7 st m,
      (m =⋆ Eq ((strtokStr str delim).At p.toBitVec) ⋆
        (Eq ((delim ++ [0]).At d.regs.X1.toBitVec) ⋆
          (Eq ((strtokLast p str delim).toBytes.At d.regs.X2.toBitVec) ⋆
            R))) ∧
      s.data = { d with
        regs := { d.regs with
          X0 := strtokRet p str delim
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7 }
        status := st
        dmem := m })
    ⟨d, strtok_r + 0x10⟩ := by
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  have hdw : (delim ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  have hD := h_mem
  rw [Std.ExtHashMap.sep_comm_l] at hD
  refine loop_rule (measure fun i => str.length + 1 - i).wf
    (fun i s => s.pc = strtok_r + 0x10 ∧ i ≤ str.length ∧
      (∀ j (_ : j < i) (hj : j < str.length), str[j] ∈ delim) ∧
      ∃ x0 x4 x5 x6 st,
      s.data = { d with
        regs := { d.regs with
          X0 := x0
          X3 := p + .ofNat i
          X4 := x4
          X5 := x5
          X6 := x6 }
        status := st })
    _ 0 _ ⟨rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _),
      d.regs.X0, d.regs.X4, d.regs.X5, d.regs.X6, d.status,
      by rw [← h_x3, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]⟩ ?_
  rintro i ⟨d', pc⟩ ⟨rfl, hi, hsp, x0, x4, x5, x6, st, rfl⟩
  instr "mov x0, x3" at strtok_r + 0x10
  instr "ldrb w4, [x3], #1" at strtok_r + 0x14
  load_byte h_mem hw
  instr "mov x6, x1" at strtok_r + 0x18
  refine loop_rule (measure fun j => delim.length + 1 - j).wf
    (fun j s => s.pc = strtok_r + 0x1c ∧ j ≤ delim.length ∧
      (∀ k (_ : k < j) (hk : k < delim.length),
        delim[k] ≠ (str ++ [0])[i]'(by simp; omega)) ∧ ∃ x5 st,
      s.data = { d with
        regs := { d.regs with
          X0 := p + .ofNat i
          X3 := p + .ofNat (i + 1)
          X4 := ⟨BitVec.zeroExtend 64
            (BitVec.zeroExtend 32 ((str ++ [0])[i]'(by simp; omega)).toBitVec)⟩
          X5 := x5
          X6 := d.regs.X1 + .ofNat j }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), _, _, by state_eq⟩ ?_
  rintro j ⟨d', pc⟩ ⟨rfl, hj, hne, x5, st', rfl⟩
  instr "ldrb w5, [x6], #1" at strtok_r + 0x1c
  load_byte hD hdw
  instr "cbnz w5, 34 <strtok_r+0x34>" at strtok_r + 0x20
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have hjl : j < delim.length := by
      refine Nat.lt_of_le_of_ne hj fun he => h_b ?_
      simp [he]
    rw [h_sym]
    instr "cmp w4, w5" at strtok_r + 0x34
    instr "b.ne 1c <strtok_r+0x1c>" at strtok_r + 0x38
    · intro hc
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hc
      rw [ldrb_cmp_ldrb_eq_iff] at hc
      refine .done _ (.inl ⟨j + 1, ?_, by rw [h_sym], hjl, fun k hk hk' => ?_,
        _, _, by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hne k hk hk'
        · rw [List.getElem_append_left hk'] at hc
          exact fun h => hc h.symm
    · intro hc
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Decidable.not_not] at hc
      rw [ldrb_cmp_ldrb_eq_iff, List.getElem_append_left hjl] at hc
      have hmem : (str ++ [0])[i]'(by simp; omega) ∈ delim :=
        hc ▸ List.getElem_mem hjl
      have hil : i < str.length := by
        refine Nat.lt_of_le_of_ne hi fun he => h_dnz ?_
        simp only [he, List.getElem_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem_cons_zero] at hmem
        exact hmem
      instr "b 10 <strtok_r+0x10>" at strtok_r + 0x3c
      refine .done _ (.inr (.inl ⟨i + 1, ?_, by rw [h_sym], hil,
        fun k hk hk' => ?_, _, _, _, _, _, by state_eq⟩))
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact hsp k hk hk'
        · rwa [List.getElem_append_left hk'] at hmem
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have hjl : j = delim.length := by
      refine Nat.le_antisymm hj (Nat.not_lt.mp fun hlt => h_dnz ?_)
      rw [List.getElem_append_left hlt] at h_b
      exact h_b ▸ List.getElem_mem hlt
    subst hjl
    have hnm : (str ++ [0])[i]'(by simp; omega) ∉ delim := by
      intro hm
      obtain ⟨k, hk, hk'⟩ := List.getElem_of_mem hm
      exact hne k hk hk hk'
    instr "cbnz w4, 4c <strtok_r+0x4c>" at strtok_r + 0x24
    · intro h_c
      rw [ldrb_eq_zero_iff] at h_c
      have hil : i < str.length :=
        Nat.lt_of_le_of_ne hi fun he => h_c (by simp [he])
      rw [List.getElem_append_left hil] at hnm
      have hspan : strtokSpan str delim = i :=
        List.length_takeWhile_eq (Nat.le_of_lt hil)
          (fun j hj => by simpa using hsp j hj (by omega))
          (fun _ => by simpa using hnm)
      have hret : strtokRet p str delim = p + .ofNat i := by
        simp only [strtokRet, hspan, Nat.ne_of_lt hil, ↓reduceIte]
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_ (strtok_r_tok code strtok_r h h_sym
        _ p str delim R h_nz h_dnz h_len h_dlen i hil hspan hnm rfl h_mem)
      rintro s ⟨hpc, x3, x4, x5, x6, x7, st, m, hm, hs⟩
      exact .inr (.inr ⟨hpc, x3, x4, x5, x6, x7, st, m, hm,
        by rw [hs, hret]⟩)
    · intro h_c
      rw [ldrb_eq_zero_iff] at h_c
      have hil : i = str.length := by
        refine Nat.le_antisymm hi (Nat.not_lt.mp fun hlt => h_nz ?_)
        rw [List.getElem_append_left hlt] at h_c
        exact h_c ▸ List.getElem_mem hlt
      have hspan : strtokSpan str delim = str.length :=
        List.length_takeWhile_eq (Nat.le_refl _)
          (fun j hj => by simpa using hsp j (hil ▸ hj) hj)
          (fun h => absurd h (Nat.lt_irrefl _))
      have hL := h_mem
      rw [show ∀ a b c (r : DataMem → Prop), a ⋆ (b ⋆ (c ⋆ r)) =
        c ⋆ (a ⋆ (b ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL
      instr "str xzr, [x2]" at strtok_r + 0x28
      simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
        [MachineData.store_of_sep64_zero hL, Effects.All, MemWidth.bytes]
      have hL' := Mem.storeInt_sep _ 8 _ _ _ ⟨hL, UInt64.toBytes_length _⟩
        (0#64).toInt
      rw [show Int.toBytes 8 (0#64).toInt = (0 : UInt64).toBytes from rfl,
        show ∀ a b c (r : DataMem → Prop), c ⋆ (a ⋆ (b ⋆ r)) =
          a ⋆ (b ⋆ (c ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL'
      instr "mov x0, #0x0" at strtok_r + 0x2c
      instr "ret" at strtok_r + 0x30
      have hend : strtokEnd str delim := .inl hspan
      refine .done _ (.inr (.inr
        ⟨rfl, ?x3, ?x4, ?x5, ?x6, ?x7, ?st, ?m, ?hm, ?hs⟩))
      case hs =>
        simp only [strtokRet, hspan, ↓reduceIte]
        state_eq
      case hm => simpa [strtokStr, strtokLast, hend] using hL'

/-- `strtok_r` with a string `x0 ≠ 0`, the delimiters at `x1`, and the
pointer at `x2` that it saves its position in. It returns the next token
of the string, see `strtokRet`, `strtokLast` and `strtokStr`. -/
theorem strtok_r_spec [Labels] (code : Code) (strtok_r : Int64)
    (h : Loaded code strtok_r strtok_r_o)
    (h_sym : label "strtok_r" = strtok_r)
    (s0 : MachineData) (str delim : List UInt8) (l : UInt64)
    (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_dnz : 0 ∉ delim) (h_len : str.length < 2 ^ 64)
    (h_dlen : delim.length < 2 ^ 64) (h_x0 : s0.regs.X0 ≠ 0)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆
      (Eq ((delim ++ [0]).At s0.regs.X1.toBitVec) ⋆
        (Eq (l.toBytes.At s0.regs.X2.toBitVec) ⋆ R))) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x3 x4 x5 x6 x7 st m,
      (m =⋆ Eq ((strtokStr str delim).At s0.regs.X0.toBitVec) ⋆
        (Eq ((delim ++ [0]).At s0.regs.X1.toBitVec) ⋆
          (Eq ((strtokLast s0.regs.X0 str delim).toBytes.At
            s0.regs.X2.toBitVec) ⋆ R))) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtokRet s0.regs.X0 str delim
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7 }
        status := st
        dmem := m })
    ⟨s0, strtok_r⟩ := by
  instr "mov x3, x0" at strtok_r
  instr "cbnz x0, 10 <strtok_r+0x10>" at strtok_r + 0x4
  · intro _
    rw [h_sym]
    simp only [ofNat_zero_or64]
    refine eventually_weaken _ _ _ _ ?_ (strtok_r_from code strtok_r h h_sym
      _ s0.regs.X0 str delim R h_nz h_dnz h_len h_dlen rfl h_mem)
    rintro s ⟨hpc, x3, x4, x5, x6, x7, st, m, hm, hs⟩
    exact ⟨hpc, x3, x4, x5, x6, x7, st, m, hm, by rw [hs]⟩
  · intro h0
    exact absurd (UInt64.toBitVec_inj.mp h0) h_x0

/-- Loads the doubleword `l` at `a`, for a hypothesis `h` that says that the
memory holds `l` at `a`. -/
macro "load_last" h:term:max : tactic => `(tactic|
  simp (disch := first | rfl | simp [UInt64.toBytes_length]) only
    [MachineData.load_of_sep64_zero $h (by simp [UInt64.toBytes_length]),
      Effects.All, MemWidth.bytes, MemWidth.bits, List.take_of_length_le,
      BitVec.ofInt_ofBytes_toBytes64])

/-- `strtok_r` with `x0 = 0`, which continues with the string at the pointer
`l ≠ 0` that the previous call saved at `x2`. -/
theorem strtok_r_spec_next [Labels] (code : Code) (strtok_r : Int64)
    (h : Loaded code strtok_r strtok_r_o)
    (h_sym : label "strtok_r" = strtok_r)
    (s0 : MachineData) (str delim : List UInt8) (l : UInt64)
    (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_dnz : 0 ∉ delim) (h_len : str.length < 2 ^ 64)
    (h_dlen : delim.length < 2 ^ 64) (h_x0 : s0.regs.X0 = 0) (h_l : l ≠ 0)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At l.toBitVec) ⋆
      (Eq ((delim ++ [0]).At s0.regs.X1.toBitVec) ⋆
        (Eq (l.toBytes.At s0.regs.X2.toBitVec) ⋆ R))) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x3 x4 x5 x6 x7 st m,
      (m =⋆ Eq ((strtokStr str delim).At l.toBitVec) ⋆
        (Eq ((delim ++ [0]).At s0.regs.X1.toBitVec) ⋆
          (Eq ((strtokLast l str delim).toBytes.At
            s0.regs.X2.toBitVec) ⋆ R))) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X0 := strtokRet l str delim
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6
          X7 := x7 }
        status := st
        dmem := m })
    ⟨s0, strtok_r⟩ := by
  have hL := h_mem
  rw [show ∀ a b c (r : DataMem → Prop), a ⋆ (b ⋆ (c ⋆ r)) =
    c ⋆ (a ⋆ (b ⋆ r)) from fun _ _ _ _ => by ac_rfl] at hL
  instr "mov x3, x0" at strtok_r
  instr "cbnz x0, 10 <strtok_r+0x10>" at strtok_r + 0x4
  · intro h0
    exact absurd (by rw [h_x0]; rfl) h0
  · intro _
    instr "ldr x3, [x2]" at strtok_r + 0x8
    load_last hL
    instr "cbz x3, 2c <strtok_r+0x2c>" at strtok_r + 0xc
    · intro h0
      exact absurd (UInt64.toBitVec_inj.mp h0) h_l
    · intro _
      rw [show strtok_r + 0xc + 4 = strtok_r + 0x10 by bv_decide]
      refine eventually_weaken _ _ _ _ ?_ (strtok_r_from code strtok_r h
        h_sym _ l str delim R h_nz h_dnz h_len h_dlen rfl h_mem)
      rintro s ⟨hpc, x3, x4, x5, x6, x7, st, m, hm, hs⟩
      exact ⟨hpc, x3, x4, x5, x6, x7, st, m, hm, by rw [hs]⟩

/-- `strtok_r` with `x0 = 0` after the end of the string, when the pointer
saved at `x2` is 0: it returns 0. -/
theorem strtok_r_spec_none [Labels] (code : Code) (strtok_r : Int64)
    (h : Loaded code strtok_r strtok_r_o)
    (h_sym : label "strtok_r" = strtok_r)
    (s0 : MachineData) (R : DataMem → Prop) (h_x0 : s0.regs.X0 = 0)
    (h_mem : s0.dmem =⋆ Eq ((0 : UInt64).toBytes.At s0.regs.X2.toBitVec) ⋆
      R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      s.data = { s0 with regs := { s0.regs with X0 := 0, X3 := 0 } })
    ⟨s0, strtok_r⟩ := by
  instr "mov x3, x0" at strtok_r
  instr "cbnz x0, 10 <strtok_r+0x10>" at strtok_r + 0x4
  · intro h0
    exact absurd (by rw [h_x0]; rfl) h0
  · intro _
    instr "ldr x3, [x2]" at strtok_r + 0x8
    load_last h_mem
    instr "cbz x3, 2c <strtok_r+0x2c>" at strtok_r + 0xc
    · intro _
      rw [h_sym]
      instr "mov x0, #0x0" at strtok_r + 0x2c
      instr "ret" at strtok_r + 0x30
      exact .done _ ⟨rfl, by state_eq⟩
    · intro h0
      exact absurd rfl h0
