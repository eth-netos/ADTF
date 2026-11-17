module

public import ADTF.AtfLibc.Listing.strlcat_o
public import ADTF.AtfLibc.Strlen
public import ADTF.AtfLibc.Strlcpy
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump
public import Kraken.AArch64.BeaconCall

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strlcat` from TF-A's `libc/strlcat.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`, plus the relocation of the call
to `strlen` (see `Kraken.AArch64.Objdump`).
-/

/-- The instructions of `strlcat` in ATF's `strlcat.o`. -/
public def strlcat_o : List Instr := objdumpAArch64(strlcat_o_dump)

/-- The length of the string in the buffer `ds`: the index of its first 0,
or the length of `ds` if it has none. -/
@[expose] public def bufStrLen (ds : List UInt8) : Nat :=
  (ds.takeWhile (· != 0)).length

/-- The buffer `ds` after `strlcat` appended the string `str` to the string
in it: `strlcpyDst` on the bytes from the end of that string on. -/
@[expose] public def strlcatDst (ds str : List UInt8) : List UInt8 :=
  ds.take (bufStrLen ds) ++ strlcpyDst str (ds.drop (bufStrLen ds))

/-- `strlcat` appends as much of the NUL-terminated string at `src` as fits
to the string in the `dsize` bytes at `dst`, under the generic calling
convention, and returns the length of the string it tried to create. It
uses 32 bytes of stack. -/
@[expose] public def strlcat_spec [Labels] (code : Code) (strlcat : Int64) :
    Prop :=
  ∀ (dst src dsize : UInt64) (ds str : List UInt8) (R : DataMem → Prop),
    CallSpec code strlcat
      (fun regs m => regs.X0 = dst ∧ regs.X1 = src ∧ regs.X2 = dsize ∧
        ds.length = dsize.toNat ∧ 0 ∉ str ∧ str.length < 2 ^ 64 ∧
        m =⋆ Eq (ds.At dst.toBitVec) ⋆ Eq ((str ++ [0]).At src.toBitVec) ⋆
          stack_available regs.SP 32 ⋆ R)
      (fun regs m => regs.X0 = .ofNat (bufStrLen ds + str.length) ∧
        m =⋆ Eq ((strlcatDst ds str).At dst.toBitVec) ⋆
          Eq ((str ++ [0]).At src.toBitVec) ⋆
          stack_available regs.SP 32 ⋆ R)

/-- The epilogue of `strlcat` from `strlcat + 0x38`: it restores `x19`,
`x29` and `x30` from the stack frame at `sp`, frees the frame and returns,
with `x0` unchanged. -/
theorem strlcat_epilogue [Labels] (code : Code) (strlcat : Int64)
    (h : Loaded code strlcat strlcat_o) (s0 : MachineData)
    (hsp : s0.regs.SP % 16 = 0) (w3 : UInt64) (A R : DataMem → Prop)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem) (pc : Int64)
    (hpc : pc = strlcat + 0x38)
    (h18 : regs.X18 = s0.regs.X18) (h20 : regs.X20 = s0.regs.X20)
    (h21 : regs.X21 = s0.regs.X21) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 32#64⟩)
    (hm : m =⋆ Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, w3].wordBytes.At
      (s0.regs.SP.toBitVec - 32#64)) ⋆ (A ⋆ R)) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = regs.X0 ∧
      (A ⋆ stack_available s.data.regs.SP 32 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, pc⟩ := by
  subst hpc
  have hal := sp_aligned (sp_sub_aligned hsp 32#64 rfl)
  dsimp only at hal
  instr "ldr x19, [sp, #16]" at strlcat + 0x38
  simp only [hSP, hal, Bool.false_eq_true, ↓reduceIte]
  load_frame hm 2
  instr_simp
  instr "ldp x29, x30, [sp], #32" at strlcat + 0x3c
  simp only [hSP, hal, Bool.false_eq_true, ↓reduceIte]
  load_frame hm 0
  load_frame hm 1
  instr_simp
  simp only [List.getElem_cons_zero, List.getElem_cons_succ,
    sub_add_ofNat, UInt64.ofBitVec_toBitVec]
  instr "ret" at strlcat + 0x40
  refine .done _ ⟨rfl, ⟨h18, rfl, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, rfl, rfl⟩, rfl, ?_⟩
  dsimp only
  rw [Std.ExtHashMap.sep_comm] at hm
  have hm' : m =⋆ (A ⋆ R) ⋆ stack_available s0.regs.SP 32 :=
    sep_mono_r (fun _ hF => anybytes_of_wordBytes hF) hm
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm R,
    ← Std.ExtHashMap.sep_assoc] at hm'
  exact hm'

/-- The length of a buffer, as `strlcat` computes it from a pointer to its
end. -/
theorem add_ofNat_sub (a : UInt64) (n : Nat) :
    UInt64.ofBitVec ((a + .ofNat n).toBitVec - a.toBitVec) = .ofNat n := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_add, BitVec.add_comm]
  exact BitVec.add_sub_cancel _ _

theorem List.set_take_append (ds x : List UInt8) {k i : Nat}
    (hk : k ≤ ds.length) (v : UInt8) :
    (ds.take k ++ x).set (k + i) v = ds.take k ++ x.set i v := by
  rw [List.set_append_right _ _ (by rw [List.length_take]; omega),
    List.length_take, Nat.min_eq_left hk, Nat.add_sub_cancel_left]

/-- The copy loop of `strlcat` from `strlcat + 0x5c`, which appends the
string `str` to the string of length `k` in `ds`, with room for `c` bytes
before the terminating NUL: it has read `j` bytes of `str` and copied the
first `min j c` of them. -/
theorem strlcat_copy [Labels] (code : Code) (strlcat : Int64)
    (h : Loaded code strlcat strlcat_o) (h_sym : label "strlcat" = strlcat)
    (s0 : MachineData) (hsp : s0.regs.SP % 16 = 0) (w3 : UInt64)
    (ds str : List UInt8) (k c : Nat) (R : DataMem → Prop)
    (hc : k + c + 1 = ds.length) (hdl : ds.length < 2 ^ 64)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem) (j : Nat)
    (hj : j ≤ str.length)
    (hX0 : regs.X0 = s0.regs.X1)
    (hX2 : regs.X2 = .ofNat (c - min j c))
    (hX3 : regs.X3 = s0.regs.X0 + .ofNat (k + min j c))
    (hX4 : regs.X4 = s0.regs.X1 + .ofNat j)
    (hX19 : regs.X19 = .ofNat k)
    (h18 : regs.X18 = s0.regs.X18) (h20 : regs.X20 = s0.regs.X20)
    (h21 : regs.X21 = s0.regs.X21) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 32#64⟩)
    (hm : m =⋆ Eq ((ds.take k ++ (str.take (min j c) ++
        (ds.drop k).drop (min j c))).At s0.regs.X0.toBitVec) ⋆
      Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆
      Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, w3].wordBytes.At
        (s0.regs.SP.toBitVec - 32#64)) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = .ofNat (k + str.length) ∧
      ((Eq ((ds.take k ++ (str.take (min str.length c) ++
          0 :: (ds.drop k).drop (min str.length c + 1))).At
          s0.regs.X0.toBitVec) ⋆
        Eq ((str ++ [0]).At s0.regs.X1.toBitVec)) ⋆
        stack_available s.data.regs.SP 32 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, strlcat + 0x5c⟩ := by
  refine loop_rule_at (measure fun j => str.length - j).wf
    (fun j d => j ≤ str.length ∧ ∃ x1 st m,
      d = ⟨{ regs with
          X1 := x1
          X2 := .ofNat (c - min j c)
          X3 := s0.regs.X0 + .ofNat (k + min j c)
          X4 := s0.regs.X1 + .ofNat j }, st, m⟩ ∧
      m =⋆ Eq ((ds.take k ++ (str.take (min j c) ++
          (ds.drop k).drop (min j c))).At s0.regs.X0.toBitVec) ⋆
        Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆
        Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, w3].wordBytes.At
          (s0.regs.SP.toBitVec - 32#64)) ⋆ R)
    _ (strlcat + 0x5c) (strlcat + 0x38) j _
    ⟨hj, regs.X1, st, m, by rw [← hX2, ← hX3, ← hX4], hm⟩ ?_
  rintro j d ⟨hj, x1, st, m, rfl, hm⟩
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc] at hm
  have hm2 := hm
  rw [Std.ExtHashMap.sep_comm_l] at hm2
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by
    rw [List.length_append, List.length_singleton]; omega
  have hl : (ds.take k ++ (str.take (min j c) ++
      (ds.drop k).drop (min j c))).length = ds.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  instr "ldrb w1, [x4]" at strlcat + 0x5c
  load_byte hm2 hw
  instr "cbnz w1, 74 <strlcat+0x74>" at strlcat + 0x60
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have hlt : j < str.length :=
      Nat.lt_of_le_of_ne hj fun he => h_b (by simp only [he,
        List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_singleton])
    simp only [List.getElem_append_left hlt] at h_b ⊢
    rw [h_sym]
    instr "cbz x2, 80 <strlcat+0x80>" at strlcat + 0x74
    · intro hz
      have hcj := ofNat_toBitVec_eq_zero (by omega) hz
      have e : min (j + 1) c = min j c := by omega
      instr "add x4, x4, #0x1" at strlcat + 0x80
      instr "b 5c <strlcat+0x5c>" at strlcat + 0x84
      refine .done _ (.inl ⟨by rw [h_sym], j + 1, ?_, ?_⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rw [e]
        rw [← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc] at hm
        exact ⟨by omega, _, _, _, by state_eq, hm⟩
    · intro hz
      have hjc : j < c := Nat.lt_of_not_le fun hcj =>
        hz (by rw [show c - min j c = 0 by omega]; rfl)
      have ej : min j c = j := Nat.min_eq_left (Nat.le_of_lt hjc)
      rw [ej] at hm hl ⊢
      rw [show c - j = (c - (j + 1)) + 1 by omega]
      instr "sub x2, x2, #0x1" at strlcat + 0x78
      simp only [ofNat_succ_sub_one]
      instr "strb w1, [x3], #1" at strlcat + 0x7c
      store_byte hm
      have hm' := Mem.storeInt_byte_sep _ _ (k + j) _ m hm (by omega)
        (by omega) str[j]
      rw [List.set_take_append _ _ (by omega),
        List.set_take_append_drop hlt (by rw [List.length_drop]; omega),
        ← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc] at hm'
      instr "add x4, x4, #0x1" at strlcat + 0x80
      instr "b 5c <strlcat+0x5c>" at strlcat + 0x84
      refine .done _ (.inl ⟨by rw [h_sym], j + 1, ?_, ?_⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · rw [show min (j + 1) c = j + 1 by omega]
        have e3 : UInt64.ofBitVec (s0.regs.X0.toBitVec +
            (BitVec.ofNat 64 (k + j) + 1)) =
            s0.regs.X0 + .ofNat (k + (j + 1)) := by
          apply UInt64.toBitVec_inj.mp
          rw [UInt64.toBitVec_add, UInt64.toBitVec_ofNat', ← Nat.add_assoc,
            BitVec.ofNat_add (k + j) 1]
          rfl
        rw [e3]
        exact ⟨by omega, _, _, _, by state_eq, hm'⟩
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have he : j = str.length := by
      refine Nat.le_antisymm hj (Nat.not_lt.mp fun hlt => h_nz ?_)
      rw [List.getElem_append_left hlt] at h_b
      exact h_b ▸ List.getElem_mem hlt
    subst he
    instr "sub x4, x4, x0" at strlcat + 0x64
    rw [hX0, add_ofNat_sub]
    instr "strb wzr, [x3]" at strlcat + 0x68
    store_byte hm
    have hz : (BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 0#64)).toInt =
        (0 : UInt8).toBitVec.toInt := by decide
    rw [hz]
    have hm' := Mem.storeInt_byte_sep _ _ (k + min str.length c) _ m hm
      (by omega) (by omega) 0
    rw [List.set_take_append _ _ (by omega),
      List.set_take_append_drop' _ (Nat.min_le_left _ _)
        (by rw [List.length_drop]; omega),
      ← Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm'
    instr "add x0, x4, x19" at strlcat + 0x6c
    rw [hX19]
    instr "b 38 <strlcat+0x38>" at strlcat + 0x70
    refine .done _ (.inr ⟨by rw [h_sym], ?_⟩)
    refine eventually_weaken _ _ _ _ ?_ (strlcat_epilogue code strlcat h s0
      hsp w3 _ R _ _ _ _ (by rw [h_sym]) h18 h20 h21 h22 h23 h24 h25 h26 h27
      h28 hSP hm')
    rintro s ⟨hpc, hpres, hx0, hms⟩
    refine ⟨hpc, hpres, ?_, hms⟩
    rw [hx0]
    uint64_eq

theorem sub_ofNat_eq_zero_iff {x : UInt64} {k : Nat} (hk : k ≤ x.toNat) :
    (x.toBitVec - (UInt64.ofNat k).toBitVec == BitVec.zero 64) = true ↔
      k = x.toNat := by
  rw [beq_iff_eq, BitVec.zero_eq, UInt64.toBitVec_ofNat']
  rw [← UInt64.toNat_toBitVec] at *
  constructor
  · intro h
    bv_omega
  · intro h
    bv_omega

/-- The room that `strlcat` leaves for the terminating NUL. -/
theorem sub_ofNat_sub_one {x : UInt64} {k : Nat} (hk : k < x.toNat) :
    UInt64.ofBitVec (x.toBitVec - (UInt64.ofNat k).toBitVec - 1) =
      .ofNat (x.toNat - k - 1) := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_ofNat', UInt64.toBitVec_ofNat']
  rw [← UInt64.toNat_toBitVec] at *
  bv_omega

theorem bufStrLen_eq {ds : List UInt8} {k : Nat} (hk : k ≤ ds.length)
    (hz : ∀ i < k, ds[i]? ≠ some 0)
    (hend : k = ds.length ∨ ds[k]? = some 0) :
    bufStrLen ds = k := by
  refine List.length_takeWhile_eq hk (fun j hj => ?_) (fun hi => ?_)
  · have := hz j hj
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact bne_iff_ne.mpr fun he => this (by rw [he])
  · have h0 := hend.resolve_left (by omega)
    rw [List.getElem?_eq_getElem hi, Option.some_inj] at h0
    rw [h0]
    rfl

/-- `strlcat` from `strlcat + 0x24`, after it found the string of length
`k` in `ds`. -/
theorem strlcat_tail [Labels] (code : Code) (strlcat : Int64)
    (h : Loaded code strlcat strlcat_o) (h_sym : label "strlcat" = strlcat)
    (h_strlen : strlen_spec code (label "strlen"))
    (s0 : MachineData) (hsp : s0.regs.SP % 16 = 0) (w3 : UInt64)
    (ds str : List UInt8) (k : Nat) (R : DataMem → Prop)
    (h_ds : ds.length = s0.regs.X2.toNat) (hk : k ≤ ds.length)
    (hz : ∀ i < k, ds[i]? ≠ some 0)
    (hend : k = ds.length ∨ ds[k]? = some 0)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem)
    (hX0 : regs.X0 = s0.regs.X1) (hX2 : regs.X2 = s0.regs.X2)
    (hX3 : regs.X3 = s0.regs.X0 + .ofNat k) (hX19 : regs.X19 = s0.regs.X0)
    (h18 : regs.X18 = s0.regs.X18) (h20 : regs.X20 = s0.regs.X20)
    (h21 : regs.X21 = s0.regs.X21) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 32#64⟩)
    (hm : m =⋆ Eq (ds.At s0.regs.X0.toBitVec) ⋆
      Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆
      Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, w3].wordBytes.At
        (s0.regs.SP.toBitVec - 32#64)) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = .ofNat (bufStrLen ds + str.length) ∧
      ((Eq ((strlcatDst ds str).At s0.regs.X0.toBitVec) ⋆
        Eq ((str ++ [0]).At s0.regs.X1.toBitVec)) ⋆
        stack_available s.data.regs.SP 32 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, strlcat + 0x24⟩ := by
  have hX2l := s0.regs.X2.toNat_lt
  rw [strlcatDst, bufStrLen_eq hk hz hend]
  instr "sub x19, x3, x19" at strlcat + 0x24
  rw [hX3, hX19, add_ofNat_sub]
  instr "subs x2, x2, x19" at strlcat + 0x28
  rw [hX2]
  instr "b.ne 54 <strlcat+0x54>" at strlcat + 0x2c
  · intro hne
    have hlt : k < ds.length := Nat.lt_of_le_of_ne hk fun he => by
      rw [(sub_ofNat_eq_zero_iff (by omega)).mpr (by omega)] at hne
      exact absurd hne (by decide)
    rw [strlcpyDst, ite_eq_right_of_eq_false _ _ (eq_false
      (List.ne_nil_of_length_pos (by rw [List.length_drop]; omega))),
      List.length_drop, h_sym]
    instr "sub x2, x2, #0x1" at strlcat + 0x54
    instr "mov x4, x0" at strlcat + 0x58
    simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
    rw [show strlcat + 88 + 4 = strlcat + 0x5c by bv_decide]
    refine strlcat_copy code strlcat h h_sym s0 hsp w3 ds str k
      (ds.length - k - 1) R (by omega) (by omega) h_nz h_len _ _ _ 0
      (Nat.zero_le _) (by exact hX0) ?_ ?_ ?_ (by rfl) (by exact h18)
      (by exact h20) (by exact h21) (by exact h22) (by exact h23)
      (by exact h24) (by exact h25) (by exact h26) (by exact h27)
      (by exact h28) (by exact hSP) ?_
    · dsimp only
      rw [Nat.zero_min, Nat.sub_zero, h_ds]
      exact sub_ofNat_sub_one (by omega)
    · dsimp only
      rw [Nat.zero_min, Nat.add_zero]
    · dsimp only
      rw [hX0]
      uint64_eq
    · rw [Nat.zero_min, List.take_zero, List.drop_zero, List.nil_append,
        List.take_append_drop]
      exact hm
  · intro heq
    have he : k = ds.length := by
      refine Classical.byContradiction fun hne => heq ?_
      rw [show (s0.regs.X2.toBitVec - (UInt64.ofNat k).toBitVec ==
          BitVec.zero 64) = false from Bool.eq_false_iff.mpr fun hb =>
        hne (by rw [h_ds]; exact (sub_ofNat_eq_zero_iff (by omega)).mp hb)]
      rfl
    subst he
    rw [List.take_length, List.drop_length, strlcpyDst,
      ite_eq_left_of_eq_true _ _ (eq_true rfl), List.append_nil]
    instr "bl strlen" at strlcat + 0x30
    rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc,
      Std.ExtHashMap.sep_comm_l] at hm
    refine CallSpec.apply (h_strlen s0.regs.X1 str _)
      (by rw [hSP]; exact sp_sub_aligned hsp 32#64 rfl)
      ⟨hX0, h_nz, h_len, hm⟩ ?_
    rintro regs1 m1 st1 hpres1 ⟨hr0, hm1⟩
    simp only [CalleeSavedRegsPreserved] at hpres1
    obtain ⟨g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, -,
      gsp⟩ := hpres1
    dsimp only
    simp only [UInt64.toInt64_ofBitVec_toBitVec]
    instr "add x0, x0, x19" at strlcat + 0x34
    rw [hr0, g19]
    rw [Std.ExtHashMap.sep_comm_l, ← Std.ExtHashMap.sep_assoc,
      Std.ExtHashMap.sep_comm_l] at hm1
    refine eventually_weaken _ _ _ _ ?_ (strlcat_epilogue code strlcat h s0
      hsp w3 _ R _ _ _ _ (by bv_decide) (g18.trans h18) (g20.trans h20)
      (g21.trans h21) (g22.trans h22) (g23.trans h23) (g24.trans h24)
      (g25.trans h25) (g26.trans h26) (g27.trans h27) (g28.trans h28)
      (gsp.trans hSP) hm1)
    rintro s ⟨hpc, hpres, hx0, hms⟩
    refine ⟨hpc, hpres, ?_, hms⟩
    rw [hx0]
    uint64_eq

/-- The condition `eq` of `cmp x3, x4` in `strlcat`, with `x3` in the
buffer of length `x` at `a` and `x4` at its end. -/
theorem add_ofNat_sub_add_eq_zero_iff {a x : UInt64} {k : Nat}
    (hk : k ≤ x.toNat) :
    ((a + .ofNat k).toBitVec - (a + x).toBitVec == BitVec.zero 64) = true ↔
      k = x.toNat := by
  rw [beq_iff_eq, BitVec.zero_eq, UInt64.toBitVec_add, UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat']
  rw [← UInt64.toNat_toBitVec] at *
  constructor
  · intro h
    bv_omega
  · intro h
    bv_omega

/-- The loop of `strlcat` from `strlcat + 0x1c` that finds the end of the
string in `ds`. -/
theorem strlcat_scan [Labels] (code : Code) (strlcat : Int64)
    (h : Loaded code strlcat strlcat_o) (h_sym : label "strlcat" = strlcat)
    (h_strlen : strlen_spec code (label "strlen"))
    (s0 : MachineData) (hsp : s0.regs.SP % 16 = 0) (w3 : UInt64)
    (ds str : List UInt8) (R : DataMem → Prop)
    (h_ds : ds.length = s0.regs.X2.toNat)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem)
    (hX0 : regs.X0 = s0.regs.X1) (hX2 : regs.X2 = s0.regs.X2)
    (hX3 : regs.X3 = s0.regs.X0) (hX4 : regs.X4 = s0.regs.X0 + s0.regs.X2)
    (hX19 : regs.X19 = s0.regs.X0)
    (h18 : regs.X18 = s0.regs.X18) (h20 : regs.X20 = s0.regs.X20)
    (h21 : regs.X21 = s0.regs.X21) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 32#64⟩)
    (hm : m =⋆ Eq (ds.At s0.regs.X0.toBitVec) ⋆
      Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆
      Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, w3].wordBytes.At
        (s0.regs.SP.toBitVec - 32#64)) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = .ofNat (bufStrLen ds + str.length) ∧
      ((Eq ((strlcatDst ds str).At s0.regs.X0.toBitVec) ⋆
        Eq ((str ++ [0]).At s0.regs.X1.toBitVec)) ⋆
        stack_available s.data.regs.SP 32 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, strlcat + 0x1c⟩ := by
  have hX2l := s0.regs.X2.toNat_lt
  have hm1 := hm
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc] at hm1
  refine loop_rule_at (measure fun k => ds.length - k).wf
    (fun k d => k ≤ ds.length ∧ (∀ i < k, ds[i]? ≠ some 0) ∧
      ∃ x1 st,
      d = ⟨{ regs with
          X1 := x1
          X3 := s0.regs.X0 + .ofNat k }, st, m⟩)
    _ (strlcat + 0x1c) (strlcat + 0x24) 0 _
    ⟨Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), regs.X1, st,
      by rw [show s0.regs.X0 + .ofNat 0 = regs.X3 by rw [hX3]; uint64_eq]⟩
    ?_
  rintro k d ⟨hk, hz, x1, st, rfl⟩
  instr "cmp x3, x4" at strlcat + 0x1c
  rw [hX4]
  instr "b.ne 44 <strlcat+0x44>" at strlcat + 0x20
  · intro hne
    have hlt : k < ds.length := Nat.lt_of_le_of_ne hk fun he => by
      rw [(add_ofNat_sub_add_eq_zero_iff (by omega)).mpr (by omega)] at hne
      exact absurd hne (by decide)
    have hdl : ds.length ≤ 2 ^ 64 := by omega
    rw [h_sym]
    instr "ldrb w1, [x3]" at strlcat + 0x44
    load_byte hm1 hdl
    instr "cbz w1, 24 <strlcat+0x24>" at strlcat + 0x48
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      refine .done _ (.inr ⟨by rw [h_sym], ?_⟩)
      rw [h_sym]
      exact strlcat_tail code strlcat h h_sym h_strlen s0 hsp w3 ds str k R
        h_ds (Nat.le_of_lt hlt) hz
        (.inr (by rw [List.getElem?_eq_getElem hlt, h_b]))
        h_nz h_len _ _ _ (by exact hX0) (by exact hX2) (by rfl)
        (by exact hX19) (by exact h18) (by exact h20) (by exact h21)
        (by exact h22) (by exact h23) (by exact h24) (by exact h25)
        (by exact h26) (by exact h27) (by exact h28) (by exact hSP) hm
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "add x3, x3, #0x1" at strlcat + 0x4c
      instr "b 1c <strlcat+0x1c>" at strlcat + 0x50
      refine .done _ (.inl ⟨by rw [h_sym], k + 1, ?_, by omega, ?_, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · rw [List.getElem?_eq_getElem hlt]
          exact fun he => h_b (Option.some_inj.mp he)
  · intro heq
    have he : k = ds.length := by
      refine Classical.byContradiction fun hne => heq ?_
      rw [show ((s0.regs.X0 + UInt64.ofNat k).toBitVec -
          (s0.regs.X0 + s0.regs.X2).toBitVec == BitVec.zero 64) = false from
        Bool.eq_false_iff.mpr fun hb => hne (by
          rw [h_ds]; exact (add_ofNat_sub_add_eq_zero_iff (by omega)).mp hb)]
      rfl
    rw [show strlcat + 32 + 4 = strlcat + 0x24 by bv_decide]
    refine .done _ (.inr ⟨rfl, ?_⟩)
    exact strlcat_tail code strlcat h h_sym h_strlen s0 hsp w3 ds str k R
      h_ds hk hz (.inl he)
      h_nz h_len _ _ _ (by exact hX0) (by exact hX2) (by rfl)
      (by exact hX19) (by exact h18) (by exact h20) (by exact h21)
      (by exact h22) (by exact h23) (by exact h24) (by exact h25)
      (by exact h26) (by exact h27) (by exact h28) (by exact hSP) hm

public theorem strlcat_ok [Labels] (code : Code) (strlcat : Int64)
    (h : Loaded code strlcat strlcat_o)
    (h_sym : label "strlcat" = strlcat)
    (h_strlen : strlen_spec code (label "strlen")) :
    strlcat_spec code strlcat := by
  rintro dst src dsize ds str R s0 hsp
    ⟨rfl, rfl, rfl, h_ds, h_nz, h_len, hm⟩
  have hsp' := sp_aligned hsp
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm
  obtain ⟨ws, hws, hm⟩ := (anybytes_sep_words_iff (k := 4)).mp hm
  obtain ⟨w0, w1, w2, w3, rfl⟩ :
      ∃ w0 w1 w2 w3, ws = [w0, w1, w2, w3] := by
    match ws, hws with
    | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
  instr "stp x29, x30, [sp, #-32]!" at strlcat
  simp only [hsp', Bool.false_eq_true, ↓reduceIte, add_neg_toBitVec]
  store_frame hm 0
  have hm1 := Mem.storeInt_frame_word_sep hm (by omega) 0 (by omega)
    s0.regs.X29.toBitVec
  store_frame hm1 1
  have hm2 := Mem.storeInt_frame_word_sep hm1 (by simp) 1
    (by simp) s0.regs.X30.toBitVec
  simp only [List.set, UInt64.ofBitVec_toBitVec] at hm2
  instr_simp
  have hal := sp_aligned (sp_sub_aligned hsp 32#64 rfl)
  dsimp only at hal
  instr "mov x29, sp" at strlcat + 0x4
  instr "str x19, [sp, #16]" at strlcat + 0x8
  simp only [hal, Bool.false_eq_true, ↓reduceIte]
  store_frame hm2 2
  have hm3 := Mem.storeInt_frame_word_sep hm2 (by simp) 2
    (by simp) s0.regs.X19.toBitVec
  simp only [List.set, UInt64.ofBitVec_toBitVec] at hm3
  instr_simp
  instr "mov x19, x0" at strlcat + 0xc
  simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
  instr "add x4, x19, x2" at strlcat + 0x10
  instr "mov x0, x1" at strlcat + 0x14
  simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
  instr "mov x3, x19" at strlcat + 0x18
  simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
  rw [Std.ExtHashMap.sep_comm_l, ← Std.ExtHashMap.sep_assoc] at hm3
  rw [show strlcat + 24 + 4 = strlcat + 0x1c by bv_decide]
  exact strlcat_scan code strlcat h h_sym h_strlen s0 hsp w3 ds str R h_ds
    h_nz h_len _ _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) hm3
