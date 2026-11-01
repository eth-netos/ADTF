module

import ADTF.AtfLibc.Listing.strlcpy_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strlcpy` from TF-A's `libc/strlcpy.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strlcpy` in ATF's `strlcpy.o`. -/
def strlcpy_o : List Instr := objdumpAArch64(strlcpy_o_dump)

/-- The loop of `strlcpy` that finds the end of the source string, from the
`k`-th byte on, entered at `strlcpy + 0x8`. It returns the length of the
string. -/
theorem strlcpy_scan [Labels] (code : Code) (strlcpy : Int64)
    (h : Loaded code strlcpy strlcpy_o)
    (h_sym : label "strlcpy" = strlcpy)
    (d : MachineData) (str : List UInt8) (R : DataMem → Prop) (k : Nat)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64) (hk : k ≤ str.length)
    (h_x3 : d.regs.X3 = d.regs.X1 + .ofNat k)
    (h_mem : d.dmem =⋆ Eq ((str ++ [0]).At d.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = d.regs.X30.toInt64 ∧ ∃ x3 st,
      s.data = { d with
        regs := { d.regs with
          X0 := .ofNat str.length
          X3 := x3 }
        status := st })
    ⟨d, strlcpy + 0x8⟩ := by
  refine loop_rule (measure fun n => str.length + 1 - n).wf
    (fun n s => s.pc = strlcpy + 0x8 ∧ n ≤ str.length ∧ ∃ x0 st,
      s.data = { d with
        regs := { d.regs with
          X0 := x0
          X3 := d.regs.X1 + .ofNat n }
        status := st })
    _ k _ ⟨rfl, hk, d.regs.X0, d.status, by rw [← h_x3]⟩ ?_
  rintro n ⟨d', pc⟩ ⟨rfl, hn, x0, st, rfl⟩
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "ldrb w0, [x3], #1" at strlcpy + 0x8
  load_byte h_mem hw
  instr "cbnz w0, 8 <strlcpy+0x8>" at strlcpy + 0xc
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have hlt : n < str.length := by
      refine Nat.lt_of_le_of_ne hn fun he => h_b ?_
      simp [he]
    refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, _, _,
      by state_eq⟩)
    simp only [InvImage, WellFoundedRelation.rel]; omega
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have he : n = str.length := by
      refine Nat.le_antisymm hn (Nat.not_lt.mp fun hlt => h_nz ?_)
      rw [List.getElem_append_left hlt] at h_b
      exact h_b ▸ List.getElem_mem hlt
    subst he
    instr "b 20 <strlcpy+0x20>" at strlcpy + 0x10
    instr "sub x0, x3, x1" at strlcpy + 0x20
    instr "sub x0, x0, #0x1" at strlcpy + 0x24
    instr "ret" at strlcpy + 0x28
    exact .done _ (.inr ⟨rfl, _, _, by state_eq⟩)

/-- The destination buffer `old` after `strlcpy` copied the string `str`
into it: as much of `str` as fits, followed by a 0, unless `old` is
empty. -/
def strlcpyDst (str old : List UInt8) : List UInt8 :=
  if old = [] then [] else
    str.take (min str.length (old.length - 1)) ++
      0 :: old.drop (min str.length (old.length - 1) + 1)

/-- `strlcpy` copies as much of the NUL-terminated string at `x1` as fits
into the `x2` bytes at `x0`, followed by a 0 (unless `x2` is 0), and returns
the length of the string. It changes only `x0`, `x2`, `x3`, `x4`, the flags
and the destination buffer. -/
theorem strlcpy_spec [Labels] (code : Code) (strlcpy : Int64)
    (h : Loaded code strlcpy strlcpy_o)
    (h_sym : label "strlcpy" = strlcpy)
    (s0 : MachineData) (str old : List UInt8) (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64)
    (h_old : old.length = s0.regs.X2.toNat)
    (h_mem : s0.dmem =⋆ Eq (old.At s0.regs.X0.toBitVec) ⋆
      Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x2 x3 x4 st m,
      (m =⋆ Eq ((strlcpyDst str old).At s0.regs.X0.toBitVec) ⋆
        (Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆ R)) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X0 := .ofNat str.length
          X2 := x2
          X3 := x3
          X4 := x4 }
        status := st
        dmem := m })
    ⟨s0, strlcpy⟩ := by
  have hX2 := s0.regs.X2.toNat_lt
  instr "mov x3, x1" at strlcpy
  instr "cbnz x2, 2c <strlcpy+0x2c>" at strlcpy + 0x4
  · intro h_x2
    have h_pos : 0 < s0.regs.X2.toNat := by
      rw [UInt64.toNat]
      exact Nat.pos_of_ne_zero fun h0 => h_x2 (BitVec.eq_of_toNat_eq h0)
    refine loop_rule (measure fun n => s0.regs.X2.toNat - n).wf
      (fun n s => s.pc = strlcpy + 0x2c ∧ n < s0.regs.X2.toNat ∧
        n ≤ str.length ∧ ∃ x4 st m,
        (m =⋆ Eq ((str.take n ++ old.drop n).At s0.regs.X0.toBitVec) ⋆
          (Eq ((str ++ [0]).At s0.regs.X1.toBitVec) ⋆ R)) ∧
        s.data = { s0 with
          regs := { s0.regs with
            X0 := s0.regs.X0 + .ofNat n
            X2 := s0.regs.X2 - .ofNat n
            X3 := s0.regs.X1 + .ofNat n
            X4 := x4 }
          status := st
          dmem := m })
      _ 0 _ ⟨by rw [h_sym], h_pos, Nat.zero_le _, _, _, _,
        by simpa [Std.ExtHashMap.sep_assoc] using h_mem, by state_eq⟩ ?_
    rintro n ⟨d, pc⟩ ⟨rfl, hn, hn', x4, st, m, hm, rfl⟩
    have hm2 := hm
    rw [Std.ExtHashMap.sep_comm_l] at hm2
    have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
    have hl : (str.take n ++ old.drop n).length = s0.regs.X2.toNat := by
      simp; omega
    instr "subs x2, x2, #0x1" at strlcpy + 0x2c
    instr "b.ne 14 <strlcpy+0x14>" at strlcpy + 0x30
    · intro hne
      have hlt := subs_count_ne hn hne
      instr "ldrb w4, [x3], #1" at strlcpy + 0x14
      load_byte hm2 hw
      instr "strb w4, [x0], #1" at strlcpy + 0x18
      store_byte hm
      instr "cbnz w4, 2c <strlcpy+0x2c>" at strlcpy + 0x1c
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        have hlt' : n < str.length :=
          Nat.lt_of_le_of_ne hn' fun he => h_b (by simp [he])
        have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by omega) (by omega)
          str[n]
        rw [List.set_take_append_drop (by simpa using hlt') (by omega)] at hm'
        simp only [List.getElem_append_left hlt']
        refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, hlt', _, _, _,
          hm', by state_eq⟩)
        simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        have he : n = str.length := by
          refine Nat.le_antisymm hn' (Nat.not_lt.mp fun hlt => h_nz ?_)
          rw [List.getElem_append_left hlt] at h_b
          exact h_b ▸ List.getElem_mem hlt
        have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by omega) (by omega) 0
        rw [List.set_take_append_drop' _ (by omega) (by omega)] at hm'
        simp only [h_b]
        subst he
        instr "sub x0, x3, x1" at strlcpy + 0x20
        instr "sub x0, x0, #0x1" at strlcpy + 0x24
        instr "ret" at strlcpy + 0x28
        refine .done _ (.inr ⟨rfl, _, _, _, _, _, ?_, by state_eq⟩)
        have h_ne : old ≠ [] := fun h0 => by simp [h0] at h_old; omega
        have hk : min str.length (old.length - 1) = str.length := by omega
        simpa [strlcpyDst, h_ne, hk] using hm'
    · intro heq
      have he := subs_count_eq hn heq
      instr "strb wzr, [x0]" at strlcpy + 0x34
      store_byte hm
      have hz : (BitVec.extractLsb' 0 8 (BitVec.extractLsb' 0 32 0#64)).toInt =
          (0 : UInt8).toBitVec.toInt := by decide
      rw [hz]
      have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by omega) (by omega) 0
      rw [List.set_take_append_drop' _ (by omega) (by omega)] at hm'
      have h_ne : old ≠ [] := fun h0 => by simp [h0] at h_old; omega
      have hk : min str.length (old.length - 1) = n := by omega
      have h_dst : strlcpyDst str old = str.take n ++ 0 :: old.drop (n + 1) :=
        by simp [strlcpyDst, h_ne, hk]
      rw [← h_dst] at hm'
      have hm2' := hm'
      rw [Std.ExtHashMap.sep_comm_l] at hm2'
      instr "b 8 <strlcpy+0x8>" at strlcpy + 0x38
      rw [h_sym]
      refine eventually_weaken _ _ _ _ ?_ (strlcpy_scan code strlcpy h h_sym _
        str _ n h_nz h_len hn' rfl hm2')
      rintro s ⟨hpc, x3, st', hs⟩
      exact .inr ⟨hpc, _, x3, _, st', _, hm', by rw [hs]⟩
  · intro h_x2
    have h_nil : old = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [h_old, UInt64.toNat, h_x2]; rfl
    subst h_nil
    have hm := h_mem
    rw [Std.ExtHashMap.sep_assoc] at hm
    have hm2 := h_mem
    rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm2
    have hpc : strlcpy + 0x4 + 0x4 = strlcpy + 0x8 := by bv_decide
    rw [hpc]
    refine eventually_weaken _ _ _ _ ?_ (strlcpy_scan code strlcpy h h_sym _
      str _ 0 h_nz h_len (Nat.zero_le _) (by uint64_eq) hm2)
    rintro s ⟨hpc, x3, st, hs⟩
    exact ⟨hpc, _, x3, _, st, _, by simpa [strlcpyDst] using hm,
      by rw [hs]⟩
