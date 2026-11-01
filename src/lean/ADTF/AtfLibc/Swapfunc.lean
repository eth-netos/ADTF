module

import ADTF.AtfLibc.Listing.swapfunc_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `swapfunc` from TF-A's `libc/qsort.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `swapfunc` in ATF's `qsort.o`. -/
def swapfunc_o : List Instr := objdumpAArch64(swapfunc_o_dump)

/-- `swapfunc` swaps the contents of the `x2` bytes at `x0` with those of the
disjoint buffer at `x1`, for `x2 > 0`. It changes only `x3` (to `x2`), `x4`,
`x5`, the flags and the two buffers. -/
theorem swapfunc_spec [Labels] (code : Code) (swapfunc : Int64)
    (h : Loaded code swapfunc swapfunc_o)
    (h_sym : label "swapfunc" = swapfunc)
    (s0 : MachineData) (as bs : List UInt8) (R : DataMem → Prop)
    (h_pos : 0 < s0.regs.X2.toNat)
    (h_as : as.length = s0.regs.X2.toNat)
    (h_bs : bs.length = s0.regs.X2.toNat)
    (h_mem : s0.dmem =⋆ Eq (as.At s0.regs.X0.toBitVec) ⋆
      Eq (bs.At s0.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x4 x5 st m,
      (m =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆
        (Eq (as.At s0.regs.X1.toBitVec) ⋆ R)) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X3 := s0.regs.X2
          X4 := x4
          X5 := x5 }
        status := st
        dmem := m })
    ⟨s0, swapfunc⟩ := by
  have hX2 := s0.regs.X2.toNat_lt
  instr "mov x3, #0x0" at swapfunc
  refine loop_rule (measure fun n => s0.regs.X2.toNat - n).wf
    (fun n s => s.pc = swapfunc + 0x4 ∧ n < s0.regs.X2.toNat ∧
      ∃ x4 x5 st m,
      (m =⋆ Eq ((bs.take n ++ as.drop n).At s0.regs.X0.toBitVec) ⋆
        (Eq ((as.take n ++ bs.drop n).At s0.regs.X1.toBitVec) ⋆ R)) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X3 := .ofNat n
          X4 := x4
          X5 := x5 }
        status := st
        dmem := m })
    _ 0 _ ⟨rfl, h_pos, _, _, _, _,
      by simpa [Std.ExtHashMap.sep_assoc] using h_mem, by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, x4, x5, st, m, hm, rfl⟩
  have hm2 := hm
  rw [Std.ExtHashMap.sep_comm_l] at hm2
  have hla : (bs.take n ++ as.drop n).length = s0.regs.X2.toNat := by
    simp; omega
  have hlb : (as.take n ++ bs.drop n).length = s0.regs.X2.toNat := by
    simp; omega
  instr "ldrb w5, [x1, x3]" at swapfunc + 0x4
  load_byte hm2 (by omega)
  instr "ldrb w4, [x0, x3]" at swapfunc + 0x8
  load_byte hm (by omega)
  simp (disch := omega) only [List.getElem_take_append_drop]
  instr "strb w5, [x0, x3]" at swapfunc + 0xc
  store_byte hm
  have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by omega) (by omega)
    (bs[n]'(by omega))
  rw [List.set_take_append_drop (by omega) (by omega),
    Std.ExtHashMap.sep_comm_l] at hm'
  instr "strb w4, [x1, x3]" at swapfunc + 0x10
  store_byte hm'
  have hm'' := Mem.storeInt_byte_sep _ _ n _ _ hm' (by omega) (by omega)
    (as[n]'(by omega))
  rw [List.set_take_append_drop (by omega) (by omega),
    Std.ExtHashMap.sep_comm_l] at hm''
  instr "add x3, x3, #0x1" at swapfunc + 0x14
  instr "cmp x2, x3" at swapfunc + 0x18
  instr "b.ne 4 <swapfunc+0x4>" at swapfunc + 0x1c
  · intro hne
    have hlt : n + 1 < s0.regs.X2.toNat := by
      refine Nat.lt_of_le_of_ne hn fun he => ?_
      rw [← UInt64.ofNat_eq_iff (by omega)] at he
      rw [← he] at hne
      simp [UInt64.ofNat_add] at hne
    refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, _, _, _, _, hm'',
      by state_eq⟩)
    simp only [InvImage, WellFoundedRelation.rel]; omega
  · intro heq
    have he : n + 1 = s0.regs.X2.toNat := by
      rw [← UInt64.ofNat_eq_iff (by omega)]
      apply UInt64.toBitVec_inj.mp
      simp only [Bool.not_eq_true, Bool.not_eq_false', beq_iff_eq,
        BitVec.zero_eq, UInt64.toBitVec_ofNat'] at heq
      simp only [UInt64.ofNat_add, UInt64.toBitVec_add,
        UInt64.toBitVec_ofNat']
      bv_decide
    rw [he, List.take_of_length_le (by omega),
      List.drop_of_length_le (by omega), List.append_nil,
      List.take_of_length_le (by omega),
      List.drop_of_length_le (by omega), List.append_nil] at hm''
    instr "ret" at swapfunc + 0x20
    exact .done _ (.inr ⟨rfl, _, _, _, _, hm'',
      by rw [← UInt64.ofNat_toNat (x := s0.regs.X2), ← he]; state_eq⟩)
