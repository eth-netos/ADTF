module

import ADTF.AtfLibc.Listing.memcpy_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `memcpy` from TF-A's `libc/memcpy.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `memcpy` in ATF's `memcpy.o`. -/
def memcpy_o : List Instr := objdumpAArch64(memcpy_o_dump)

/-- `memcpy` copies the `x2` bytes at `x1` to the disjoint buffer at `x0`,
and returns `x0`. It changes only `x3` (to `x2`), `x4`, the flags and the
destination buffer. -/
theorem memcpy_spec [Labels] (code : Code) (memcpy : Int64)
    (h : Loaded code memcpy memcpy_o)
    (h_sym : label "memcpy" = memcpy)
    (s0 : MachineData) (dst src : List UInt8) (R : DataMem → Prop)
    (h_dst : dst.length = s0.regs.X2.toNat)
    (h_src : src.length = s0.regs.X2.toNat)
    (h_mem : s0.dmem =⋆ Eq (dst.At s0.regs.X0.toBitVec) ⋆
      Eq (src.At s0.regs.X1.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x4 st m,
      (m =⋆ Eq (src.At s0.regs.X0.toBitVec) ⋆
        (Eq (src.At s0.regs.X1.toBitVec) ⋆ R)) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X3 := s0.regs.X2
          X4 := x4 }
        status := st
        dmem := m })
    ⟨s0, memcpy⟩ := by
  have hX2 := s0.regs.X2.toNat_lt
  instr "mov x3, #0x0" at memcpy
  refine loop_rule (measure fun n => s0.regs.X2.toNat + 1 - n).wf
    (fun n s => s.pc = memcpy + 0x4 ∧ n ≤ s0.regs.X2.toNat ∧
      ∃ x4 st m,
      (m =⋆ Eq ((src.take n ++ dst.drop n).At s0.regs.X0.toBitVec) ⋆
        (Eq (src.At s0.regs.X1.toBitVec) ⋆ R)) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X3 := .ofNat n
          X4 := x4 }
        status := st
        dmem := m })
    _ 0 _ ⟨rfl, Nat.zero_le _, _, _, _,
      by simpa [Std.ExtHashMap.sep_assoc] using h_mem,
      by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, x4, st, m, hm, rfl⟩
  instr "cmp x2, x3" at memcpy + 0x4
  instr "b.ne 10 <memcpy+0x10>" at memcpy + 0x8
  · intro hne
    have hlt : n < s0.regs.X2.toNat := by
      refine Nat.lt_of_le_of_ne hn fun he => ?_
      rw [← UInt64.ofNat_eq_iff (by omega)] at he
      rw [he] at hne
      simp at hne
    have hm2 : m =⋆ Eq (src.At s0.regs.X1.toBitVec) ⋆
        (Eq ((src.take n ++ dst.drop n).At s0.regs.X0.toBitVec) ⋆ R) := by
      rwa [Std.ExtHashMap.sep_comm_l]
    have hl : (src.take n ++ dst.drop n).length = s0.regs.X2.toNat := by
      simp; omega
    instr "ldrb w4, [x1, x3]" at memcpy + 0x10
    load_byte hm2 (by omega)
    instr "strb w4, [x0, x3]" at memcpy + 0x14
    store_byte hm
    have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by omega) (by omega)
      src[n]
    rw [List.set_take_append_drop (by omega) (by omega)] at hm'
    instr "add x3, x3, #0x1" at memcpy + 0x18
    instr "b 4 <memcpy+0x4>" at memcpy + 0x1c
    refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, _, _, _, hm',
      by state_eq⟩)
    simp only [InvImage, WellFoundedRelation.rel]; omega
  · intro heq
    have he : n = s0.regs.X2.toNat := by
      rw [← UInt64.ofNat_eq_iff (by omega)]
      apply UInt64.toBitVec_inj.mp
      simp at heq
      bv_decide
    subst he
    rw [List.take_of_length_le (by omega),
      List.drop_of_length_le (by omega), List.append_nil] at hm
    instr "ret" at memcpy + 0xc
    exact .done _ (.inr ⟨rfl, _, _, _, hm, by state_eq⟩)
