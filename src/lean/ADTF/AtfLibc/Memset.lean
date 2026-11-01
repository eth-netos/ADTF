module

import ADTF.AtfLibc.Listing.memset_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `memset` from TF-A's `libc/memset.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `memset` in ATF's `memset.o`. -/
def memset_o : List Instr := objdumpAArch64(memset_o_dump)

/-- `memset` fills the `x2` bytes at `x0` with the low byte of `x1`, and
returns `x0`. It changes only `x1` to `x6`, the flags and the buffer. -/
theorem memset_spec [Labels] (code : Code) (memset : Int64)
    (h : Loaded code memset memset_o)
    (h_sym : label "memset" = memset)
    (s0 : MachineData) (old : List UInt8) (R : DataMem → Prop)
    (h_old : old.length = s0.regs.X2.toNat)
    (h_mem : s0.dmem =⋆ Eq (old.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x1 x2 x3 x4 x5 x6 st m,
      (m =⋆ Eq ((List.replicate s0.regs.X2.toNat s0.regs.X1.toUInt8).At
        s0.regs.X0.toBitVec) ⋆ R) ∧
      s.data = { s0 with
        regs := { s0.regs with
          X1 := x1
          X2 := x2
          X3 := x3
          X4 := x4
          X5 := x5
          X6 := x6 }
        status := st
        dmem := m })
    ⟨s0, memset⟩ := by
  have hX2 := s0.regs.X2.toNat_lt
  instr "cbz x2, 58 <memset+0x58>" at memset
  · intro h_x2
    have h0 : s0.regs.X2.toNat = 0 := by rw [UInt64.toNat, h_x2]; rfl
    have h_nil : old = [] := List.eq_nil_of_length_eq_zero (h_old.trans h0)
    subst h_nil
    rw [h_sym]
    instr "ret" at memset + 0x58
    exact .done _ ⟨rfl, _, _, _, _, _, _, _, _, by simpa [h0] using h_mem,
      rfl⟩
  · intro h_x2
    have h_pos : 0 < s0.regs.X2.toNat := by
      rw [UInt64.toNat]
      exact Nat.pos_of_ne_zero fun h0 => h_x2 (BitVec.eq_of_toNat_eq h0)
    instr "and w1, w1, #0xff" at memset + 0x4
    instr "mov x3, x0" at memset + 0x8
    refine loop_rule (measure fun n => s0.regs.X2.toNat - n).wf
      (fun n s => s.pc = memset + 0xc ∧ n < s0.regs.X2.toNat ∧
        ∃ x4 st m,
        (m =⋆ Eq ((List.replicate n s0.regs.X1.toUInt8 ++ old.drop n).At
          s0.regs.X0.toBitVec) ⋆ R) ∧
        s.data = { s0 with
          regs := { s0.regs with
            X1 := ⟨BitVec.zeroExtend 64
              (s0.regs.X1.toUInt8.toBitVec.zeroExtend 32)⟩
            X2 := s0.regs.X2 - .ofNat n
            X3 := s0.regs.X0 + .ofNat n
            X4 := x4 }
          status := st
          dmem := m })
      _ 0 _ ⟨by dsimp only; bv_decide, h_pos, s0.regs.X4, s0.status, s0.dmem,
        by simpa using h_mem,
        ?_⟩ ?_
    · dsimp only
      congr 2 <;> first | rfl | uint64_eq |
        (apply UInt64.toBitVec_inj.mp
         simp only [UInt64.toBitVec_toUInt8]
         bv_decide)
    rintro n ⟨d, pc⟩ ⟨rfl, hn, x4, st, m, hm, rfl⟩
    instr "ands x4, x3, #0x7" at memset + 0xc
    instr "b.ne 4c <memset+0x4c>" at memset + 0x10
    · intro h_al
      rw [h_sym]
      instr "strb w1, [x3], #1" at memset + 0x4c
      store_byte hm
      have hm' := Mem.storeInt_byte_sep _ _ n _ m hm (by simp; omega)
        (by simp; omega) s0.regs.X1.toUInt8
      rw [List.set_replicate_append_drop _ (by omega)] at hm'
      instr "subs x2, x2, #0x1" at memset + 0x50
      instr "b.ne c <memset+0xc>" at memset + 0x54
      · intro hne
        have hlt := subs_count_ne hn hne
        refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, _, _, _, hm',
          by state_eq⟩)
        simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro heq
        have he := subs_count_eq hn heq
        rw [he, List.drop_of_length_le (by omega), List.append_nil] at hm'
        instr "ret" at memset + 0x58
        exact .done _ (.inr ⟨rfl, _, _, _, _, _, _, _, _, hm', rfl⟩)
    · intro h_al
      instr "mov w5, w1" at memset + 0x14
      instr "mov x6, #0x101010101010101" at memset + 0x18
      instr "mul x5, x5, x6" at memset + 0x1c
      refine loop_rule (measure fun q => s0.regs.X2.toNat - n - q).wf
        (fun q s => s.pc = memset + 0x20 ∧ q % 8 = 0 ∧
          q ≤ s0.regs.X2.toNat - n ∧ ∃ x6 st m,
          (m =⋆ Eq ((List.replicate (n + q) s0.regs.X1.toUInt8 ++
            old.drop (n + q)).At s0.regs.X0.toBitVec) ⋆ R) ∧
          s.data = { s0 with
            regs := { s0.regs with
              X1 := ⟨BitVec.zeroExtend 64
                (s0.regs.X1.toUInt8.toBitVec.zeroExtend 32)⟩
              X2 := s0.regs.X2 - .ofNat n
              X3 := s0.regs.X0 + .ofNat n
              X4 := .ofNat q
              X5 := ⟨s0.regs.X1.toUInt8.toBitVec.zeroExtend 64 *
                0x101010101010101#64⟩
              X6 := x6 }
            status := st
            dmem := m })
        _ 0 _ ⟨by dsimp only; bv_decide, rfl, Nat.zero_le _, _, _, _,
          by simpa using hm, by
            simp only [Bool.not_eq_true, Bool.not_eq_false', beq_iff_eq,
              BitVec.zero_eq] at h_al
            dsimp only
            congr 2 <;> first | rfl |
              (apply UInt64.toBitVec_inj.mp
               simp only [UInt64.toBitVec_add, UInt64.toBitVec_toUInt8,
                 UInt64.toBitVec_ofNat'] at h_al ⊢
               bv_decide)⟩ ?_
      rintro q ⟨d, pc⟩ ⟨rfl, hq8, hq, x6, st, m, hm, rfl⟩
      instr "sub x6, x2, x4" at memset + 0x20
      instr "cmp x6, #0x7" at memset + 0x24
      instr "b.hi 5c <memset+0x5c>" at memset + 0x28
      · intro hhi
        rw [cmp_hi_iff] at hhi
        simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat'] at hhi
        have hlt : 8 ≤ s0.regs.X2.toNat - n - q := by
          rw [← UInt64.toNat_toBitVec] at *
          bv_omega
        rw [h_sym]
        have ha : (s0.regs.X0 + UInt64.ofNat n).toBitVec +
            BitVec.ofInt 64 ↑(UInt64.ofNat q).toBitVec.toNat =
            s0.regs.X0.toBitVec + BitVec.ofNat 64 (n + q) := by
          simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat', ofInt_toNat64,
            BitVec.ofNat_add, BitVec.add_assoc]
        instr "str x5, [x3, x4]" at memset + 0x5c
        rw [ha]
        simp (disch := first | rfl | (simp [MemWidth.bytes]; omega)) only
          [MachineData.store_of_sep64 hm, Effects.All, MemWidth.bytes]
        have hm' := Mem.storeInt_slice_sep _ _ (n + q) 8 _ m hm
          (by simp; omega) (by simp; omega)
          (s0.regs.X1.toUInt8.toBitVec.zeroExtend 64 *
            0x101010101010101#64).toInt
        rw [Int.toBytes_fill, List.replicate_append_drop_store]
          at hm'
        instr "add x4, x4, #0x8" at memset + 0x60
        instr "b 20 <memset+0x20>" at memset + 0x64
        refine .done _ (.inl ⟨q + 8, ?_, by rw [h_sym], by omega, by omega, _,
          _, _, by rw [← Nat.add_assoc]; exact hm', by state_eq⟩)
        simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro hhi
        rw [cmp_hi_iff] at hhi
        simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat'] at hhi
        have hle : s0.regs.X2.toNat - n - q ≤ 7 := by
          rw [← UInt64.toNat_toBitVec] at *
          bv_omega
        instr "and x4, x2, #0xfffffffffffffff8" at memset + 0x2c
        instr "and x2, x2, #0x7" at memset + 0x30
        instr "add x3, x3, x4" at memset + 0x34
        instr "add x2, x2, x3" at memset + 0x38
        have hr : (s0.regs.X2 - UInt64.ofNat n).toBitVec.toNat =
            s0.regs.X2.toNat - n := by
          rw [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat']
          rw [← UInt64.toNat_toBitVec] at *
          bv_omega
        have hmask := and_neg8_eq (r := (s0.regs.X2 - UInt64.ofNat n).toBitVec)
          hq8 (by omega) (by omega)
        refine loop_rule (measure fun k => s0.regs.X2.toNat - k).wf
          (fun k s => s.pc = memset + 0x3c ∧ k ≤ s0.regs.X2.toNat ∧
            ∃ x4 x6 st m,
            (m =⋆ Eq ((List.replicate k s0.regs.X1.toUInt8 ++
              old.drop k).At s0.regs.X0.toBitVec) ⋆ R) ∧
            s.data = { s0 with
              regs := { s0.regs with
                X1 := ⟨BitVec.zeroExtend 64
                  (s0.regs.X1.toUInt8.toBitVec.zeroExtend 32)⟩
                X2 := s0.regs.X0 + s0.regs.X2
                X3 := s0.regs.X0 + .ofNat k
                X4 := x4
                X5 := ⟨s0.regs.X1.toUInt8.toBitVec.zeroExtend 64 *
                  0x101010101010101#64⟩
                X6 := x6 }
              status := st
              dmem := m })
          _ (n + q) _ ⟨by dsimp only; bv_decide, by omega, _, _, _, _, hm, by
            dsimp only
            congr 2 <;> first | rfl |
              (apply UInt64.toBitVec_inj.mp
               simp only [UInt64.ofNat_add, UInt64.toBitVec_add,
                 UInt64.toBitVec_sub, UInt64.toBitVec_ofNat'] at hmask ⊢
               bv_decide)⟩ ?_
        rintro k ⟨d, pc⟩ ⟨rfl, hk, x4, x6, st, m, hm, rfl⟩
        instr "cmp x3, x2" at memset + 0x3c
        instr "b.eq 58 <memset+0x58>" at memset + 0x40
        · intro heq
          have he : k = s0.regs.X2.toNat := by
            simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat',
              BitVec.zero_eq] at heq
            rw [← UInt64.toNat_toBitVec] at *
            bv_omega
          rw [he, List.drop_of_length_le (by omega), List.append_nil] at hm
          rw [h_sym]
          instr "ret" at memset + 0x58
          exact .done _ (.inr (.inr (.inr ⟨rfl, _, _, _, _, _, _, _, _, hm,
            rfl⟩)))
        · intro hne
          have hlt : k < s0.regs.X2.toNat := by
            refine Nat.lt_of_le_of_ne hk fun he => hne ?_
            simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat',
              BitVec.zero_eq]
            rw [← UInt64.toNat_toBitVec] at *
            bv_omega
          instr "strb w1, [x3], #1" at memset + 0x44
          store_byte hm
          have hm' := Mem.storeInt_byte_sep _ _ k _ m hm (by simp; omega)
            (by simp; omega) s0.regs.X1.toUInt8
          rw [List.set_replicate_append_drop _ (by omega)] at hm'
          instr "b 3c <memset+0x3c>" at memset + 0x48
          refine .done _ (.inl ⟨k + 1, ?_, by rw [h_sym], by omega, _, _, _,
            _, hm', by state_eq⟩)
          simp only [InvImage, WellFoundedRelation.rel]; omega
