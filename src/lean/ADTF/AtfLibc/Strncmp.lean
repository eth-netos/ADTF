module

import ADTF.AtfLibc.Listing.strncmp_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strncmp` from TF-A's `libc/strncmp.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strncmp` in ATF's `strncmp.o`. -/
def strncmp_o : List Instr := objdumpAArch64(strncmp_o_dump)

/-- `strncmp` compares at most `x2` bytes of the strings at `x0` and `x1`,
like `strcmp`, and returns 0 if the first `x2` bytes are equal. It changes
only `x0`, `x3`, `x4`, `x5` and the flags. -/
theorem strncmp_spec [Labels] (code : Code) (strncmp : Int64)
    (h : Loaded code strncmp strncmp_o)
    (h_sym : label "strncmp" = strncmp)
    (s0 : MachineData) (as bs : List UInt8) (R1 R2 : DataMem → Prop)
    (h_as : s0.regs.X2.toNat ≤ as.length ∨ 0 ∈ as)
    (h_bs : s0.regs.X2.toNat ≤ bs.length ∨ 0 ∈ bs)
    (h_len1 : as.length ≤ 2 ^ 64) (h_len2 : bs.length ≤ 2 ^ 64)
    (h_mem1 : s0.dmem =⋆ Eq (as.At s0.regs.X0.toBitVec) ⋆ R1)
    (h_mem2 : s0.dmem =⋆ Eq (bs.At s0.regs.X1.toBitVec) ⋆ R2) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r x0,
      r ≤ s0.regs.X2.toNat ∧
      (∀ i < r, as[i]? = bs[i]? ∧ as[i]? ≠ some 0) ∧
      (r = s0.regs.X2.toNat ∧ x0 = 0 ∨
        ∃ a b, as[r]? = some a ∧ bs[r]? = some b ∧
          (a = b ∧ a = 0 ∧ x0 = 0 ∨ a ≠ b ∧ x0 = byteDiff a b)) ∧
      ∃ x3 x4 x5 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X3 := x3
          X4 := x4
          X5 := x5 }
        status := st })
    ⟨s0, strncmp⟩ := by
  have hX2 := s0.regs.X2.toNat_lt
  instr "cbz x2, 30 <strncmp+0x30>" at strncmp
  · intro h0
    have h0' : s0.regs.X2.toNat = 0 := by
      have : s0.regs.X2 = 0 := UInt64.toBitVec_inj.mp (by simpa using h0)
      simp [this]
    instr "mov w0, #0x0" at strncmp + 0x30
    instr "b 1c <strncmp+0x1c>" at strncmp + 0x34
    instr "ret" at strncmp + 0x1c
    exact .done _ ⟨rfl, 0, _, by omega, by simp, .inl ⟨h0'.symm, rfl⟩,
      _, _, _, _, by state_eq⟩
  · intro h0
    have hpos : 0 < s0.regs.X2.toNat := by
      refine Nat.pos_of_ne_zero fun he => h0 ?_
      have : s0.regs.X2 = 0 := UInt64.toNat_inj.mp (by simpa using he)
      simp [this]
    instr "mov x4, #0x0" at strncmp + 0x4
    refine loop_rule (measure fun n => s0.regs.X2.toNat - n).wf
      (fun n s => s.pc = strncmp + 0x8 ∧ n < s0.regs.X2.toNat ∧
        (∀ i < n, as[i]? = bs[i]? ∧ as[i]? ≠ some 0) ∧
        ∃ x3 x5 st, s.data = { s0 with
          regs := { s0.regs with
            X3 := x3
            X4 := .ofNat n
            X5 := x5 }
          status := st })
      _ 0 _ ⟨by dsimp only; bv_decide, hpos, by simp, _, _, _,
        by state_eq⟩ ?_
    rintro n ⟨d, pc⟩ ⟨rfl, hn, hz, x3, x5, st, rfl⟩
    have ha : n < as.length :=
      lt_length_of_no_zero (fun i hi => (hz i hi).2) hn h_as
    have hb : n < bs.length :=
      lt_length_of_no_zero (fun i hi => (hz i hi).1 ▸ (hz i hi).2) hn h_bs
    instr "ldrb w3, [x0, x4]" at strncmp + 0x8
    load_byte h_mem1 h_len1
    instr "ldrb w5, [x1, x4]" at strncmp + 0xc
    load_byte h_mem2 h_len2
    instr "cmp w3, w5" at strncmp + 0x10
    instr "b.eq 20 <strncmp+0x20>" at strncmp + 0x14
    · intro heq
      rw [ldrb_cmp_ldrb_eq_iff] at heq
      instr "cbz w3, 30 <strncmp+0x30>" at strncmp + 0x20
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        instr "mov w0, #0x0" at strncmp + 0x30
        instr "b 1c <strncmp+0x1c>" at strncmp + 0x34
        instr "ret" at strncmp + 0x1c
        exact .done _ (.inr ⟨rfl, n, _, by omega, hz,
          .inr ⟨_, _, by simp [ha], by simp [hb], .inl ⟨heq, h_b, rfl⟩⟩,
          _, _, _, _, by state_eq⟩)
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        have hz' : ∀ i < n + 1, as[i]? = bs[i]? ∧ as[i]? ≠ some 0 := by
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hz i hi
          · exact ⟨by simp [ha, hb, heq], by simp [ha, h_b]⟩
        instr "add x4, x4, #0x1" at strncmp + 0x24
        instr "cmp x2, x4" at strncmp + 0x28
        instr "b.ne 8 <strncmp+0x8>" at strncmp + 0x2c
        · intro hne
          have hlt : n + 1 < s0.regs.X2.toNat := by
            refine Nat.lt_of_le_of_ne hn fun he => ?_
            rw [← UInt64.ofNat_eq_iff (by omega)] at he
            rw [← he] at hne
            simp [UInt64.ofNat_add] at hne
          refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, hz', _, _, _,
            by state_eq⟩)
          simp only [InvImage, WellFoundedRelation.rel]; omega
        · intro heq'
          have he : n + 1 = s0.regs.X2.toNat := by
            rw [← UInt64.ofNat_eq_iff (by omega)]
            apply UInt64.toBitVec_inj.mp
            simp only [Bool.not_eq_true, Bool.not_eq_false', beq_iff_eq,
              BitVec.zero_eq, UInt64.toBitVec_ofNat'] at heq'
            simp only [UInt64.ofNat_add, UInt64.toBitVec_add,
              UInt64.toBitVec_ofNat']
            bv_decide
          instr "mov w0, #0x0" at strncmp + 0x30
          instr "b 1c <strncmp+0x1c>" at strncmp + 0x34
          instr "ret" at strncmp + 0x1c
          exact .done _ (.inr ⟨rfl, n + 1, _, by omega, hz',
            .inl ⟨he, rfl⟩, _, _, _, _, by state_eq⟩)
    · intro hne
      rw [ldrb_cmp_ldrb_eq_iff] at hne
      instr "sub w0, w3, w5" at strncmp + 0x18
      instr "ret" at strncmp + 0x1c
      exact .done _ (.inr ⟨rfl, n, _, by omega, hz,
        .inr ⟨_, _, by simp [ha], by simp [hb], .inr ⟨hne, rfl⟩⟩,
        _, _, _, _, by unfold byteDiff; state_eq⟩)
