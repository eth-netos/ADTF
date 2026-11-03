module

import ADTF.AtfLibc.Listing.memcmp_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `memcmp` from TF-A's `libc/memcmp.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `memcmp` in ATF's `memcmp.o`. -/
def memcmp_o : List Instr := objdumpAArch64(memcmp_o_dump)

/-- `memcmp` compares the `x2` bytes at `x0` and `x1`. Up to index `r`
they are equal; it returns 0 if `r` is `x2`, and otherwise the difference
`byteDiff` of the first bytes that differ. The two buffers may overlap. It
changes only `x0`, `x1` (to `x1 - 1`), `x3`, `x4`, `x5` and the flags. -/
theorem memcmp_spec [Labels] (code : Code) (memcmp : Int64)
    (h : Loaded code memcmp memcmp_o)
    (h_sym : label "memcmp" = memcmp)
    (s0 : MachineData) (as bs : List UInt8) (R1 R2 : DataMem → Prop)
    (h_as : s0.regs.X2.toNat ≤ as.length)
    (h_bs : s0.regs.X2.toNat ≤ bs.length)
    (h_len1 : as.length ≤ 2 ^ 64) (h_len2 : bs.length ≤ 2 ^ 64)
    (h_mem1 : s0.dmem =⋆ Eq (as.At s0.regs.X0.toBitVec) ⋆ R1)
    (h_mem2 : s0.dmem =⋆ Eq (bs.At s0.regs.X1.toBitVec) ⋆ R2) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r x0,
      r ≤ s0.regs.X2.toNat ∧ (∀ i < r, as[i]? = bs[i]?) ∧
      (r = s0.regs.X2.toNat ∧ x0 = 0 ∨
        ∃ a b, as[r]? = some a ∧ bs[r]? = some b ∧ a ≠ b ∧
          x0 = byteDiff a b) ∧
      ∃ x3 x4 x5 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 - 1
          X3 := x3
          X4 := x4
          X5 := x5 }
        status := st })
    ⟨s0, memcmp⟩ := by
  instr "sub x1, x1, #0x1" at memcmp
  instr "mov x4, #0x0" at memcmp + 0x4
  have hX2 := s0.regs.X2.toNat_lt
  refine loop_rule (measure fun n => s0.regs.X2.toNat + 1 - n).wf
    (fun n s => s.pc = memcmp + 0x8 ∧ n ≤ s0.regs.X2.toNat ∧
      (∀ i < n, as[i]? = bs[i]?) ∧
      ∃ x3 x5 st, s.data = { s0 with
        regs := { s0.regs with
          X1 := s0.regs.X1 - 1
          X3 := x3
          X4 := .ofNat n
          X5 := x5 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _, by simp, _, _, _,
      by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, hz, x3, x5, st, rfl⟩
  instr "cmp x2, x4" at memcmp + 0x8
  instr "b.ne 18 <memcmp+0x18>" at memcmp + 0xc
  · intro hne
    have hlt : n < s0.regs.X2.toNat := by
      refine Nat.lt_of_le_of_ne hn fun he => ?_
      rw [← UInt64.ofNat_eq_iff (by omega)] at he
      rw [he] at hne
      simp at hne
    instr "ldrb w3, [x0, x4]" at memcmp + 0x18
    load_byte h_mem1 h_len1
    instr "add x4, x4, #0x1" at memcmp + 0x1c
    instr "ldrb w5, [x1, x4]" at memcmp + 0x20
    simp only [ofInt_toNat64, UInt64.toBitVec_ofNat', sub_one_add_add_one]
    load_byte h_mem2 h_len2
    instr "cmp w3, w5" at memcmp + 0x24
    instr "b.eq 8 <memcmp+0x8>" at memcmp + 0x28
    · intro heq
      rw [ldrb_cmp_ldrb_eq_iff] at heq
      refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, ?_, _, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · simp [show i < as.length by omega, show i < bs.length by omega,
            heq]
    · intro hne
      rw [ldrb_cmp_ldrb_eq_iff] at hne
      instr "sub w0, w3, w5" at memcmp + 0x2c
      instr "ret" at memcmp + 0x30
      exact .done _ (.inr ⟨rfl, n, _, hn, hz,
        .inr ⟨_, _, by simp [show n < as.length by omega],
          by simp [show n < bs.length by omega], hne, rfl⟩, _, _, _, _,
        by unfold byteDiff; state_eq⟩)
  · intro heq
    have he : n = s0.regs.X2.toNat := by
      rw [UInt64.ofNat_eq_iff (by omega) |>.symm]
      apply UInt64.toBitVec_inj.mp
      simp at heq
      bv_decide
    instr "mov w0, #0x0" at memcmp + 0x10
    instr "b 30 <memcmp+0x30>" at memcmp + 0x14
    instr "ret" at memcmp + 0x30
    exact .done _ (.inr ⟨rfl, n, _, hn, hz, .inl ⟨he, rfl⟩, _, _, _, _,
      by state_eq⟩)
