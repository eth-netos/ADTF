module

import ADTF.AtfLibc.Listing.memrchr_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `memrchr` from TF-A's `libc/memrchr.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `memrchr` in ATF's `memrchr.o`. -/
def memrchr_o : List Instr := objdumpAArch64(memrchr_o_dump)

/-- `memrchr` searches the `x2` bytes at `x0` backwards for the low byte of
`x1`, and returns the address of its last occurrence, or the null pointer if
there is none. It changes only `x0`, `x1` (to its low byte), `x2`, `x3`, `x4`
and the flags. -/
theorem memrchr_spec [Labels] (code : Code) (memrchr : Int64)
    (h : Loaded code memrchr memrchr_o)
    (h_sym : label "memrchr" = memrchr)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : s0.regs.X2.toNat ≤ bs.length)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ x0,
      IsLastMatch bs s0.regs.X1.toUInt8 s0.regs.X0 s0.regs.X2.toNat x0 ∧
      ∃ x3 x4 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 - 1
          X3 := x3
          X4 := x4 }
        status := st })
    ⟨s0, memrchr⟩ := by
  instr "sub x3, x2, #0x1" at memrchr
  instr "and w1, w1, #0xff" at memrchr + 0x4
  instr "add x3, x0, x3" at memrchr + 0x8
  instr "sub x2, x3, x2" at memrchr + 0xc
  have hX2 := s0.regs.X2.toNat_lt
  refine loop_rule (measure fun k => k).wf
    (fun k s => s.pc = memrchr + 0x10 ∧ k ≤ s0.regs.X2.toNat ∧
      (∀ i < s0.regs.X2.toNat, k ≤ i →
        bs[i]? ≠ some s0.regs.X1.toUInt8) ∧
      ∃ x0 x4 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 - 1
          X3 := s0.regs.X0 + .ofNat k - 1
          X4 := x4 }
        status := st })
    _ s0.regs.X2.toNat _ ⟨by dsimp only; bv_decide, Nat.le_refl _,
      fun i hi hk => absurd hi (by omega), _, _, _, by state_eq⟩ ?_
  rintro k ⟨d, pc⟩ ⟨rfl, hk, hz, x0, x4, st, rfl⟩
  instr "mov x0, x3" at memrchr + 0x10
  instr "cmp x3, x2" at memrchr + 0x14
  instr "b.ne 24 <memrchr+0x24>" at memrchr + 0x18
  · intro hne
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => ?_)
      subst h0
      simp at hne
    rw [show s0.regs.X0 + .ofNat (j + 1) - 1 = s0.regs.X0 + .ofNat j
      by uint64_eq]
    instr "ldrb w4, [x0]" at memrchr + 0x24
    load_byte h_mem h_len
    instr "sub x3, x3, #0x1" at memrchr + 0x28
    instr "cmp w4, w1" at memrchr + 0x2c
    instr "b.ne 10 <memrchr+0x10>" at memrchr + 0x30
    · intro hc
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hc
      rw [ldrb_cmp_and_eq_iff] at hc
      refine .done _ (.inl ⟨j, ?_, by rw [h_sym], by omega, ?_, _, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi hji
        rcases Nat.lt_or_eq_of_le hji with hji | rfl
        · exact hz i hi hji
        · simp [show j < bs.length by omega, hc]
    · intro hc
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Decidable.not_not] at hc
      rw [ldrb_cmp_and_eq_iff] at hc
      instr "ret" at memrchr + 0x34
      exact .done _ (.inr ⟨rfl, _, .inr ⟨j, by omega,
        by simp [show j < bs.length by omega, hc], rfl,
        fun i hi hji => hz i hi hji⟩, _, _, _, by state_eq⟩)
  · intro heq
    have h0 : k = 0 := by
      have : UInt64.ofNat k = 0 := by
        apply UInt64.toBitVec_inj.mp
        simp at heq
        simp only [UInt64.toBitVec_zero]
        bv_decide
      simpa using (UInt64.ofNat_eq_iff (by omega)).mp this
    subst h0
    instr "mov x0, #0x0" at memrchr + 0x1c
    instr "b 34 <memrchr+0x34>" at memrchr + 0x20
    instr "ret" at memrchr + 0x34
    exact .done _ (.inr ⟨rfl, 0,
      .inl ⟨rfl, fun i hi => hz i hi (by omega)⟩,
      _, _, _, by state_eq⟩)
