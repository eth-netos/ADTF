module

import ADTF.AtfLibc.Listing.strcmp_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strcmp` from TF-A's `libc/strcmp.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strcmp` in ATF's `strcmp.o`. -/
def strcmp_o : List Instr := objdumpAArch64(strcmp_o_dump)

/-- `strcmp` compares the NUL-terminated strings at `x0` and `x1`. Up to
index `r` they are equal and nonzero; it returns 0 if both have a 0 at `r`,
and otherwise the difference `byteDiff` of the bytes at `r`. It changes only
`x0`, `x2`, `x3`, `x4` and the flags. -/
theorem strcmp_spec [Labels] (code : Code) (strcmp : Int64)
    (h : Loaded code strcmp strcmp_o)
    (h_sym : label "strcmp" = strcmp)
    (s0 : MachineData) (as bs : List UInt8) (R1 R2 : DataMem → Prop)
    (h_as : 0 ∈ as) (h_bs : 0 ∈ bs)
    (h_len1 : as.length ≤ 2 ^ 64) (h_len2 : bs.length ≤ 2 ^ 64)
    (h_mem1 : s0.dmem =⋆ Eq (as.At s0.regs.X0.toBitVec) ⋆ R1)
    (h_mem2 : s0.dmem =⋆ Eq (bs.At s0.regs.X1.toBitVec) ⋆ R2) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ (r : Nat) (x0 : UInt64),
      (∀ i < r, as[i]? = bs[i]? ∧ as[i]? ≠ some 0) ∧
      (∃ a b, as[r]? = some a ∧ bs[r]? = some b ∧
        (a = b ∧ a = 0 ∧ x0 = 0 ∨ a ≠ b ∧ x0 = byteDiff a b)) ∧
      ∃ x2 x3 x4 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X2 := x2
          X3 := x3
          X4 := x4 }
        status := st })
    ⟨s0, strcmp⟩ := by
  instr "mov x3, #0x0" at strcmp
  refine loop_rule (measure fun n => as.length - n).wf
    (fun n s => s.pc = strcmp + 0x4 ∧
      (∀ i < n, as[i]? = bs[i]? ∧ as[i]? ≠ some 0) ∧
      ∃ x2 x4 st, s.data = { s0 with
        regs := { s0.regs with
          X2 := x2
          X3 := .ofNat n
          X4 := x4 }
        status := st })
    _ 0 _ ⟨rfl, by simp, _, _, _, by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hz, x2, x4, st, rfl⟩
  have ha : n < as.length :=
    lt_length_of_forall_ne (fun i hi => (hz i hi).2) h_as
  have hb : n < bs.length :=
    lt_length_of_forall_ne (fun i hi => (hz i hi).1 ▸ (hz i hi).2) h_bs
  instr "ldrb w2, [x0, x3]" at strcmp + 0x4
  load_byte h_mem1 h_len1
  instr "ldrb w4, [x1, x3]" at strcmp + 0x8
  load_byte h_mem2 h_len2
  instr "cmp w2, w4" at strcmp + 0xc
  instr "b.eq 1c <strcmp+0x1c>" at strcmp + 0x10
  · intro heq
    rw [ldrb_cmp_ldrb_eq_iff] at heq
    instr "add x3, x3, #0x1" at strcmp + 0x1c
    instr "cbnz w2, 4 <strcmp+0x4>" at strcmp + 0x20
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], ?_, _, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · exact ⟨by simp [ha, hb, heq], by simp [ha, h_b]⟩
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "mov w0, #0x0" at strcmp + 0x24
      instr "b 18 <strcmp+0x18>" at strcmp + 0x28
      instr "ret" at strcmp + 0x18
      exact .done _ (.inr ⟨rfl, n, _, hz, ⟨_, _, by simp [ha], by simp [hb],
        .inl ⟨heq, h_b, rfl⟩⟩, _, _, _, _, by state_eq⟩)
  · intro hne
    rw [ldrb_cmp_ldrb_eq_iff] at hne
    instr "sub w0, w2, w4" at strcmp + 0x14
    instr "ret" at strcmp + 0x18
    exact .done _ (.inr ⟨rfl, n, _, hz, ⟨_, _, by simp [ha], by simp [hb],
      .inr ⟨hne, rfl⟩⟩, _, _, _, _, by unfold byteDiff; state_eq⟩)
