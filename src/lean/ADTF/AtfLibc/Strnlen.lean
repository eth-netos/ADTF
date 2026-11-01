module

import ADTF.AtfLibc.Listing.strnlen_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strnlen` from TF-A's `libc/strnlen.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strnlen` in ATF's `strnlen.o`. -/
def strnlen_o : List Instr := objdumpAArch64(strnlen_o_dump)

/-- `strnlen` returns the index `r` of the first 0 in the bytes at `x0`, or
`x1` if there is none among the first `x1` bytes. It reads only those bytes,
so `bs` needs to be only as long as that, and it changes only `x0`, `x2`,
`x3` and the flags. -/
theorem strnlen_spec [Labels] (code : Code) (strnlen : Int64)
    (h : Loaded code strnlen strnlen_o)
    (h_sym : label "strnlen" = strnlen)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : s0.regs.X1.toNat ≤ bs.length ∨ 0 ∈ bs)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r,
      r ≤ s0.regs.X1.toNat ∧ (∀ i < r, bs[i]? ≠ some 0) ∧
      (r = s0.regs.X1.toNat ∨ bs[r]? = some 0) ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := .ofNat r
          X2 := s0.regs.X0
          X3 := x3 }
        status := st })
    ⟨s0, strnlen⟩ := by
  instr "mov x2, x0" at strnlen
  instr "mov x0, #0x0" at strnlen + 0x4
  refine loop_rule (measure fun n => s0.regs.X1.toNat + 1 - n).wf
    (fun n s => s.pc = strnlen + 0x8 ∧ n ≤ s0.regs.X1.toNat ∧
      (∀ i < n, bs[i]? ≠ some 0) ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := .ofNat n
          X2 := s0.regs.X0
          X3 := x3 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _, by simp, _, _,
      by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, hz, x3, st, rfl⟩
  have hX1 := s0.regs.X1.toNat_lt
  instr "cmp x0, x1" at strnlen + 0x8
  instr "b.ne 14 <strnlen+0x14>" at strnlen + 0xc
  · intro hne
    have hlt : n < s0.regs.X1.toNat := by
      refine Nat.lt_of_le_of_ne hn fun he => ?_
      rw [← UInt64.ofNat_eq_iff (by omega)] at he
      rw [he] at hne
      simp at hne
    have hb := lt_length_of_no_zero hz hlt h_bs
    instr "ldrb w3, [x2, x0]" at strnlen + 0x14
    load_byte h_mem h_len
    instr "cbz w3, 10 <strnlen+0x10>" at strnlen + 0x18
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "ret" at strnlen + 0x10
      exact .done _ (.inr ⟨rfl, n, hn, hz, .inr (by simp [hb, h_b]), _, _,
        by state_eq⟩)
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "add x0, x0, #0x1" at strnlen + 0x1c
      instr "b 8 <strnlen+0x8>" at strnlen + 0x20
      refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, ?_, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · simp [hb, h_b]
  · intro heq
    have he : n = s0.regs.X1.toNat := by
      rw [← UInt64.ofNat_eq_iff (by omega)]
      apply UInt64.toBitVec_inj.mp
      simp at heq
      bv_decide
    instr "ret" at strnlen + 0x10
    exact .done _ (.inr ⟨rfl, n, hn, hz, .inl he, _, _, by state_eq⟩)
