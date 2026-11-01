module

import ADTF.AtfLibc.Listing.strrchr_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strrchr` from TF-A's `libc/strrchr.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strrchr` in ATF's `strrchr.o`. -/
def strrchr_o : List Instr := objdumpAArch64(strrchr_o_dump)

/-- `strrchr` returns the address of the last occurrence of the low byte of
`x1` in the bytes at `x0` up to and including the first 0, at index `r`, or
the null pointer if there is none. It changes only `x0`, `x1` (to its low
byte), `x2`, `x3` and the flags. -/
theorem strrchr_spec [Labels] (code : Code) (strrchr : Int64)
    (h : Loaded code strrchr strrchr_o)
    (h_sym : label "strrchr" = strrchr)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : 0 ∈ bs)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r x0,
      (∀ i < r, bs[i]? ≠ some 0) ∧ bs[r]? = some 0 ∧
      IsLastMatch bs s0.regs.X1.toUInt8 s0.regs.X0 (r + 1) x0 ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 + .ofNat r
          X3 := x3 }
        status := st })
    ⟨s0, strrchr⟩ := by
  instr "and w1, w1, #0xff" at strrchr
  instr "mov x2, x0" at strrchr + 0x4
  instr "mov x0, #0x0" at strrchr + 0x8
  refine loop_rule (measure fun n => bs.length - n).wf
    (fun n s => s.pc = strrchr + 0xc ∧ (∀ i < n, bs[i]? ≠ some 0) ∧
      ∃ x0 x3 st,
      IsLastMatch bs s0.regs.X1.toUInt8 s0.regs.X0 n x0 ∧
      s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 + .ofNat n
          X3 := x3 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, by simp, _, _, _, .zero _ _ _,
      by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hz, x0, x3, st, hm, rfl⟩
  have hb : n < bs.length := lt_length_of_forall_ne hz h_bs
  instr "ldrb w3, [x2]" at strrchr + 0xc
  load_byte h_mem h_len
  instr "cmp w3, w1" at strrchr + 0x10
  instr "csel x0, x0, x2, ne" at strrchr + 0x14
  rw [csel_ne_ldrb_cmp_and]
  have hm' : IsLastMatch bs s0.regs.X1.toUInt8 s0.regs.X0 (n + 1)
      (if bs[n] = s0.regs.X1.toUInt8 then s0.regs.X0 + .ofNat n else x0) := by
    split
    · exact .succ_eq hb ‹_›
    · exact hm.succ_ne hb ‹_›
  generalize (if bs[n] = s0.regs.X1.toUInt8 then _ else x0) = x0' at hm' ⊢
  instr "cbz w3, 24 <strrchr+0x24>" at strrchr + 0x18
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    instr "ret" at strrchr + 0x24
    exact .done _ (.inr ⟨rfl, n, x0', hz, by simp [hb, h_b], hm', _, _,
      by state_eq⟩)
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    instr "add x2, x2, #0x1" at strrchr + 0x1c
    instr "b c <strrchr+0xc>" at strrchr + 0x20
    refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], ?_, x0', _, _, hm',
      by state_eq⟩)
    · simp only [InvImage, WellFoundedRelation.rel]; omega
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hz i hi
      · simp [hb, h_b]
