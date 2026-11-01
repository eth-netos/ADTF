module

import ADTF.AtfLibc.Listing.strchr_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strchr` from TF-A's `libc/strchr.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strchr` in ATF's `strchr.o`. -/
def strchr_o : List Instr := objdumpAArch64(strchr_o_dump)

/-- `strchr` searches the bytes at `x0` for the low byte `c` of `x1`, up to
the first 0. It returns the address of `c` at index `r`, or the null pointer
if a 0 comes first. A 0 terminator is found if `c` is 0. It changes only
`x0`, `x1` (to `c`), `x2` and the flags. -/
theorem strchr_spec [Labels] (code : Code) (strchr : Int64)
    (h : Loaded code strchr strchr_o)
    (h_sym : label "strchr" = strchr)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : 0 ∈ bs ∨ s0.regs.X1.toUInt8 ∈ bs)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r x0,
      (∀ i < r, bs[i]? ≠ some s0.regs.X1.toUInt8 ∧ bs[i]? ≠ some 0) ∧
      (bs[r]? = some s0.regs.X1.toUInt8 ∧ x0 = s0.regs.X0 + .ofNat r ∨
        bs[r]? = some 0 ∧ s0.regs.X1.toUInt8 ≠ 0 ∧ x0 = 0) ∧
      ∃ x2 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := x2 }
        status := st })
    ⟨s0, strchr⟩ := by
  instr "and w1, w1, #0xff" at strchr
  refine loop_rule (measure fun n => bs.length - n).wf
    (fun n s => s.pc = strchr + 0x4 ∧
      (∀ i < n, bs[i]? ≠ some s0.regs.X1.toUInt8 ∧ bs[i]? ≠ some 0) ∧
      ∃ x2 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := s0.regs.X0 + .ofNat n
          X1 := s0.regs.X1 &&& 0xff
          X2 := x2 }
        status := st })
    _ 0 _ ⟨rfl, by simp, _, _, by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hz, x2, st, rfl⟩
  have hb : n < bs.length := by
    rcases h_bs with h_bs | h_bs
    · exact lt_length_of_forall_ne (fun i hi => (hz i hi).2) h_bs
    · exact lt_length_of_forall_ne (fun i hi => (hz i hi).1) h_bs
  instr "ldrb w2, [x0]" at strchr + 0x4
  load_byte h_mem h_len
  instr "cmp w2, w1" at strchr + 0x8
  instr "b.eq 20 <strchr+0x20>" at strchr + 0xc
  · intro heq
    rw [ldrb_cmp_and_eq_iff] at heq
    instr "ret" at strchr + 0x20
    exact .done _ (.inr ⟨rfl, n, _, hz, .inl ⟨by simp [hb, heq], rfl⟩,
      _, _, by state_eq⟩)
  · intro hne
    rw [ldrb_cmp_and_eq_iff] at hne
    instr "cbz w2, 1c <strchr+0x1c>" at strchr + 0x10
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "mov x0, #0x0" at strchr + 0x1c
      instr "ret" at strchr + 0x20
      exact .done _ (.inr ⟨rfl, n, _, hz,
        .inr ⟨by simp [hb, h_b], fun hc => hne (h_b.trans hc.symm), rfl⟩,
        _, _, by state_eq⟩)
    · intro h_b
      rw [ldrb_eq_zero_iff] at h_b
      instr "add x0, x0, #0x1" at strchr + 0x14
      instr "b 4 <strchr+0x4>" at strchr + 0x18
      refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], ?_, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · simp [hb, h_b, hne]
