module

import ADTF.AtfLibc.Listing.strlen_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strlen` from TF-A's `libc/strlen.o`

Trusted base: as in `ADTF.AtfLibc.Setjmp`. Branch targets are absolute
addresses relative to the symbol `strlen`, whose address is a hypothesis
(`label "strlen" = strlen`), like the layout (`Loaded`).
-/

/-- The instructions of `strlen` in ATF's `strlen.o`. -/
def strlen_o : List Instr := objdumpAArch64(strlen_o_dump)

/-- `strlen` returns the length of the NUL-terminated string at `x0`. It
changes only `x0`, `x1` and `x2`. -/
theorem strlen_spec [Labels] (code : Code) (strlen : Int64)
    (h : Loaded code strlen strlen_o) (h_sym : label "strlen" = strlen)
    (s0 : MachineData) (str : List UInt8) (R : DataMem → Prop)
    (h_nz : 0 ∉ str) (h_len : str.length < 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq ((str ++ [0]).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      s.data.regs = { s0.regs with
        X0 := .ofNat str.length
        X1 := s0.regs.X0 + .ofNat str.length
        X2 := 0 } ∧
      s.data.status = s0.status ∧ s.data.dmem = s0.dmem)
    ⟨s0, strlen⟩ := by
  instr "mov x1, x0" at strlen
  -- The head is the `ldrb`; `n` bytes have been found nonzero.
  refine loop_rule (measure fun n => str.length + 1 - n).wf
    (fun n s => s.pc = strlen + 0x4 ∧ n ≤ str.length ∧ ∃ x2,
      s.data = { s0 with regs := { s0.regs with
        X1 := s0.regs.X0 + .ofNat n
        X2 := x2 } })
    _ 0 _
    ⟨rfl, Nat.zero_le _, s0.regs.X2, by dsimp only; congr 2; uint64_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, x2, rfl⟩
  have hw : (str ++ [0]).length ≤ 2 ^ 64 := by simp; omega
  instr "ldrb w2, [x1]" at strlen + 0x4
  load_byte h_mem hw
  instr "cbnz w2, 14 <strlen+0x14>" at strlen + 0x8
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have hlt : n < str.length := by
      refine Nat.lt_of_le_of_ne hn fun he => h_b ?_
      simp [he]
    instr "add x1, x1, #0x1" at strlen + 0x14
    instr "b 4 <strlen+0x4>" at strlen + 0x18
    refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt,
      ⟨BitVec.zeroExtend 64 (BitVec.zeroExtend 32
        ((str ++ [0])[n]'(by simp; omega)).toBitVec)⟩,
      by dsimp only; congr 2; uint64_eq⟩)
    simp only [InvImage, WellFoundedRelation.rel]; omega
  · intro h_b
    rw [ldrb_eq_zero_iff] at h_b
    have he : n = str.length := by
      refine Nat.le_antisymm hn (Nat.not_lt.mp fun hlt => h_nz ?_)
      rw [List.getElem_append_left hlt] at h_b
      exact h_b ▸ List.getElem_mem hlt
    subst he
    instr "sub x0, x1, x0" at strlen + 0xc
    instr "ret" at strlen + 0x10
    refine .done _ (.inr ⟨rfl, ?_, rfl, rfl⟩)
    dsimp only
    congr 1
    · uint64_eq
    · rw [h_b]; rfl
