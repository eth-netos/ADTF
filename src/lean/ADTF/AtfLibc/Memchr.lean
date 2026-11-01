module

import ADTF.AtfLibc.Listing.memchr_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `memchr` from TF-A's `libc/memchr.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `memchr` in ATF's `memchr.o`. -/
def memchr_o : List Instr := objdumpAArch64(memchr_o_dump)

/-- `memchr` searches the `x2` bytes at `x0` for the low byte of `x1`. It
returns the address of the first occurrence, at index `r`, or the null pointer
if there is none (then `r` is `x2`). It changes only `x0`, `x1` (to its low
byte), `x2`, `x3` and the flags. -/
theorem memchr_spec [Labels] (code : Code) (memchr : Int64)
    (h : Loaded code memchr memchr_o)
    (h_sym : label "memchr" = memchr)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : s0.regs.X2.toNat ≤ bs.length)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r x0,
      (∀ i < r, bs[i]? ≠ some s0.regs.X1.toUInt8) ∧
      (r = s0.regs.X2.toNat ∧ x0 = 0 ∨
        r < s0.regs.X2.toNat ∧ bs[r]? = some s0.regs.X1.toUInt8 ∧
        x0 = s0.regs.X0 + .ofNat r) ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := x0
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 + s0.regs.X2
          X3 := x3 }
        status := st })
    ⟨s0, memchr⟩ := by
  instr "add x2, x0, x2" at memchr
  instr "and w1, w1, #0xff" at memchr + 0x4
  refine loop_rule (measure fun n => s0.regs.X2.toNat + 1 - n).wf
    (fun n s => s.pc = memchr + 0x8 ∧ n ≤ s0.regs.X2.toNat ∧
      (∀ i < n, bs[i]? ≠ some s0.regs.X1.toUInt8) ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := s0.regs.X0 + .ofNat n
          X1 := s0.regs.X1 &&& 0xff
          X2 := s0.regs.X0 + s0.regs.X2
          X3 := x3 }
        status := st })
    _ 0 _ ⟨by dsimp only; bv_decide, Nat.zero_le _, by simp, _, _,
      by state_eq⟩ ?_
  rintro n ⟨d, pc⟩ ⟨rfl, hn, hz, x3, st, rfl⟩
  have hX2 := s0.regs.X2.toNat_lt
  instr "cmp x0, x2" at memchr + 0x8
  instr "b.ne 18 <memchr+0x18>" at memchr + 0xc
  · intro hne
    have hlt : n < s0.regs.X2.toNat := by
      refine Nat.lt_of_le_of_ne hn fun he => ?_
      rw [← UInt64.ofNat_eq_iff (by omega)] at he
      rw [he] at hne
      simp at hne
    instr "ldrb w3, [x0]" at memchr + 0x18
    load_byte h_mem h_len
    instr "cmp w3, w1" at memchr + 0x1c
    instr "b.eq 14 <memchr+0x14>" at memchr + 0x20
    · intro heq
      rw [ldrb_cmp_and_eq_iff] at heq
      instr "ret" at memchr + 0x14
      exact .done _ (.inr ⟨rfl, n, _, hz,
        .inr ⟨hlt, by simp [show n < bs.length by omega, heq], rfl⟩, _, _,
        by state_eq⟩)
    · intro heq
      rw [ldrb_cmp_and_eq_iff] at heq
      instr "add x0, x0, #0x1" at memchr + 0x24
      instr "b 8 <memchr+0x8>" at memchr + 0x28
      refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, ?_, _, _,
        by state_eq⟩)
      · simp only [InvImage, WellFoundedRelation.rel]; omega
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hz i hi
        · simp [show i < bs.length by omega, heq]
  · intro heq
    have he : n = s0.regs.X2.toNat := by
      rw [← UInt64.ofNat_eq_iff (by omega)]
      apply UInt64.toBitVec_inj.mp
      simp at heq
      bv_decide
    instr "mov x0, #0x0" at memchr + 0x10
    instr "ret" at memchr + 0x14
    exact .done _ (.inr ⟨rfl, n, _, hz, .inl ⟨he, rfl⟩, _, _,
      by state_eq⟩)
