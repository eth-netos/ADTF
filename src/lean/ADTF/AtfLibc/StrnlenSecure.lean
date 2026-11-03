module

import ADTF.AtfLibc.Listing.strnlen_secure_o
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strnlen_secure` from TF-A's `libc/strnlen_secure.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`.
-/

/-- The instructions of `strnlen_secure` in ATF's `strnlen_secure.o`. -/
def strnlen_secure_o : List Instr := objdumpAArch64(strnlen_secure_o_dump)

/-- `strnlen_secure` returns 0 if `x0` is the null pointer, and otherwise
the same as `strnlen`: the index `r` of the first 0 in the bytes at `x0`, or
`x1` if there is none among the first `x1` bytes. It changes only `x0`, `x2`,
`x3` and the flags. -/
theorem strnlen_secure_spec [Labels] (code : Code) (strnlen_secure : Int64)
    (h : Loaded code strnlen_secure strnlen_secure_o)
    (h_sym : label "strnlen_secure" = strnlen_secure)
    (s0 : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_bs : s0.regs.X1.toNat ≤ bs.length ∨ 0 ∈ bs)
    (h_len : bs.length ≤ 2 ^ 64)
    (h_mem : s0.dmem =⋆ Eq (bs.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧ ∃ r,
      (s0.regs.X0 = 0 → r = 0) ∧
      (s0.regs.X0 ≠ 0 → r ≤ s0.regs.X1.toNat ∧
        (∀ i < r, bs[i]? ≠ some 0) ∧
        (r = s0.regs.X1.toNat ∨ bs[r]? = some 0)) ∧
      ∃ x3 st, s.data = { s0 with
        regs := { s0.regs with
          X0 := .ofNat r
          X2 := s0.regs.X0
          X3 := x3 }
        status := st })
    ⟨s0, strnlen_secure⟩ := by
  instr "mov x2, x0" at strnlen_secure
  instr "mov x0, #0x0" at strnlen_secure + 0x4
  instr "cbz x2, 1c <strnlen_secure+0x1c>" at strnlen_secure + 0x8
  · intro h0
    instr "ret" at strnlen_secure + 0x1c
    exact .done _ ⟨rfl, 0, fun _ => rfl,
      fun h1 => (h1 (UInt64.toBitVec_inj.mp (by simpa using h0))).elim, _, _,
      by state_eq⟩
  · intro h0
    have hx : s0.regs.X0 ≠ 0 := fun he => h0 (by simp [he])
    refine loop_rule (measure fun n => s0.regs.X1.toNat + 1 - n).wf
      (fun n s => s.pc = strnlen_secure + 0xc ∧ n ≤ s0.regs.X1.toNat ∧
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
    instr "cmp x0, x1" at strnlen_secure + 0xc
    instr "b.eq 1c <strnlen_secure+0x1c>" at strnlen_secure + 0x10
    · intro heq
      have he : n = s0.regs.X1.toNat := by
        rw [← UInt64.ofNat_eq_iff (by omega)]
        apply UInt64.toBitVec_inj.mp
        simp at heq
        bv_decide
      instr "ret" at strnlen_secure + 0x1c
      exact .done _ (.inr ⟨rfl, n, fun h => absurd h hx,
        fun _ => ⟨hn, hz, .inl he⟩, _, _, by state_eq⟩)
    · intro hne
      have hlt : n < s0.regs.X1.toNat := by
        refine Nat.lt_of_le_of_ne hn fun he => ?_
        rw [← UInt64.ofNat_eq_iff (by omega)] at he
        rw [he] at hne
        simp at hne
      have hb := lt_length_of_no_zero hz hlt h_bs
      instr "ldrb w3, [x2, x0]" at strnlen_secure + 0x14
      load_byte h_mem h_len
      instr "cbnz w3, 20 <strnlen_secure+0x20>" at strnlen_secure + 0x18
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        instr "add x0, x0, #0x1" at strnlen_secure + 0x20
        instr "b c <strnlen_secure+0xc>" at strnlen_secure + 0x24
        refine .done _ (.inl ⟨n + 1, ?_, by rw [h_sym], hlt, ?_, _, _,
          by state_eq⟩)
        · simp only [InvImage, WellFoundedRelation.rel]; omega
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hz i hi
          · simp [hb, h_b]
      · intro h_b
        rw [ldrb_eq_zero_iff] at h_b
        instr "ret" at strnlen_secure + 0x1c
        exact .done _ (.inr ⟨rfl, n, fun h => absurd h hx,
          fun _ => ⟨hn, hz, .inr (by simp [hb, h_b])⟩, _, _, by state_eq⟩)
