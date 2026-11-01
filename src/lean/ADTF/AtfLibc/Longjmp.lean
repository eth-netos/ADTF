module

import ADTF.AtfLibc.Listing.longjmp_o
import ADTF.AtfLibc.Setjmp
import Kraken.AArch64.Beacon
import Kraken.AArch64.BeaconMem
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `longjmp` from TF-A's `libc/setjmp.o`

`longjmp` restores the state that `setjmp` saved.

Trusted base of the theorems in this file: `aarch64-none-elf-objdump`
(pinned in `src/toolchain/arm-gnu-toolchain.version`), which printed the
listing in `Listing/`; the elaborator `objdumpAArch64`; Kraken's assembly
parser and its semantics of the instructions. Rerunning
`src/scripts/atf-listings.py` and checking that `git diff` is empty ties the
listing to the object file of the pinned `imx-atf` build (no CI does this
yet). Where the linker places the code is a hypothesis (`Loaded`).
-/

/-- Rewrites the loads of an instruction's effects with the lemmas `ls`,
which say what the buffer of `longjmp` holds, and simplifies the loaded
values to registers of the saved state. -/
macro "load_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := first | rfl | simp [jmpBuf_length])
    only [$ls,*, Effects.All, MemWidth.bytes, MemWidth.bits,
      BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceDiv,
      jmpBuf_slice, jmpBuf_take, List.getD_cons_succ, List.getD_cons_zero,
      BitVec.ofInt_ofBytes_toBytes64])

/-- The instructions of `longjmp` in ATF's `setjmp.o`. -/
def longjmp_o : List Instr := objdumpAArch64(longjmp_o_dump)

/-- `longjmp` restores the callee-saved registers, the link register and the
stack pointer from the buffer at `x0` that `setjmp` filled in the state
`saved`, and returns to the saved link register with `x0` set to `x1`, or 1
if `x1` is 0. -/
theorem longjmp_spec [Labels] (code : Code) (longjmp : Int64)
    (h : Loaded code longjmp longjmp_o)
    (s0 saved : MachineData) (R : DataMem → Prop)
    (h_mem : s0.dmem =⋆ Eq ((jmpBuf saved).At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = saved.regs.X30.toInt64 ∧
      s.data.regs.X19 = saved.regs.X19 ∧ s.data.regs.X20 = saved.regs.X20 ∧
      s.data.regs.X21 = saved.regs.X21 ∧ s.data.regs.X22 = saved.regs.X22 ∧
      s.data.regs.X23 = saved.regs.X23 ∧ s.data.regs.X24 = saved.regs.X24 ∧
      s.data.regs.X25 = saved.regs.X25 ∧ s.data.regs.X26 = saved.regs.X26 ∧
      s.data.regs.X27 = saved.regs.X27 ∧ s.data.regs.X28 = saved.regs.X28 ∧
      s.data.regs.X29 = saved.regs.X29 ∧ s.data.regs.X30 = saved.regs.X30 ∧
      s.data.regs.SP = saved.regs.SP ∧
      s.data.regs.X0 = (if s0.regs.X1 = 0 then 1 else s0.regs.X1) ∧
      s.data.dmem = s0.dmem)
    ⟨s0, longjmp⟩ := by
  have hw : (jmpBuf saved).length ≤ 2 ^ 64 := by simp [jmpBuf_length]
  have hl := MachineData.load_of_sep64 h_mem hw
  have hl0 := MachineData.load_of_sep64_zero h_mem hw
  instr "ldp x7, xzr, [x0, #96]" at longjmp
  load_simp [hl]
  instr "ldp x19, x20, [x0]" at longjmp + 0x4
  -- One pass rewrites only the load at offset 0, not the one at offset 8.
  load_simp [hl0]
  load_simp [hl]
  instr "ldp x21, x22, [x0, #16]" at longjmp + 0x8
  load_simp [hl]
  instr "ldp x23, x24, [x0, #32]" at longjmp + 0xc
  load_simp [hl]
  instr "ldp x25, x26, [x0, #48]" at longjmp + 0x10
  load_simp [hl]
  instr "ldp x27, x28, [x0, #64]" at longjmp + 0x14
  load_simp [hl]
  instr "ldp x29, x30, [x0, #80]" at longjmp + 0x18
  load_simp [hl]
  instr "mov sp, x7" at longjmp + 0x1c
  instr "ands x0, x1, x1" at longjmp + 0x20
  instr "cinc x0, x0, eq" at longjmp + 0x24
  instr "ret" at longjmp + 0x28
  refine Eventually.done _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_,
      rfl⟩
  apply UInt64.toBitVec_inj.mp
  split <;> simp_all [UInt64.toBitVec_inj] <;> bv_decide
