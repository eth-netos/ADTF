module

import ADTF.AtfLibc.Listing.setjmp_o
import Kraken.AArch64.Beacon
import Kraken.AArch64.BeaconMem
import Kraken.AArch64.Objdump

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-- The instructions of `setjmp` in ATF's `setjmp.o`. -/
def setjmp_o : List Instr := objdumpAArch64(setjmp_o_dump)

/-- The buffer contents that `setjmp` writes for the state `s`. -/
def jmpBuf (s : MachineData) : List UInt8 :=
  ([s.regs.X19, s.regs.X20, s.regs.X21, s.regs.X22, s.regs.X23, s.regs.X24,
    s.regs.X25, s.regs.X26, s.regs.X27, s.regs.X28, s.regs.X29, s.regs.X30,
    s.regs.SP, 0].map UInt64.toBytes).flatten

/-- Memory discharger: proves that a store's address is in the data memory,
from a hypothesis `m =⋆ Eq (bs.At a) ⋆ R` about the memory `m` before earlier
stores. -/
macro "mem_disch" : tactic => `(tactic| (
  repeat apply Mem.loadInt_isSome_storeInt
  first
  | (apply Mem.loadInt_isSome_of_sep_zero
     assumption
     simp only [*]; decide)
  | (apply Mem.loadInt_isSome_of_sep64
     assumption
     simp only [*]; decide)))

/-- Rewrites the stores of an instruction's effects into `Mem.storeInt`s,
discharging the check that the address is in the data memory with
`mem_disch`. -/
macro "store_simp" : tactic => `(tactic|
  simp (disch := mem_disch) only [MachineData.store_of_isSome, Effects.All])

/-- Append discharger: proves the side conditions of `Mem.storeBytes_append`
for stores to constant offsets. -/
macro "append_disch" : tactic => `(tactic| (
  simp only [List.length_append, Int.toBytes_length]
  all_goals first | bv_decide | simp))

/-- `setjmp` saves the callee-saved registers, the link register and the stack
pointer into the 112-byte buffer at `x0`, and returns 0. -/
theorem setjmp_spec [Labels] (code : Code) (setjmp : Int64)
    (h : Loaded code setjmp setjmp_o)
    (s0 : MachineData) (old : List UInt8) (R : DataMem → Prop)
    (h_old : old.length = 112)
    (h_mem : s0.dmem =⋆ Eq (old.At s0.regs.X0.toBitVec) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      s.data.regs = { s0.regs with X0 := 0, X7 := s0.regs.SP } ∧
      s.data.status = s0.status ∧
      s.data.dmem =⋆ Eq ((jmpBuf s0).At s0.regs.X0.toBitVec) ⋆ R)
    ⟨s0, setjmp⟩ := by
  instr "mov x7, sp" at setjmp
  instr "stp x19, x20, [x0]" at setjmp + 0x4
  store_simp
  instr "stp x21, x22, [x0, #16]" at setjmp + 0x8
  store_simp
  instr "stp x23, x24, [x0, #32]" at setjmp + 0xc
  store_simp
  instr "stp x25, x26, [x0, #48]" at setjmp + 0x10
  store_simp
  instr "stp x27, x28, [x0, #64]" at setjmp + 0x14
  store_simp
  instr "stp x29, x30, [x0, #80]" at setjmp + 0x18
  store_simp
  instr "stp x7, xzr, [x0, #96]" at setjmp + 0x1c
  store_simp
  instr "mov x0, #0x0" at setjmp + 0x20
  instr "ret" at setjmp + 0x24
  refine Eventually.done _ ⟨rfl, rfl, rfl, ?_⟩
  simp (disch := append_disch) only
    [Mem.storeInt_eq_storeBytes, Mem.storeBytes_append]
  have h_sep := Mem.storeBytes_sep _ 112 old (jmpBuf s0) R _ ⟨h_mem, h_old,
    by simp only [jmpBuf, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.length_append, UInt64.toBytes_length,
      List.length_nil]⟩
  simp only [jmpBuf, UInt64.toBytes, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    at h_sep ⊢
  exact h_sep
