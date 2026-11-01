module

public import Kraken.AArch64.Beacon
public import Kraken.AArch64.BeaconMem
public import Kraken.AArch64.BeaconLoop

/-!
# Lemmas and tactics shared by the proofs of TF-A's C library functions
-/

@[expose] public section

/-- The condition of `cbz`/`cbnz` on a 32-bit register into which `ldrb`
loaded the byte `b`. -/
theorem ldrb_eq_zero_iff (b : UInt8) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64
      (BitVec.zeroExtend 32 b.toBitVec)) = 0 ↔ b = 0 := by
  rw [← UInt8.toBitVec_inj]
  generalize b.toBitVec = v
  simp only [UInt8.toBitVec_zero]
  bv_decide

/-- Rewrites the byte loads of an instruction's effects with
`MachineData.load_byte_of_sep64 h_mem hw`, for the separation-logic
hypothesis `h_mem` and the length bound `hw` of the bytes. The index has to
be below the length, which the discharger proves with `omega`. -/
macro "load_byte" h_mem:term:max hw:term:max : tactic => `(tactic|
  simp (disch := first | rfl | (simp; omega)) only [UInt64.toBitVec_add,
    UInt64.toBitVec_ofNat', MachineData.load_byte_of_sep64 $h_mem $hw,
    MachineData.load_byte_of_sep64_zero $h_mem $hw, Effects.All])

/-- Proves an equality of two `UInt64`s by `bv_decide` on their bit vectors,
with `UInt64.ofNat` of a sum split up. -/
macro "uint64_eq" : tactic => `(tactic| (
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_add, UInt64.ofNat_add, UInt64.toBitVec_ofNat',
    UInt64.toBitVec_ofNat]
  bv_decide))
