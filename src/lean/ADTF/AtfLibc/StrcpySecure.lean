module

public import ADTF.AtfLibc.Listing.strcpy_secure_o
public import ADTF.AtfLibc.StrnlenSecure
import ADTF.AtfLibc.Common
import Kraken.AArch64.Objdump
public import Kraken.AArch64.BeaconCall

open Kraken.AArch64.Parser Kraken.AArch64.Beacon

/-!
# `strcpy_secure` from TF-A's `libc/strcpy_secure.o`

Trusted base: as in `ADTF.AtfLibc.Strlen`, plus the relocation of the call
to `strnlen_secure` (see `Kraken.AArch64.Objdump`).
-/

/-- The instructions of `strcpy_secure` in ATF's `strcpy_secure.o`. -/
public def strcpy_secure_o : List Instr := objdumpAArch64(strcpy_secure_o_dump)

/-- `-EINVAL` as the `int` that `strcpy_secure` returns in `w0`. -/
public abbrev EINVAL_neg : UInt64 := 0xffffffea

/-- `-ERANGE` as the `int` that `strcpy_secure` returns in `w0`. -/
public abbrev ERANGE_neg : UInt64 := 0xffffffde

/-- The return value `ret` and the new destination bytes `ds'` of
`strcpy_secure(dst, size, src)`, for the destination bytes `ds` and the
source bytes `bs`. -/
@[expose] public def StrcpySecureResult (dst size src : UInt64) (ds bs : List UInt8)
    (ret : UInt64) (ds' : List UInt8) : Prop :=
  if dst = 0 ∨ src = 0 then ret = EINVAL_neg ∧ ds' = ds
  else if size = 0 then ret = ERANGE_neg ∧ ds' = ds
  else ∃ r, r ≤ size.toNat ∧ (∀ i < r, bs[i]? ≠ some 0) ∧
    (r = size.toNat ∨ bs[r]? = some 0) ∧
    if r = size.toNat then ret = ERANGE_neg ∧ ds' = ds.set 0 0
    else ret = 0 ∧ ds' = bs.take r ++ 0 :: ds.drop (r + 1)

/-- `strcpy_secure` copies the NUL-terminated string at `src` to the
`size` bytes at `dst`, under the generic calling convention, with
`StrcpySecureResult`. It uses 48 bytes of stack. -/
@[expose] public def strcpy_secure_spec [Labels] (code : Code) (strcpy_secure : Int64) :
    Prop :=
  ∀ (dst size src : UInt64) (ds bs : List UInt8) (R : DataMem → Prop),
    CallSpec code strcpy_secure
      (fun regs m => regs.X0 = dst ∧ regs.X1 = size ∧ regs.X2 = src ∧
        ds.length = size.toNat ∧ (size.toNat ≤ bs.length ∨ 0 ∈ bs) ∧
        bs.length ≤ 2 ^ 64 ∧
        m =⋆ Eq (ds.At dst.toBitVec) ⋆ Eq (bs.At src.toBitVec) ⋆
          stack_available regs.SP 48 ⋆ R)
      (fun regs m => ∃ ds',
        StrcpySecureResult dst size src ds bs regs.X0 ds' ∧
        m =⋆ Eq (ds'.At dst.toBitVec) ⋆ Eq (bs.At src.toBitVec) ⋆
          stack_available regs.SP 48 ⋆ R)

/-- The condition `ne` after `cmp x, #0x0`. -/
theorem cmp_zero_ne {x : UInt64}
    (h : (!x.toBitVec - 0 == BitVec.zero 64) = true) : x ≠ 0 := by
  rintro rfl
  exact absurd h (by decide)

theorem cmp_zero_eq {x : UInt64}
    (h : ¬(!x.toBitVec - 0 == BitVec.zero 64) = true) : x = 0 := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_zero]
  revert h
  generalize x.toBitVec = v
  rw [BitVec.zero_eq]
  bv_decide

/-- The flag `z` of `ccmp x, #0x0, ...` when it compares. -/
theorem ccmp_zero_eq {x : UInt64} (h : x.toBitVec - 0#64 = BitVec.zero 64) :
    x = 0 := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_zero]
  revert h
  generalize x.toBitVec = v
  rw [BitVec.zero_eq]
  bv_decide

theorem ccmp_zero_ne {x : UInt64}
    (h : ¬x.toBitVec - 0#64 = BitVec.zero 64) : x ≠ 0 := by
  rintro rfl
  exact h (by decide)

/-- The epilogue of `strcpy_secure` from `strcpy_secure + 0x44`: it restores
`x19`–`x21`, `x29` and `x30` from the stack frame at `sp`, frees the frame and
returns, with `x0` unchanged. -/
theorem strcpy_secure_epilogue [Labels] (code : Code) (strcpy_secure : Int64)
    (h : Loaded code strcpy_secure strcpy_secure_o) (s0 : MachineData)
    (hsp : s0.regs.SP % 16 = 0) (w5 : UInt64) (A R : DataMem → Prop)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem) (pc : Int64)
    (hpc : pc = strcpy_secure + 0x44)
    (h18 : regs.X18 = s0.regs.X18) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 48#64⟩)
    (hm : m =⋆ Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, s0.regs.X20,
      s0.regs.X21, w5].wordBytes.At (s0.regs.SP.toBitVec - 48#64)) ⋆
      (A ⋆ R)) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = regs.X0 ∧
      (A ⋆ stack_available s.data.regs.SP 48 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, pc⟩ := by
  subst hpc
  have hal := sp_aligned (sp_sub_aligned hsp 48#64 rfl)
  dsimp only at hal
  instr "ldr x21, [sp, #32]" at strcpy_secure + 0x44
  simp only [hSP, hal, Bool.false_eq_true, ↓reduceIte]
  load_frame hm 4
  instr_simp
  instr "ldp x19, x20, [sp, #16]" at strcpy_secure + 0x48
  simp only [hSP, hal, Bool.false_eq_true, ↓reduceIte]
  load_frame hm 2
  load_frame hm 3
  instr_simp
  instr "ldp x29, x30, [sp], #48" at strcpy_secure + 0x4c
  simp only [hal, Bool.false_eq_true, ↓reduceIte]
  load_frame hm 0
  load_frame hm 1
  instr_simp
  simp only [List.getElem_cons_zero, List.getElem_cons_succ,
    sub_add_ofNat, UInt64.ofBitVec_toBitVec]
  instr "ret" at strcpy_secure + 0x50
  refine .done _ ⟨rfl, ⟨h18, rfl, rfl, rfl, h22, h23, h24, h25, h26, h27,
    h28, rfl, rfl⟩, rfl, ?_⟩
  dsimp only
  rw [Std.ExtHashMap.sep_comm] at hm
  have hm' : m =⋆ (A ⋆ R) ⋆ stack_available s0.regs.SP 48 :=
    sep_mono_r (fun _ hF => anybytes_of_wordBytes hF) hm
  rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm R,
    ← Std.ExtHashMap.sep_assoc] at hm'
  exact hm'

/-- After copying the bytes of `b` from `n + 1` on over `a`, copying byte
`n` too. -/
theorem List.set_take_succ_append_drop {a b : List UInt8} {n : Nat}
    {x : UInt8} (ha : n < a.length) (hb : n < b.length) (hx : b[n] = x) :
    (a.take (n + 1) ++ b.drop (n + 1)).set n x = a.take n ++ b.drop n := by
  rw [← hx, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
    List.append_assoc, List.set_append_right _ _ (by simp; omega),
    List.length_take, Nat.min_eq_left (by omega), Nat.sub_self,
    List.singleton_append, List.set_cons_zero, List.drop_eq_getElem_cons hb]


/-- The bytes of the destination after `strcpy_secure` has copied a string
of length `r` from `bs` to `ds`. -/
abbrev strcpy_dest (ds bs : List UInt8) (r : Nat) : List UInt8 :=
  bs.take r ++ 0 :: ds.drop (r + 1)

theorem strcpy_dest_length {ds bs : List UInt8} {r : Nat}
    (hr : r < ds.length) (hrb : r ≤ bs.length) :
    (strcpy_dest ds bs r).length = ds.length := by
  simp only [List.length_append, List.length_take, List.length_cons,
    List.length_drop]
  omega

theorem strcpy_dest_getElem {ds bs : List UInt8} {r j : Nat} (hj : j < r)
    (hrb : r ≤ bs.length) (h : j < (strcpy_dest ds bs r).length) :
    (strcpy_dest ds bs r)[j] = bs[j]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_take]

/-- Storing the terminating NUL of the copy. -/
theorem List.set_eq_take_strcpy_dest {ds bs : List UInt8} {r : Nat}
    (hr : r < ds.length) (hrb : r ≤ bs.length) :
    ds.set r 0 = ds.take r ++ (strcpy_dest ds bs r).drop r := by
  rw [List.set_eq_take_append_cons_drop,
    ite_eq_left_of_eq_true _ _ (eq_true hr), strcpy_dest,
    List.drop_left' (by simp only [List.length_take]; omega)]

/-- The string that `strnlen_secure` measured fits in its bytes. -/
theorem strnlen_le_length {bs : List UInt8} {n r : Nat}
    (h_bs : n ≤ bs.length ∨ 0 ∈ bs) (hrn : r ≤ n)
    (hz : ∀ i < r, bs[i]? ≠ some 0) : r ≤ bs.length := by
  rcases h_bs with h | h
  · omega
  · exact Nat.le_of_lt (lt_length_of_forall_ne hz h)

/-- The copy loop of `strcpy_secure` from `strcpy_secure + 0x58`, which
copies the string backwards: the bytes from `k` on are already copied, with
the terminating NUL at `r`. -/
theorem strcpy_secure_copy [Labels] (code : Code) (strcpy_secure : Int64)
    (h : Loaded code strcpy_secure strcpy_secure_o)
    (h_sym : label "strcpy_secure" = strcpy_secure) (s0 : MachineData)
    (hsp : s0.regs.SP % 16 = 0) (w5 : UInt64) (ds bs : List UInt8) (r : Nat)
    (R : DataMem → Prop) (hr : r < ds.length) (hrb : r ≤ bs.length)
    (hbl : bs.length ≤ 2 ^ 64) (hdl : ds.length ≤ 2 ^ 64)
    (regs : Reg64s) (st : StatusFlags) (m : DataMem) (k : Nat) (hk : k ≤ r)
    (hX0 : regs.X0 = .ofNat k)
    (h18 : regs.X18 = s0.regs.X18) (h22 : regs.X22 = s0.regs.X22)
    (h23 : regs.X23 = s0.regs.X23) (h24 : regs.X24 = s0.regs.X24)
    (h25 : regs.X25 = s0.regs.X25) (h26 : regs.X26 = s0.regs.X26)
    (h27 : regs.X27 = s0.regs.X27) (h28 : regs.X28 = s0.regs.X28)
    (hSP : regs.SP = ⟨s0.regs.SP.toBitVec - 48#64⟩)
    (h19 : regs.X19 = s0.regs.X0) (h20 : regs.X20 = s0.regs.X2)
    (hm : m =⋆ Eq ((ds.take k ++ (strcpy_dest ds bs r).drop k).At
      s0.regs.X0.toBitVec) ⋆ Eq (bs.At s0.regs.X2.toBitVec) ⋆
      Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, s0.regs.X20,
        s0.regs.X21, w5].wordBytes.At (s0.regs.SP.toBitVec - 48#64)) ⋆ R) :
    Eventually code.stepWp (fun s =>
      s.pc = s0.regs.X30.toInt64 ∧
      CalleeSavedRegsPreserved s0.regs s.data.regs ∧
      s.data.regs.X0 = 0 ∧
      ((Eq ((strcpy_dest ds bs r).At s0.regs.X0.toBitVec) ⋆
        Eq (bs.At s0.regs.X2.toBitVec)) ⋆
        stack_available s.data.regs.SP 48 ⋆ R) s.data.dmem)
    ⟨⟨regs, st, m⟩, strcpy_secure + 0x58⟩ := by
  rw [← h19, ← h20] at hm
  refine loop_rule_at (measure id).wf
    (fun k d => k ≤ r ∧ ∃ x1 st m,
      d = ⟨{ regs with X0 := .ofNat k, X1 := x1 }, st, m⟩ ∧
      m =⋆ Eq ((ds.take k ++ (strcpy_dest ds bs r).drop k).At
        regs.X19.toBitVec) ⋆ Eq (bs.At regs.X20.toBitVec) ⋆
        Eq ([s0.regs.X29, s0.regs.X30, s0.regs.X19, s0.regs.X20,
          s0.regs.X21, w5].wordBytes.At (s0.regs.SP.toBitVec - 48#64)) ⋆ R)
    _ (strcpy_secure + 0x58) (strcpy_secure + 0x44) k _
    ⟨hk, regs.X1, st, m, by rw [← hX0], hm⟩ ?_
  rintro k d ⟨hk, x1, st, m, rfl, hm⟩
  instr "cbz x0, 44 <strcpy_secure+0x44>" at strcpy_secure + 0x58
  have hk64 : k < 2 ^ 64 := by omega
  · intro hz
    obtain rfl : k = 0 := ofNat_toBitVec_eq_zero hk64 hz
    refine .done _ (.inr ⟨by rw [h_sym], ?_⟩)
    simp only [List.take_zero, List.drop_zero, List.nil_append, h19, h20] at hm
    rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm
    refine eventually_weaken _ _ _ _ ?_ (strcpy_secure_epilogue code
      strcpy_secure h s0 hsp w5 _ R _ _ _ _ (by rw [h_sym]) h18 h22 h23 h24 h25 h26 h27
      h28 hSP hm)
    rintro s ⟨hpc, hpres, hx0, hms⟩
    exact ⟨hpc, hpres, hx0, hms⟩
  · intro hz
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 :=
      Nat.exists_eq_succ_of_ne_zero fun h0 => hz (by rw [h0]; rfl)
    instr "sub x0, x0, #0x1" at strcpy_secure + 0x5c
    simp only [ofNat_succ_sub_one]
    rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc] at hm
    have hm2 := hm
    rw [Std.ExtHashMap.sep_comm_l] at hm2
    have hT := strcpy_dest_length hr hrb
    have hl : (ds.take (j + 1) ++ (strcpy_dest ds bs r).drop (j + 1)).length =
        ds.length := by
      rw [List.length_append, List.length_take, List.length_drop, hT]
      omega
    instr "ldrb w1, [x20, x0]" at strcpy_secure + 0x60
    load_byte hm2 hbl
    instr "strb w1, [x19, x0]" at strcpy_secure + 0x64
    store_byte hm
    have hm' := Mem.storeInt_byte_sep _ _ j _ m hm (by omega) (by omega)
      bs[j]
    rw [List.set_take_succ_append_drop (by omega) (by omega)
        (strcpy_dest_getElem (by omega) hrb (by omega)),
      ← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc] at hm'
    instr "b 58 <strcpy_secure+0x58>" at strcpy_secure + 0x68
    refine .done _ (.inl ⟨by rw [h_sym], j, ?_, by omega, _, _, _, rfl, hm'⟩)
    simp only [InvImage, WellFoundedRelation.rel, id]
    omega

public theorem strcpy_secure_ok [Labels] (code : Code) (strcpy_secure : Int64)
    (h : Loaded code strcpy_secure strcpy_secure_o)
    (h_sym : label "strcpy_secure" = strcpy_secure)
    (h_strnlen_secure : strnlen_secure_spec code (label "strnlen_secure")) :
    strcpy_secure_spec code strcpy_secure := by
  rintro dst size src ds bs R s0 hsp
    ⟨rfl, rfl, rfl, h_ds, h_bs, h_len, hm⟩
  instr "cmp x0, #0x0" at strcpy_secure
  instr "ccmp x2, #0x0, #0x4, ne" at strcpy_secure + 0x4
  split
  · rename_i hx0
    replace hx0 := cmp_zero_ne hx0
    instr "b.eq 6c <strcpy_secure+0x6c>" at strcpy_secure + 0x8
    · intro hx2
      replace hx2 := ccmp_zero_eq hx2
      instr "mov w0, #0xffffffea" at strcpy_secure + 0x6c
      instr "ret" at strcpy_secure + 0x70
      refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩, ds, ?_, hm⟩
      rw [StrcpySecureResult, ite_eq_left_of_eq_true _ _ (eq_true (.inr hx2))]
      exact ⟨rfl, rfl⟩
    · intro hx2
      replace hx2 := ccmp_zero_ne hx2
      have hsp' := sp_aligned hsp
      rw [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] at hm
      obtain ⟨ws, hws, hm⟩ := (anybytes_sep_words_iff (k := 6)).mp hm
      obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ :
          ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
        match ws, hws with
        | [w0, w1, w2, w3, w4, w5], _ => exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
      instr "stp x29, x30, [sp, #-48]!" at strcpy_secure + 0xc
      simp only [hsp', Bool.false_eq_true, ↓reduceIte, add_neg_toBitVec]
      store_frame hm 0
      have hm1 := Mem.storeInt_frame_word_sep hm (by omega) 0 (by omega)
        s0.regs.X29.toBitVec
      store_frame hm1 1
      have hm2 := Mem.storeInt_frame_word_sep hm1 (by simp) 1
        (by simp) s0.regs.X30.toBitVec
      simp only [List.set, UInt64.ofBitVec_toBitVec] at hm2
      instr_simp
      have halu := sp_sub_aligned hsp 48#64 rfl
      have hal := sp_aligned halu
      dsimp only at hal
      instr "mov x29, sp" at strcpy_secure + 0x10
      instr "stp x19, x20, [sp, #16]" at strcpy_secure + 0x14
      simp only [hal, Bool.false_eq_true, ↓reduceIte]
      store_frame hm2 2
      have hm3 := Mem.storeInt_frame_word_sep hm2 (by simp) 2
        (by simp) s0.regs.X19.toBitVec
      store_frame hm3 3
      have hm4 := Mem.storeInt_frame_word_sep hm3 (by simp) 3
        (by simp) s0.regs.X20.toBitVec
      instr_simp
      instr "str x21, [sp, #32]" at strcpy_secure + 0x18
      simp only [hal, Bool.false_eq_true, ↓reduceIte]
      store_frame hm4 4
      have hm5 := Mem.storeInt_frame_word_sep hm4 (by simp) 4
        (by simp) s0.regs.X21.toBitVec
      simp only [List.set, UInt64.ofBitVec_toBitVec] at hm5
      instr_simp
      instr "mov x21, x1" at strcpy_secure + 0x1c
      simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
      have hd0 : ¬(s0.regs.X0 = 0 ∨ s0.regs.X2 = 0) := by
        rintro (h0 | h0)
        · exact hx0 h0
        · exact hx2 h0
      instr "cbz x1, 40 <strcpy_secure+0x40>" at strcpy_secure + 0x20
      · intro hz
        have hz : s0.regs.X1 = 0 := UInt64.toBitVec_inj.mp hz
        rw [h_sym]
        instr "mov w0, #0xffffffde" at strcpy_secure + 0x40
        refine eventually_weaken _ _ _ _ ?_ (strcpy_secure_epilogue code
          strcpy_secure h s0 hsp w5 _ R _ _ _ _ (by bv_decide) rfl rfl rfl
          rfl rfl rfl rfl rfl rfl hm5)
        rintro s ⟨hpc, hpres, hx0', hms⟩
        refine ⟨hpc, hpres, ds, ?_, hms⟩
        rw [StrcpySecureResult, ite_eq_right_of_eq_false _ _ (eq_false hd0),
          ite_eq_left_of_eq_true _ _ (eq_true hz), hx0']
        exact ⟨rfl, rfl⟩
      · intro hz
        have hz : s0.regs.X1 ≠ 0 := fun h0 => hz (by rw [h0]; rfl)
        instr "mov x19, x0" at strcpy_secure + 0x24
        instr "mov x20, x2" at strcpy_secure + 0x28
        instr "mov x0, x2" at strcpy_secure + 0x2c
        simp only [ofNat_zero_or64, UInt64.ofBitVec_toBitVec]
        instr "bl strnlen_secure" at strcpy_secure + 0x30
        rw [Std.ExtHashMap.sep_assoc,
          Std.ExtHashMap.sep_comm_l (q := Eq (bs.At s0.regs.X2.toBitVec)),
          Std.ExtHashMap.sep_comm_l (q := Eq (bs.At s0.regs.X2.toBitVec))]
          at hm5
        refine CallSpec.apply (h_strnlen_secure s0.regs.X2 s0.regs.X1 bs _)
          halu ⟨rfl, rfl, h_bs, h_len, hm5⟩ ?_
        rintro regs1 m1 st1 hpres1 ⟨⟨r, hr0, -, hr⟩, hm6⟩
        obtain ⟨hrn, hrz, hrs⟩ := hr hx2
        simp only [CalleeSavedRegsPreserved] at hpres1
        obtain ⟨h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, -,
          hsp1⟩ := hpres1
        dsimp only
        simp only [UInt64.toInt64_ofBitVec_toBitVec]
        instr "cmp x21, x0" at strcpy_secure + 0x34
        simp only [h21, hr0]
        have hX1 := s0.regs.X1.toNat_lt
        have hrt : (UInt64.ofNat r).toBitVec.toNat = r := by
          rw [UInt64.toBitVec_ofNat', BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        instr "b.hi 54 <strcpy_secure+0x54>" at strcpy_secure + 0x38
        · intro hhi
          rw [cmp_hi_iff, hrt, UInt64.toNat_toBitVec] at hhi
          have hrb := strnlen_le_length h_bs hrn hrz
          rw [h_sym]
          rw [Std.ExtHashMap.sep_comm_l (q := Eq (ds.At s0.regs.X0.toBitVec)),
            Std.ExtHashMap.sep_comm_l (q := Eq (ds.At s0.regs.X0.toBitVec))]
            at hm6
          instr "strb wzr, [x19, x0]" at strcpy_secure + 0x54
          rw [h19, hr0]
          store_byte hm6
          have hm7 := Mem.storeInt_byte_sep _ _ r _ m1 hm6 (by omega)
            (by omega) 0
          rw [List.set_eq_take_strcpy_dest (by omega) hrb,
            ← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc] at hm7
          rw [show strcpy_secure + 84 + 4 = strcpy_secure + 0x58 by bv_decide]
          refine eventually_weaken _ _ _ _ ?_ (strcpy_secure_copy code
            strcpy_secure h h_sym s0 hsp w5 ds bs r R (by omega) hrb h_len
            (by omega) regs1 _ _ r (Nat.le_refl r) hr0 h18 h22 h23 h24 h25 h26
            h27 h28 hsp1 h19 h20 hm7)
          rintro s ⟨hpc, hpres, hx0', hms⟩
          refine ⟨hpc, hpres, strcpy_dest ds bs r, ?_, hms⟩
          rw [StrcpySecureResult, ite_eq_right_of_eq_false _ _ (eq_false hd0),
            ite_eq_right_of_eq_false _ _ (eq_false hz)]
          refine ⟨r, hrn, hrz, hrs, ?_⟩
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hx0']
          exact ⟨rfl, rfl⟩
        · intro hhi
          rw [cmp_hi_iff, hrt, UInt64.toNat_toBitVec] at hhi
          have he : r = s0.regs.X1.toNat := by omega
          rw [Std.ExtHashMap.sep_comm_l (q := Eq (ds.At s0.regs.X0.toBitVec)),
            Std.ExtHashMap.sep_comm_l (q := Eq (ds.At s0.regs.X0.toBitVec))]
            at hm6
          instr "strb wzr, [x19]" at strcpy_secure + 0x3c
          rw [h19]
          have hd1 : 1 ≤ ds.length := by
            have : s0.regs.X1.toNat ≠ 0 := fun h0 =>
              hz (UInt64.toNat_inj.mp (by rw [h0]; rfl))
            omega
          simp (disch := first | rfl | exact hd1) only
            [MachineData.store_of_sep64_zero hm6, Effects.All]
          have hm7 := Mem.storeInt_byte_sep _ _ 0 _ m1 hm6 (by omega)
            (by omega) 0
          have e : s0.regs.X0.toBitVec + BitVec.ofNat 64 0 =
              s0.regs.X0.toBitVec := BitVec.add_zero _
          rw [e, ← Std.ExtHashMap.sep_assoc (Eq ((ds.set 0 0).At _)),
            Std.ExtHashMap.sep_comm_l] at hm7
          instr_simp
          instr "mov w0, #0xffffffde" at strcpy_secure + 0x40
          refine eventually_weaken _ _ _ _ ?_ (strcpy_secure_epilogue code
            strcpy_secure h s0 hsp w5 _ R _ _ _ _ (by bv_decide) h18 h22 h23
            h24 h25 h26 h27 h28 hsp1 hm7)
          rintro s ⟨hpc, hpres, hx0', hms⟩
          refine ⟨hpc, hpres, ds.set 0 0, ?_, hms⟩
          rw [StrcpySecureResult, ite_eq_right_of_eq_false _ _ (eq_false hd0),
            ite_eq_right_of_eq_false _ _ (eq_false hz)]
          refine ⟨r, hrn, hrz, hrs, ?_⟩
          rw [ite_eq_left_of_eq_true _ _ (eq_true he), hx0']
          exact ⟨rfl, rfl⟩
  · rename_i hx0
    replace hx0 := cmp_zero_eq hx0
    instr "b.eq 6c <strcpy_secure+0x6c>" at strcpy_secure + 0x8
    · intro _
      instr "mov w0, #0xffffffea" at strcpy_secure + 0x6c
      instr "ret" at strcpy_secure + 0x70
      refine .done _ ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩, ds, ?_, hm⟩
      rw [StrcpySecureResult, ite_eq_left_of_eq_true _ _ (eq_true (.inl hx0))]
      exact ⟨rfl, rfl⟩
    · intro hz
      exact absurd (by decide) hz
