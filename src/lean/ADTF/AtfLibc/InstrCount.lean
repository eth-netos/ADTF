import ADTF.AtfLibc.Listing.memcpy_o
import ADTF.AtfLibc.Listing.memset_o
import ADTF.AtfLibc.Listing.memchr_o
import ADTF.AtfLibc.Listing.memrchr_o
import ADTF.AtfLibc.Listing.memcmp_o
import ADTF.AtfLibc.Listing.strlen_o
import ADTF.AtfLibc.Listing.strnlen_o
import ADTF.AtfLibc.Listing.strnlen_secure_o
import ADTF.AtfLibc.Listing.strcmp_o
import ADTF.AtfLibc.Listing.strncmp_o
import ADTF.AtfLibc.Listing.strchr_o
import ADTF.AtfLibc.Listing.strrchr_o
import ADTF.AtfLibc.Listing.strlcpy_o
import ADTF.AtfLibc.Listing.strtok_r_o
import ADTF.AtfLibc.Listing.swapfunc_o
import ADTF.AtfLibc.Listing.setjmp_o
import ADTF.AtfLibc.Listing.longjmp_o
import ADTF.AtfLibc.Listing.strtoul_o
import ADTF.AtfLibc.Listing.strtoull_o
import ADTF.AtfLibc.Listing.strtol_o
import ADTF.AtfLibc.Listing.strtoll_o
import ADTF.AtfLibc.Listing.unsigned_num_print_o
import Kraken.AArch64.Objdump

/-!
# Number of verified instructions of the TF-A libc functions

Prints, for each function proven in `ADTF.AtfLibc`, the length of the
instruction list that `objdumpAArch64` makes of its listing (the list that
the proofs' `Loaded` hypothesis refers to), and the total. This file is not
imported by `ADTF`; run it with

    lake env lean ADTF/AtfLibc/InstrCount.lean

in `src/lean`. See `README.md` in this directory.
-/

open Kraken.AArch64.Parser

/-- The verified functions and the lengths of their instruction lists. -/
def instrCounts : List (String × Nat) := [
  ("memcpy", (objdumpAArch64(memcpy_o_dump)).length),
  ("memset", (objdumpAArch64(memset_o_dump)).length),
  ("memchr", (objdumpAArch64(memchr_o_dump)).length),
  ("memrchr", (objdumpAArch64(memrchr_o_dump)).length),
  ("memcmp", (objdumpAArch64(memcmp_o_dump)).length),
  ("strlen", (objdumpAArch64(strlen_o_dump)).length),
  ("strnlen", (objdumpAArch64(strnlen_o_dump)).length),
  ("strnlen_secure", (objdumpAArch64(strnlen_secure_o_dump)).length),
  ("strcmp", (objdumpAArch64(strcmp_o_dump)).length),
  ("strncmp", (objdumpAArch64(strncmp_o_dump)).length),
  ("strchr", (objdumpAArch64(strchr_o_dump)).length),
  ("strrchr", (objdumpAArch64(strrchr_o_dump)).length),
  ("strlcpy", (objdumpAArch64(strlcpy_o_dump)).length),
  ("strtok_r", (objdumpAArch64(strtok_r_o_dump)).length),
  ("swapfunc", (objdumpAArch64(swapfunc_o_dump)).length),
  ("setjmp", (objdumpAArch64(setjmp_o_dump)).length),
  ("longjmp", (objdumpAArch64(longjmp_o_dump)).length),
  ("strtoul", (objdumpAArch64(strtoul_o_dump)).length),
  ("strtoull", (objdumpAArch64(strtoull_o_dump)).length),
  ("strtol", (objdumpAArch64(strtol_o_dump)).length),
  ("strtoll", (objdumpAArch64(strtoll_o_dump)).length),
  ("unsigned_num_print",
    (objdumpAArch64(unsigned_num_print_o_dump)).length)]

#eval do
  for (name, n) in instrCounts do
    IO.println s!"{name} {n}"
  IO.println s!"total {(instrCounts.map Prod.snd).sum}"
