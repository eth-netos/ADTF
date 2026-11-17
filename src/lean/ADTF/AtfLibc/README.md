# Verified TF-A libc functions

This directory proves specifications of functions of TF-A's libc against
their object code in the `imx93` release build. Each proof refers to the
instruction list that the elaborator `objdumpAArch64` makes of the objdump
listing in `Listing/` (via the hypothesis `Loaded code f foo_o`).

## Number of verified instructions

| Function | Object file | Instructions |
|---|---|---:|
| memcpy | memcpy.o | 8 |
| memset | memset.o | 26 |
| memchr | memchr.o | 11 |
| memrchr | memrchr.o | 14 |
| memcmp | memcmp.o | 13 |
| strlen | strlen.o | 7 |
| strnlen | strnlen.o | 9 |
| strnlen_secure | strnlen_secure.o | 10 |
| strcpy_secure | strcpy_secure.o | 29 |
| strcmp | strcmp.o | 11 |
| strncmp | strncmp.o | 14 |
| strchr | strchr.o | 9 |
| strrchr | strrchr.o | 10 |
| strlcpy | strlcpy.o | 15 |
| strlcat | strlcat.o | 34 |
| strtok_r | strtok.o | 29 |
| swapfunc | qsort.o | 9 |
| setjmp | setjmp.o | 10 |
| longjmp | setjmp.o | 11 |
| strtoul | strtoul.o | 99 |
| strtoull | strtoull.o | 104 |
| strtol | strtol.o | 101 |
| strtoll | strtoll.o | 101 |
| unsigned_num_print | snprintf.o | 76 |
| **Total** | | **760** |

The 22 functions with loops account for 739 instructions, `setjmp` and
`longjmp` (which have no loops) for 21. The other functions in the same
object files (e.g. the rest of `qsort.o` and `snprintf.o`) are not verified
and not counted.

### How the numbers were obtained

- The counts are the lengths of the instruction lists that `objdumpAArch64`
  makes of the listings, printed by `InstrCount.lean`:

      cd src/lean && lake env lean ADTF/AtfLibc/InstrCount.lean

- For each function, the count equals its symbol size in the object file
  divided by 4, so each listing covers the whole function:

      cd imx-atf/build/imx93/release
      aarch64-none-elf-readelf -sW libc/strtoul.o | grep strtoul

- Every address in these lists is symbolically executed by at least one
  `instr "..." at ...` in the proofs, whose string matches the listing at
  that address, so no listed instruction is left unverified. There are 857
  `instr` steps in total: instructions after a join point (e.g. a shared
  `ret`, or the counter update of `CHECK_AND_PUT_CHAR` in
  `unsigned_num_print`) are stepped once per incoming path, and the three
  `strtok_r` specifications each step the entry sequence. No instruction is
  executed by any other means than the `instr` tactic. A `bl` in
  `strcpy_secure` (to `strnlen_secure`) or `strlcat` (to `strlen`) continues
  with the callee's specification (`CallSpec.apply`), so the callee's
  instructions are counted only in the callee's row.
