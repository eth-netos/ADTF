# Verifying AArch64 object files in Lean: plan and design decisions

This document records the plan and the design decisions for verifying the
code in AArch64 object files with Kraken (the `kraken` submodule). It is
extended as the design develops. It started as the design of an ELF parser
(sections 2 to 5); section 1 describes the goal that replaced that, and
section 1.5 which parts of the parser design are still needed.

## 1. Goal

Write proofs about the functions in AArch64 object files (`.o`), as the
compiler and assembler produce them, using Kraken. The first use case is
TF-A's BL31 for the i.MX 93 (the `imx-atf` submodule), whose build leaves
114 object files (section 2).

Later, the proofs should compose as the object files get linked: a proof
about each object file, plus facts about how the linker placed them, should
give a proof about the linked `bl31.elf`. This is postponed, but the design
keeps it in mind (section 1.4).

Constraint: only open-source software is used (the two proprietary NXP
firmware files that the i.MX 93 boot image needs are the only exception, and
they are not needed here).

### 1.1 Definition of success

Earlier, the plan measured progress by round-trip properties of an ELF
parser and encoder (section 5). These are tests of a tool, not the goal:
they say that a file was read correctly, not that anything about its code
was proven. They also make less sense once instructions come from objdump
(section 4.5), since there is no Lean decoder whose output could be
encoded back (section 5.0).

Success is now: Lean theorems, checked by Lean, about a few interesting
functions of BL31, stated about the code as it is in the object files that
the BL31 build produced, and proven with instruction beacons (section 1.3).
For the first milestone, these are platform-independent functions that
exercise features a proof about real firmware needs: loops, memory
buffers, calls between object files, tail calls, function pointers
(section 1.2.1). The TRDC functions (the Trusted Resource Domain Controller,
which the i.MX 93 uses to restrict which bus masters may access which memory
and peripherals) are the eventual goal, but need a TRDC semantics combined
with Kraken's ISA semantics, planned via Sockeye's Lean backend
(section 1.2.2).

Each theorem says what the function does to registers and memory, under
which preconditions, and that it returns to its caller.
What the trusted base of such a theorem is (objdump, the converter of
section 4.5, Kraken's semantics) is stated next to it.

### 1.2 Candidate functions

Each function is in its own section in its object file
(`-ffunction-sections`). Sizes are from the object files. The features that
a function exercises are what makes it interesting beyond its size.

#### 1.2.1 First milestone: platform-independent functions

Verifying the TRDC functions (section 1.2.2) needs a semantics of the TRDC,
combined with Kraken's ISA semantics. That is planned via Sockeye's Lean
backend, but too big for a first milestone. So the first milestone takes
functions that access no device registers and no system registers, and
contain none of the instructions that Kraken lacks (section 4.4). This was
checked by listing the mnemonics of each function in `objdump -d` of its
object file. Their specs only talk about registers and ordinary memory,
which Kraken's semantics already covers.

The C library that TF-A brings along (`lib/libc`, built into
`build/imx93/release/libc/*.o`) is the richest source. Not all of it is
linked into `bl31.elf`, but all of it is in object files, which is what is
verified.

Leaf functions with loops over memory, whose specs relate memory to Lean
functions on `List UInt8`:

- `strlen` (28 bytes, 8 instructions): the simplest loop; precondition: a
  NUL-terminated string in memory.
- `strnlen`, `memchr`, `strchr` (36, 44, 36 bytes), `memrchr` (56),
  `strrchr` (40, uses `csel`): read-only searches.
- `memcmp`, `strcmp`, `strncmp` (52, 44, 56 bytes): two buffers, a signed
  result.
- `memcpy` (32 bytes): a byte copy loop; separation logic for two disjoint
  buffers.
- `memset` (104 bytes): aligns, then stores whole words whose value is the
  byte replicated by a `mul`, then the tail; bit-level reasoning.
- `strlcpy` (60 bytes), `strtok_r` (116 bytes): writes, and a pointer as
  result (`strtok_r` also keeps state in memory between calls).
- `swapfunc` (36 bytes, static, in `qsort.o`).

Arithmetic:

- `page_align` (28 bytes, `bl_common.o`), `plat_core_pos_by_mpidr` (28,
  `csinv`), `imx_validate_ns_entrypoint` (20, a security check: rejects
  non-secure entry points below `PLAT_NS_IMAGE_OFFSET`, `0x80200000`). The
  last two are in platform files, but are pure computations.
- `strtoul`, `strtol`, `strtoull`, `strtoll` (396 to 416 bytes): digit
  parsing with overflow detection (`udiv`, `madd`, `umulh`); the spec
  compares with a reference function in Lean.
- `unsigned_num_print` (304 bytes, static, in `snprintf.o`): number to
  digits with `udiv` and `msub`, into a buffer.

Calls between object files (relocations `CALL26` and `JUMP26`), the first
step towards composition (section 1.4):

- `memmove` (52 bytes): copies backwards itself, and otherwise tail-calls
  `memcpy` (`b memcpy`, a `JUMP26` relocation).
- `memcpy_s` (136 bytes) calls `memcpy`; `strlcat` (136) calls `strlen`;
  `strcpy_secure` (116) calls `strnlen_secure` (40).
- `setjmp`, `longjmp` (40, 44 bytes, assembly): save and restore the
  callee-saved registers and `sp`; `longjmp` returns to where `setjmp` was
  called, so its spec is about control flow, not about a return.
- Stretch: `qsort` (4 bytes) tail-calls `local_qsort` (796 bytes, static),
  which is recursive and calls the comparison function through a function
  pointer (`blr`), so its spec takes the comparison function's spec as a
  parameter.
- Stretch: `vsnprintf` (1,364 bytes): a `switch` compiled to a jump table
  (`adr`, `br`), and variadic arguments (`va_list`).

Data structures of TF-A that do not depend on the platform:

- `psci_find_max_off_lvl` (76 bytes), `psci_find_target_suspend_lvl` (52),
  in `psci_common.o`: small functions on PSCI's power state structures.
- `find_xlat_table_entry` (148 bytes, static, `xlat_tables_utils.o`): walks
  translation tables in memory; loads only.
- `mmap_add_region_ctx` (548 bytes, `xlat_tables_core.o`): inserts a region
  into the sorted memory map, rejecting overlaps; calls `memmove` and
  `memcpy`. A security-relevant invariant (the map stays sorted and without
  overlaps).
- Stretch: `xlat_tables_map_region` (428 bytes): recursive; calls
  `xlat_desc` (236 bytes), which calls `xlat_arch_get_pas` and
  `xlat_arch_regime_get_xn_desc` (pure, a few instructions).

Some of these call platform code on error paths only (`tf_log`,
`console_flush`, `el3_panic`, `plat_panic_handler`). Their specs enter as
hypotheses about undefined symbols, e.g. "does not return", or the
precondition excludes the error; both fit the composition plan of
section 1.4.

Suggested order: `strlen`, `memcpy`, `memcmp`, `memset`, `memmove` (first
call), `strlcat`, `setjmp`/`longjmp`, `strtoul`, `mmap_add_region_ctx`.

#### 1.2.2 Later: TRDC functions

These need a TRDC semantics combined with Kraken's ISA semantics (planned via
Sockeye's Lean backend). From `drivers/nxp/trdc/imx_trdc.c` (`imx_trdc.o`)
and `plat/imx/imx93/trdc.c` (`trdc.o`), roughly in the order in which they
could be done:

- `trdc_get_mbc_base` (static, 32 bytes): leaf; reads `TRDC_HWCFG0` (MMIO,
  `ldrh`); `csel`.
- `trdc_mbc_enabled`, `trdc_mrc_enabled` (12 bytes each): one MMIO read, bit
  test.
- `trdc_mrc_set_control` (60 bytes): call to a static function in another
  section (`CALL26` against a section symbol); stack frame (`stp x29, x30`);
  `ccmp`; MMIO write.
- `trdc_mrc_rgn_config` (152 bytes): the MRC region descriptor writes; alignment
  masks; 8 arguments.
- `trdc_mbc_blk_config` (220 bytes): `switch` compiled to a comparison tree;
  `umaddl`; read-modify-write of a 4-bit field of an MMIO register.
- `trdc_mda_set_cpu` (132 bytes): 10 arguments, 2 of them on the stack
  (`ldrb w8, [sp, #8]`); read-check-write-lock.
- `trdc_mda_set_noncpu` (100 bytes): as above, 7 arguments.
- `trdc_fuse_read` (88 bytes): global data (`fuse_data` in `.data`) via
  `ADRP`/`ADD`/`LDST8` relocations; unrolled loop.
- `trdc_mbc_set_control` (164 bytes): loop over a global table
  (`trdc_mgr_blks`); early returns.
- `trdc_mgr_mbc_setup` (164 bytes): loop of calls; callee specs used in a proof.
- `trdc_setup` (524 bytes): nested loops of calls driven by a configuration
  table in memory; the function whose spec says "the TRDC ends up configured as
  the table says".
- `trdc_config` (440 bytes): stretch goal: tables with pointers
  (`R_AARCH64_ABS64` relocations in `.data.trdc_cfg_info`), the inlined ELE fuse
  read (MMIO polling loop), a call to `NOTICE` (`printf`).

The ToySys model (`doc/ToySys/System.lean`) already has a TRDC whose MRC
region descriptors are written by a firmware program; the spec of
`trdc_mrc_rgn_config` and `trdc_setup` can state their effect in the same
terms, which is the link from these proofs to the system-level properties of
ToySys.

#### 1.2.3 Later: other platform-dependent functions

These exercise further features, but need device registers, system
registers, or instructions without semantics, or call platform code on
their main path:

- `get_arm_std_svc_args` (12 bytes): returns the address of data in `.rodata`
  (`ADRP`/`ADD`).
- `console_lpuart_putc` (56 bytes): assembly (`.S`); MMIO polling loop on a
  status register, so termination depends on the device.
- `psci_smc_handler` (332 bytes): `switch` compiled to a jump table (`ldrb` from
  `.rodata`, `adr`, `br x3`); many calls.
- `udelay` (104 bytes): platform-independent C, but calls the platform's
  timer through a function pointer in global data, so its spec needs the
  timer's spec; indirect calls through a function pointer in global data
  (`blr x0`); callee-saved registers `x19`-`x21`; `udiv`.
- `psci_validate_power_state` and similar: tail call through a function pointer
  (`br x16`).
- `plat_my_core_pos` (16 bytes): `mrs mpidr_el1`: blocked until `mrs` has
  semantics (section 4.4).
- `spin_lock`, `spin_unlock` (32, 8 bytes): `ldaxr`/`stxr`/`wfe`/`sevl`/`stlr`:
  blocked until these have semantics, and needs a model of other cores.
- `flush_dcache_range` (56 bytes): `mrs ctr_el0`, `dc civac`, `dsb`: blocked as
  above.

The functions marked "blocked" contain instructions that get no semantics
for now (section 4.4).

### 1.3 Proof style: instruction beacons

Proofs step through a function with an instruction beacon per instruction,
as `doc/ToySys/ISA.lean` does with its `instr i at a` tactic: `i` is the
instruction and `a` its address, both redundant (they follow from the program
and the state), but checked, so that a proof script can be read next to a
disassembly and fails at the first place where it and the code disagree.

For object files, the natural form is the text that objdump prints, at the
function's symbol plus the offset that objdump prints, e.g.

```lean
  instr "ldrb w1, [x4, #-1]!" at memmove + 0x28
```

Kraken has no such tactic. Its `kstep` steps through straight-line code
without naming the instructions. Porting `instr` means:

- parsing the instruction with Kraken's assembly parser (so that objdump's
  text can be pasted) and comparing it with the fetched `Operation`;
- expressing the address relative to a symbol whose address the `Labels`
  instance gives, since an object file has no addresses (section 1.4);
- the special cases that ToySys has: conditional branches give two goals,
  calls continue with the callee's spec.

### 1.4 Composability under linking (postponed)

What a proof about one object file can assume, so that proofs compose:

- Addresses of symbols are parameters (Kraken's `Labels` class), not fixed
  numbers: undefined symbols, and the sections of the object file itself,
  get their addresses only from the linker. A relocation becomes an operand
  that mentions the symbol (section 2).
- A call to another function is justified by that function's spec, as a
  hypothesis of the theorem. ToySys's `swap_swap_ok` does this with a
  `Symbols` map and one `Loaded` hypothesis per function; linking then
  amounts to discharging the hypotheses of one object file's theorems with
  the theorems of another.
- What the linker does has to be stated as facts about the linked file:
  each section's bytes end up at its address, with the relocated fields
  filled in. Checking this for `bl31.elf` needs the ELF container parser for
  executables (sections 3 and 5) and an instruction encoder or decoder for
  the relocated fields.
- Kraken's `NOTES.md` discusses why its layout-based semantics makes
  composition of programs hard, and plans to make the semantics depend only
  on the addresses of the current and the next instruction, which would help.

### 1.5 What of this design is still needed

Still needed:

- The objdump-based code layer (section 4.5): `objdump -d -r` output,
  converted to assembly that Kraken's parser reads, with relocations as
  `ConstExpr` operands. This replaces the Lean decoder for the first
  milestone.
- Adding the missing instructions to Kraken's `Operation`, parser and
  printer without semantics (section 4.4). The first targets avoid them, but
  the files contain them, so the converter must accept them.
- An ELF container parser for object files (section 3), because some
  proofs need what `objdump -d` does not give (section 4.5): the contents of
  data sections, relocations in data sections, and the symbol table. Most
  first-milestone targets (section 1.2.1) get by without it, since they
  only access memory passed in by pointer; the first that needs it is
  `vsnprintf`, whose jump table is in `.rodata.vsnprintf`. The TRDC
  functions need it for `fuse_data`, `trdc_mgr_blks` and the configuration
  tables (with `R_AARCH64_ABS64` relocations in `.data.trdc_cfg_info`).
  Executables (`bl31.elf`) and segments can wait until the composition
  step.
- The mapping-symbol background (section 2.1) stays as an explanation of
  why objdump can tell code from data; the converter itself does not need
  them.

New, and not in Kraken yet:

- Instruction beacons (section 1.3).
- Later, for the TRDC functions (not the first milestone): MMIO with a
  device model. Every TRDC function accesses device registers.
  Kraken's AArch64 semantics has `nonmem_load` and `nonmem_store` effects,
  but its `Effects.All` maps them to `False`, so no MMIO access can be
  verified yet. Kraken's x86-64 side has an example with a device state
  (`Kraken/X64/Examples/IncrementMMIO.lean`), and ToySys has a `Platform`
  with `read` and `write` relations; one of these designs has to come to
  AArch64, with the device semantics generated by Sockeye's Lean backend.
- Calls: specs of callees as hypotheses, the link register, callee-saved
  registers and the stack frame. Kraken's AArch64 examples on `main` have no
  calls; the `vcgen` branch (Sebastian Graf's, not merged) has
  frame-based specs and a call example for x86-64 only.
- A way to state the initial contents of data sections in a precondition,
  from the parsed ELF file.

Already in Kraken (`main` at `c9aa45e`):

- The assembly parser, accepting objdump's aliases (`mov`, `cmp`, `lsl`,
  `cset`, `tst`, `ubfx`, ...), and `parseAArch64("...")` to write programs
  in Lean files.
- `ConstExpr` with `label`, `pg_hi21` and `lo12`, and the `Labels` class for
  symbol addresses, which is what relocations need.
- `Effects.unimplemented`, whose weakest precondition is `False`.
- Symbolic execution (`kstep`, `kprologue`), separation logic for memory
  (`=⋆`, `ecancel`, `load_sep`, `store_sep`), and `Eventually` with
  `eventually_trans` and a loop rule (`reg_dec_loop`).
- Kraken's README says it verifies code "disassembled from compiler output
  (`.o` files)", but `main` contains no tool for that; the converter of
  section 4.5 is new.

Can go away, or is postponed:

- The Lean instruction decoder (sections 4.1 to 4.3): postponed. objdump
  takes its place. The `sail-arm` encodings are still the reference if a
  Lean decoder or encoder is written later to take objdump out of the
  trusted base (section 5.0).
- The byte-exact ELF round trip and the `Layout` cruft (sections 5.1 to
  5.4): postponed; comparing the parsed container with `readelf` output
  tests the parser better (section 5.0).
- The pretty-printer compared with objdump (section 5.6): dropped, since
  objdump is now the source of the instructions, not an oracle.
- The code-layer datatype `CodeItem`/`CodeSection` (section 3): replaced by
  one Kraken `Program` per section, as Kraken's parser produces it, plus the
  symbols of that section as labels.

## 2. Test inputs at hand

Building BL31 (`make PLAT=imx93 bl31` in `imx-atf`, with Arm GNU Toolchain
14.3.Rel1 for `aarch64-none-elf`) leaves its intermediate files in
`imx-atf/build/imx93/release`:

- 114 object files (`bl31/*.o`, `libc/*.o`), each `ELF 64-bit LSB
  relocatable, ARM aarch64`. They are not deleted after linking;
  `lib/libc.a` is an archive of the `libc` ones. The `.d` files next to them
  are make dependency files.
- `bl31/bl31.elf`, the linked executable (entry point `0x204e0000`, two
  `PT_LOAD` segments), plus `bl31.map` (linker map) and `bl31.dump`
  (disassembly).
- `bl31.bin`, the raw image that goes into the boot image.

Observations from `readelf` that matter for the design:

- TF-A compiles with `-ffunction-sections -fdata-sections`, so each function
  is its own section (`.text.bl31_main`) with its own relocation section
  (`.rela.text.bl31_main`). This makes a section a natural unit of code.
- Relocations seen in `bl31_main.o`, where S is the symbol's address, A the
  addend and P the address of the instruction being patched:
  - `R_AARCH64_ADR_PREL_PG_HI21`, for ADRP: the 21-bit immediate becomes
    `Page(S + A) - Page(P)` in units of 4 KiB pages, where `Page(x)` clears
    the low 12 bits. "PREL" means PC-relative, "PG" page, "HI21" the high 21
    bits of the page offset (giving a range of ±4 GiB).
  - `R_AARCH64_ADD_ABS_LO12_NC`, for the ADD that follows such an ADRP: the
    12-bit immediate becomes the low 12 bits of `S + A`, i.e. the offset
    within the page. "ABS" means absolute (not PC-relative), "NC" no
    overflow check, since the higher bits are dropped on purpose.
  - `R_AARCH64_CALL26`, for BL, and `R_AARCH64_JUMP26`, for B: the 26-bit
    immediate becomes `(S + A - P) / 4`, a PC-relative branch of ±128 MiB.
    The two differ only in that a linker may insert a veneer for BL that
    clobbers x16/x17.

  So an ADRP/ADD pair materializes the address of `S + A`. Kraken's
  `ConstExpr` already has `label`, `pg_hi21`, `lo12`, `add` and `int64`, so
  an instruction plus its relocation can become an `Operation` whose operand
  is e.g. `.pg_hi21 (.add (.label "sym") (.int64 addend))`.
- The toolchain emits mapping symbols (section 2.1); `bl31.elf` has 472 of
  them.
- Instructions in `bl31.elf` that Kraken's `Operation` does not cover yet
  (counts from `objdump -d`, which prints about 9,780 instructions plus 65
  `.word` and 1 `.short` data items in executable sections): `mrs` (130),
  `msr` (115), `isb` (36), `dsb` (26), `dc` (7), `wfi` (7), `eret` (3),
  `wfe` (2), and one each of `tlbi`, `sev`, `sevl`, `psb`, `udf`, `ldaxr`,
  `stxr`, `stlr`, `stlrb`, `ldarb`. Roughly 4% of the code; the rest are
  integer, load/store and branch instructions that Kraken has (`objdump`
  prints aliases such as `mov`, `cmp`, `tst`, `lsl`, `ubfx`, `cset`).
  How they are handled is decided in section 4.4.

### 2.1 Mapping symbols: `$x` and `$d`

An executable section is just bytes; nothing in the section itself says
which bytes are instructions. Besides instructions, compilers and
assemblers put data into executable sections: literal pools (constants that
an `ldr x0, =value` loads PC-relatively), jump tables of `switch`
statements, and, in a linked file, whatever the linker script merges into
the same output section (in `bl31.elf`, the read-only strings such as
`"BL31: %s"` end up in the executable `.ro` section). An instruction word
and a data word can have the same bits, so the bytes alone cannot tell them
apart.

The AArch64 ELF ABI (Arm's "ELF for the Arm 64-bit Architecture") solves
this with mapping symbols: local symbols of type `NOTYPE` and size 0 whose
name says what starts at their address, until the next mapping symbol in the
same section:

- `$x` (or `$x.<anything>`): A64 instructions start here.
- `$d` (or `$d.<anything>`): data starts here.

The assembler emits them automatically. `readelf -s` on `bl31_main.o` shows
e.g. `$x` at offset 0 of each `.text.*` section, and `bl31.elf` has `$d` at
`0x204e0170`, where `objdump -d` then prints `.word 0x5d1b0020` instead of
an instruction, and in front of the strings in `.ro`, which it prints as a
hex dump.

They are ordinary symbols, so `strip` removes them together with all other
symbols. On a stripped copy of `bl31.elf` (made with `aarch64-none-elf-strip`
for this check), `objdump -d` has nothing to go by and decodes everything
in `.ro` as instructions: 10,504 lines instead of about 9,850, among them
609 `udf` or `.inst` lines for words that are no valid instruction, and
plausible-looking but wrong instructions for the strings.

How often files lack them, checked with `aarch64-none-elf-strip` 14.3 on
`bl31_main.o` (9 mapping symbols) and `bl31.elf` (472):

| `strip` option              | `.o` keeps them | executable keeps them |
|-----------------------------|-----------------|-----------------------|
| `--strip-debug`, `-X`       | yes             | yes                   |
| `--strip-unneeded`, `-x`    | yes             | no                    |
| none (= `--strip-all`)      | no              | no                    |

- Object files: the assembler always emits them, and nobody strips object
  files fully, since that would remove the symbols the linker needs. So
  for the main use case (reasoning about `.o` files) they are there.
- Executables from a build directory (`bl31.elf`, U-Boot's `u-boot`,
  Linux's `vmlinux`) are not stripped and have them.
- Executables installed by a Linux distribution or a Yocto image are
  usually stripped, and both `--strip-all` and `--strip-unneeded` remove
  mapping symbols from executables; the debug symbols, if kept, go to a
  separate debug file that contains the symbol table.
- Firmware is usually not shipped as an ELF file at all: the build turns
  `bl31.elf` into the flat binary `bl31.bin` (no headers, no symbols), and
  that is what goes into the boot image. To reason about it, one takes the
  `bl31.elf` of the same build and checks that its loaded contents equal
  `bl31.bin`.

So files without mapping symbols are common in deployment, but the files
this project will parse (object files and unstripped build outputs) have
them. For a stripped file, the parser can fall back to treating all
executable sections as code and keeping undecodable words as `undecoded`,
with the caveat that data may be decoded as instructions.

## 3. Lean datatype for an ELF file (first sketch)

See section 1.5 for which parts of this section are still needed.

Two layers:

1. A faithful container layer that mirrors the file: header, sections with
   their raw bytes, segments, symbols and relocations. Parsing it needs no
   knowledge of instructions. Unknown enum values are kept (`other n`) rather
   than rejected, so that any valid ELF file parses.
2. A code layer on top: the executable sections decoded into Kraken
   instructions, with relocations and symbols folded into the operands.

The container layer accepts ELF64 little-endian files for any machine and
does not depend on the architecture; it lives in its own directory (or
file), separate from the AArch64-specific code. The code layer is
instantiated only for AArch64 for now and rejects files whose `e_machine`
is not `EM_AARCH64` (183). Other architectures (Kraken also has x86-64)
can be added later by instantiating the code layer for them.

```lean
namespace Elf

inductive FileType
  | rel | exec | dyn | core | other (n : UInt16)

structure Header where
  type : FileType
  entry : UInt64
  flags : UInt32

inductive SectionType
  | null | progbits | symtab | strtab | rela | nobits | rel | group
  | other (n : UInt32)

structure Section where
  name : String
  type : SectionType
  flags : UInt64      -- SHF_WRITE, SHF_ALLOC, SHF_EXECINSTR, ...
  addr : UInt64       -- 0 in object files
  size : UInt64       -- for `nobits`, `data` is empty but `size` is not
  link : UInt32
  info : UInt32
  addralign : UInt64
  entsize : UInt64
  data : ByteArray

/-- A program header; only present in executables and shared objects. -/
structure Segment where
  type : UInt32       -- PT_LOAD, PT_GNU_STACK, ...
  flags : UInt32      -- PF_R, PF_W, PF_X
  offset : UInt64
  vaddr : UInt64
  paddr : UInt64
  filesz : UInt64
  memsz : UInt64
  align : UInt64

inductive SymbolBinding | «local» | global | weak | other (n : UInt8)
inductive SymbolType
  | notype | object | func | «section» | file | other (n : UInt8)

/-- Where a symbol is defined. -/
inductive SymbolSection
  | undef               -- defined in another object file
  | abs                 -- absolute value, not relative to a section
  | common
  | index (i : Nat)     -- index into `Elf.sections`

structure Symbol where
  name : String
  value : UInt64        -- offset in its section (object file) or address
  size : UInt64
  binding : SymbolBinding
  type : SymbolType
  visibility : UInt8
  sec : SymbolSection

inductive RelocType
  | abs64 | prel32 | adrPrelPgHi21 | addAbsLo12Nc | ldst64AbsLo12Nc
  | call26 | jump26 | condbr19 | other (n : UInt32)
  -- (to be completed with the types that actually occur)

structure Rela where
  offset : UInt64       -- offset in the target section
  symbol : Nat          -- index into `Elf.symbols`
  type : RelocType
  addend : Int64

structure File where
  header : Header
  sections : Array Section
  segments : Array Segment          -- empty for object files
  symbols : Array Symbol            -- from `.symtab`
  /-- For each section index, the relocations that apply to it. -/
  relocations : Std.HashMap Nat (Array Rela)

end Elf
```

Code layer, sketch:

```lean
/-- One 4-byte-aligned piece of an executable section. -/
inductive CodeItem
  | instr (i : Kraken.AArch64.Instr)   -- operands may mention labels
  | undecoded (w : UInt32)             -- not (yet) supported by the decoder
  | data (bytes : ByteArray)           -- between `$d` and the next `$x`

structure CodeSection where
  name : String
  items : Array (UInt64 × CodeItem)    -- offset in the section, item
  labels : Array (UInt64 × String)     -- symbols defined in this section
```

Open points:

- The sketch does not yet have the `Layout` field of section 5.3.
- Whether a `CodeSection` can simply be turned into a Kraken `Program`
  (`instr`, `label` and `byteArray` directives) for each section, with
  Kraken's `Labels` class providing the symbol addresses that the linker
  would choose. Kraken already treats an `.int64` branch target as relative
  to the current instruction and a `.label` as absolute, which fits object
  files. What does not fit is a whole file: several sections, undefined
  symbols, symbol sizes and bindings.
- Whether `Section.data` should keep the bytes of non-executable sections
  (needed for constant data that code reads, e.g. `.rodata.psci_args.0`).
- Representation of the raw integer fields: `UInt64` follows the file;
  `BitVec 64` is what Kraken's semantics uses.
- Static archives (`libc.a`) could later be read as a list of object files.

### 3.1 Why section contents stay bytes in the container layer

An alternative is a single datatype whose executable sections hold decoded
instructions instead of bytes. Reasons for keeping bytes in the container
layer and computing the decoded view from them:

- Code and data cannot always be told apart (section 2.1). Executable
  sections contain data too (literal pools, jump tables, strings), and only
  the `$x`/`$d` mapping symbols say where. In a stripped executable there
  are no symbols, so a datatype holding decoded instructions would have no
  sound way to fill itself: decoding everything turns data into wrong
  instructions. Even with mapping symbols, the data regions have to be
  bytes, so the datatype needs bytes in executable sections anyway.
- The ELF round trip of section 5 would depend on an exact instruction
  round trip (section 5.5): every word would have to be decoded and encoded
  back bit for bit, including encodings that Kraken's `Operation` does not
  distinguish. Every gap in the decoder would break the ELF tests, which
  could otherwise be finished before the decoder.
- The container layer does not depend on the architecture. Kraken also has
  an x86-64 backend, and the same container parser and encoder could serve
  it, with only the code layer being specific to AArch64.
- Proofs can refer to the actual file: a statement like "the bytes at this
  offset decode to this `Operation`" keeps the decoder visible as a function
  that is part of the trusted base, instead of hiding it inside the parser.

The decoded view should still be as convenient as a decoded datatype. One
way is to make the container parametric in the section contents, e.g.
`File (Contents : Type)`, with `parse : ByteArray -> Except String (File
ByteArray)` and a `File.map` that turns `File ByteArray` into `File
CodeSection` for executable sections. Encoding a `File CodeSection` back
into bytes would need the instruction encoder of section 5.5, and is not
planned.

## 4. Where instruction decoding information comes from

### 4.1 Sail's Arm model

`rems-project/sail-arm` contains Sail models of the Arm architecture,
translated automatically from Arm's ASL specification (2023-03 version for
`arm-v9.4-a`). License: BSD 3-Clause Clear, which is open source; "Clear"
means it explicitly grants no patent rights. Copyright holders include Arm.

Unlike the Sail RISC-V model, which has an `ast` union type and an `encdec`
mapping between bits and AST, the Arm model has no instruction AST. Each
encoding is a clause of a scattered decode function that matches the opcode
bits, slices out the fields and calls a `decode_*` function, which computes
the operands and directly calls the `execute_*` function. For ADD (shifted
register), from `arm-v9.4-a/src/instrs64.sail`:

```sail
function clause __DecodeA64_DataProcReg ((pc, ([_, bitzero, bitzero,
    bitzero, bitone, bitzero, bitone, bitone, _, _, bitzero, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] as __opcode))
    if SEE < 14) = {
    SEE = 14;
    let Rd = Slice(__opcode, 0, 5);
    let Rn = Slice(__opcode, 5, 5);
    let imm6 = Slice(__opcode, 10, 6);
    let Rm = Slice(__opcode, 16, 5);
    let shift = Slice(__opcode, 22, 2);
    let S = Slice(__opcode, 29, 1);
    let op = Slice(__opcode, 30, 1);
    let sf = Slice(__opcode, 31, 1);
  decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg(
      Rd, Rn, imm6, Rm, shift, S, op, sf)
}

function
decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
    (Rd, Rn, imm6, Rm, shift, S, op, sf) = {
    let 'd = UInt(Rd);
    let 'n = UInt(Rn);
    let 'm = UInt(Rm);
    let 'datasize = if sf == 0b1 then 64 else 32;
    let sub_op : bool = op == 0b1;
    let setflags : bool = S == 0b1;
    if shift == 0b11 then {
        throw(Error_Undefined())
    };
    if sf == 0b0 & [imm6[5]] == 0b1 then {
        throw(Error_Undefined())
    };
    let shift_type : ShiftType = DecodeShift(shift);
    let 'shift_amount = UInt(imm6);
    execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg(
      d, datasize, m, n, setflags, shift_amount, shift_type, sub_op)
}

function execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
    (d, datasize, m, n, setflags, shift_amount, shift_type, sub_op) = {
    result : bits('datasize) = undefined;
    let operand1 : bits('datasize) = X_read(n, datasize);
    operand2 : bits('datasize) =
      ShiftReg(m, shift_type, shift_amount, datasize);
    nzcv : bits(4) = undefined;
    carry_in : bits(1) = undefined;
    if sub_op then {
        operand2 = not_vec(operand2);
        carry_in = 0b1
    } else {
        carry_in = 0b0
    };
    (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
    if setflags then {
        (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv
    };
    X_set(d, datasize) = result
}
```

The pattern is the encoding `sf op S 01011 shift 0 Rm imm6 Rn Rd` written
from bit 0 upwards; `SEE` is ASL's mechanism for ordering overlapping
encodings. Decode and execute are fused, so the model cannot be used as is to
produce a decoded instruction; it can only run one.

### 4.2 Sail to Lean

Sail has a Lean backend (`sail -lean`, experimental since Sail 0.20), and
`sail-arm`'s `arm-v9.4-a/Makefile` has a `gen_lean` target. Work on it is
recent and ongoing (October 2026):

- rems-project/sail#1769 (merged 2026-10-09): Lean backend fixes found while
  translating `sail-arm`, among them an exponential blowup in the Arm decode
  functions.
- rems-project/sail-arm#33 (merged 2026-10-13): translates slices of the
  v9.4 model (selected with Sail's slicing options, rooted at the `execute_*`
  functions of the instructions a proof needs) and tests the result against
  an Apple M4. Small slices (`add`, `eor`, `extr`) build in seconds, but the
  integer data-processing decoder is one 2,542-line definition taking over
  40 minutes to elaborate, and `ldr` did not finish in 30 minutes. No
  repository with the generated Lean is published.

So no ready-to-use Lean translation of the Arm model exists, and translating
the decoder is currently the slow part.

### 4.3 Options

1. Agent-written Lean decoder from bit patterns to Kraken `Operation`s,
   with the encodings taken from `sail-arm` (patterns and field slices in
   the `__DecodeA64_*` clauses, conditions in the `decode_*` functions).
   Kraken's `Operation` set is small (about 100 constructors), so this is a
   bounded amount of code. **Chosen**, see below.
2. A code generator that extracts the patterns and field slices from the
   `sail-arm` sources (or Sail's JSON/IR output) and emits the Lean pattern
   matching; the mapping from fields to Kraken operands would still be
   code that cannot be produced by the generator.
3. Translate the `sail-arm` decoder to Lean with Sail's backend. This does
   not give a decoded instruction (decode calls execute), and it is
   currently slow to elaborate.

Independently of the option, the decoder can be tested against an existing
disassembler without any new dependency: `aarch64-none-elf-objdump` prints
the assembly of each word, Kraken's assembly parser turns that text into an
`Operation`, and the result must equal the decoder's output. The object files
from section 2 give thousands of real test words, and Kraken's fuzzer can
generate more.

Other Lean work to look at: LNSym (github.com/leanprover/LNSym), a
symbolic simulator for Armv8 machine code in Lean, which has its own
decoder; its coverage and license are not checked yet.

Decision: option 1. The decoder is agent-written Lean that maps bit patterns
to Kraken `Operation`s, and the encodings (bit patterns, field positions,
conditions under which an encoding is undefined, and the order of
overlapping encodings) are taken from `sail-arm`'s `arm-v9.4-a` sources.
Each decoder case should name the `sail-arm` clause it follows, so that it
can be reviewed against it. Option 2 does not save much, since the mapping to
Kraken's operands cannot be produced by a code generator anyway, and option
3 does not produce decoded instructions.

### 4.4 Instructions that Kraken does not have yet

Decision: the instructions missing from Kraken's `Operation` (section 2:
`mrs`, `msr`, `isb`, `dsb`, `dc`, `tlbi`, `eret`, `wfi`, `wfe`, `sev`,
`sevl`, `udf`, and the exclusive and acquire/release loads and stores) are
added as new constructors of Kraken's `AArch64.Operation`, without
semantics. Semantics need a human review, for which there is no time now.

Until they get semantics, executing one of them yields Kraken's existing
`Effects.unimplemented (msg : String)`, which Kraken's AArch64 semantics
already returns for e.g. execution reaching a data block. In
`Kraken/AArch64/OmniSemantics.lean`, its weakest precondition is `False`, so
proofs about code paths that reach such an instruction get stuck there
instead of proving anything wrong, while code that does not reach it can
still be verified. No new `Effects` constructor is needed.

Since the new constructors are part of `Operation`, Kraken's printer and
its assembly parser have to handle them too; the objdump-based testing above
needs at least the parser. Kraken's fuzzer derives its instruction
generator from all constructors of `Operation` (`gen_ctors% Operation` in
`KrakenRunnerAArch64.lean`) and compares Kraken's results with real
execution, so it has to skip the constructors without semantics.

The `undecoded` code item (section 3) remains for words the decoder does not
recognize at all, e.g. SIMD and floating-point instructions, which do not
occur in BL31.

### 4.5 Alternative without a decoder: objdump and Kraken's parser

Instead of decoding instruction words in Lean, the code layer could be
produced from the text that GNU `objdump -d -r` prints, read by Kraken's
existing assembly parser:

1. Run `objdump -d -r` on the file.
2. A converter (Lean or a script) turns objdump's listing into assembly that
   Kraken's parser accepts: drop addresses and raw bytes, drop objdump's
   annotations (`<symbol>` after branch targets, `//` comments), turn each
   section into a label per symbol plus instructions, turn data lines
   (`.word`, hex dumps) into `byteArray` directives, and fold each
   relocation line into the operand of the instruction above it (e.g.
   `adrp x0, 0 <...>` with `R_AARCH64_ADR_PREL_PG_HI21 .rodata.psci_args.0`
   becomes `adrp x0, .rodata.psci_args.0`, and the `add` with
   `R_AARCH64_ADD_ABS_LO12_NC` becomes `add x0, x0, :lo12:.rodata.psci_args.0`).
3. Kraken's parser produces a `Program` per section, and the instructions
   that Kraken does not have yet (section 4.4) have to be added to its parser
   as well as to `Operation`. This is acceptable; as with `Operation`, they
   get no semantics (executing them yields `Effects.unimplemented`).

This gives a code layer without writing a decoder, and Kraken's parser
already accepts objdump's aliases. The costs:

- `objdump` (and the converter) become part of what has to be trusted: a
  proof about the resulting `Program` is about the file only as far as
  objdump decodes it correctly. With a Lean decoder, the trusted part is a
  Lean function that can be reviewed against `sail-arm` clause by clause.
- Verification needs a cross toolchain at proof time, or the objdump output
  has to be committed next to each file.
- objdump's text format has to be followed exactly, including its quirks,
  and it can change between binutils versions.

Information that verification still needs from the ELF file itself, since
`objdump -d -r` does not print it or prints it only as comments:

- The contents of non-executable sections: initial values of `.data`,
  constants in `.rodata` (e.g. `.rodata.psci_args.0`, which
  `get_arm_std_svc_args` returns the address of), and the sizes of `.bss`
  and other `NOBITS` sections. Code reads and writes them, so they belong to
  the initial memory.
- Relocations in data sections, e.g. `.rela.rodata.psci_args.0`: pointers
  stored in data, such as function pointer tables, which say what an
  indirect branch (`blr`) can reach.
- The symbol table: sizes (where a function or object ends), bindings
  (local, global, weak), undefined symbols (what an object file expects
  from others), and which section each symbol is in.
- Section attributes: flags (writable, executable), alignment, and in
  executables the addresses; and the program headers (`PT_LOAD` segments
  with their permissions and `memsz` vs `filesz`), which say what memory is
  executable, writable or zero-initialized at boot. Kraken's semantics has
  `require_exec_access`, `require_read_access` and `require_write_access`
  effects that this would answer.
- The entry point of an executable.
- The connection between bytes and instructions: if a statement is about
  the binary that is actually loaded (e.g. `bl31.bin`), the instruction
  bytes and their addresses are needed to check that the `Program` matches
  them.

`objdump` and `readelf` can print all of these too (`-s` for contents, `-t`
or `-s` for symbols, `-h`/`-S` and `-l` for sections and segments), but
then the converter parses several text formats instead of one binary format,
which is more work and more fragile than parsing the ELF container directly.

A hybrid is possible: parse the ELF container in Lean (section 3), and use
the objdump route only for decoding instruction words until the Lean decoder
exists. The objdump route then also serves as the oracle for testing the
decoder (section 5.6).

## 5. Round-trip testing

### 5.0 What round trips are still good for

Round trips test a parser against an encoder; they were never a proof about
the code (section 1.1). With instructions coming from objdump (section 4.5):

- There is no Lean decoder, so there is nothing for an instruction round
  trip (section 5.5) to test in that form.
- The ELF container parser is still written in Lean and still in the
  trusted base, since data sections, data relocations and symbols come from
  it. It needs a test, but a comparison with GNU `readelf` (section 5.6,
  last paragraphs) is the better one, since it is independent and catches
  errors that a parser and an encoder make in the same way (section 5.1).
  The byte-exact round trip and the `Layout` it needs (sections 5.2 and 5.3)
  are postponed.
- One round trip becomes more useful than before: checking objdump's output
  against the bytes. With a Lean instruction encoder written from the
  `sail-arm` encodings, `encodeInstr (parseAsm (objdump w)) = w` can be
  checked for each instruction word of a verified function (relocated fields
  as in the object file). If it holds, objdump and the converter drop out of
  the trusted base: the theorem is then about the bytes, and only the Lean
  encoder has to be trusted (or reviewed against `sail-arm`). This is
  translation validation, and it is a later milestone.

An ELF encoder for the container layer is feasible and small: the format is
a fixed-size file header, two tables of fixed-size entries (program headers
and section headers) and blobs of bytes at given offsets. Writing it is
mostly the parser in reverse.

The round trip is about the container layer only. Section contents,
including the instruction words of `.text` sections, are kept as bytes, and
the code layer of section 3 is a view computed from them that the encoder
does not use. In object files these bytes hold the instructions as the
assembler wrote them, with relocated fields still 0 (or the addend); the
relocations are separate entries in `.rela.*` sections. So the ELF round trip
needs no instruction encoder. An instruction encoder would only be needed to
produce new code, e.g. to write out modified object files (section 5.5).

### 5.1 Two possible properties

1. `encode (parse file) = file`: byte equality with the original file.
2. `parse (encode (parse file)) = parse file`: the encoder may lay the file
   out differently, but the parser must read back the same value.

Trade-offs:

- (1) detects information that the parser drops, e.g. a flag bit or a
  symbol's visibility that the datatype has no field for: the encoder
  cannot write back what it was never given. (2) does not, since both sides
  of the equation lose it in the same way.
- (1) forces the datatype to keep layout details that carry no meaning
  (section 5.2); (2) needs none of them, and lets the encoder choose its own
  layout, which is what is wanted when writing new files.
- (2) checks that the encoder keeps all information in the datatype, which
  (1) checks too, but (2) does so also for values that did not come from a
  GNU-built file, e.g. if the layout fields are dropped (section 5.3).
- Neither detects a parser and an encoder that misinterpret a field in the
  same way, e.g. both treat the symbol's `st_info` byte with binding and type
  swapped. Only an independent oracle catches that, e.g. comparing the parsed
  value with the output of `readelf -h -S -s -r` from GNU binutils (open
  source, part of the Arm GNU toolchain installed for section 2).

### 5.2 What byte equality costs in the datatype

Measured on the 115 files of section 2 (with a Python script over the raw
headers):

- The constant fields are the same in all files: `e_ident` is always
  `7f 45 4c 46 02 01 01` followed by zeros, and `e_version`, `e_ehsize`,
  `e_phentsize`, `e_shentsize` and `e_phoff` (64) have their standard values.
  The parser can reject other values and the encoder write the constants, so
  no field is needed.
- All bytes not covered by a header, a table or a section's data (4,913 bytes
  in total, alignment padding) are zero. The parser can check that, so gaps
  need no field either.
- The file offsets of the sections cannot simply be recomputed. Only 31 of
  the 115 files have their sections' data in index order. 99 of the 114
  object files follow the rule "other sections by index, then `.symtab`,
  `.strtab`, the `.rela.*` sections and `.shstrtab`, each aligned, then the
  section headers", the 15 others do not, and `bl31.elf` follows neither.
  Reproducing GNU `as` and `ld` exactly is not worth it, so the datatype
  keeps `sh_offset` for each section and `e_shoff`.
- The string tables cannot be recomputed either. `.shstrtab` shares suffixes
  between names in 83 of the 115 files (e.g. `.text.foo` is found inside
  `.rela.text.foo`), and no file's `.shstrtab` is the plain concatenation of
  the names in section order; `.strtab` is the plain concatenation in 100
  files, and shares suffixes in 15. So the datatype keeps the bytes of the
  string tables, and the name offsets (`sh_name`, `st_name`) of sections and
  symbols.

So the cruft is: `e_shoff`, and for each section `sh_offset` and `sh_name`,
for each symbol `st_name`, plus the raw string tables. Everything else in
the file is information that the datatype needs anyway.

### 5.3 Keeping the cruft apart

The cruft can be kept out of the main datatype:

```lean
/-- Where things are in the file. Only needed to reproduce a file byte for
byte; without it, the encoder chooses a layout. -/
structure Layout where
  shoff : UInt64
  sectionOffsets : Array UInt64       -- `sh_offset`, by section index
  sectionNameOffsets : Array UInt32   -- `sh_name`, by section index
  symbolNameOffsets : Array UInt32    -- `st_name`, by symbol index
  shstrtab : ByteArray
  strtab : ByteArray

structure File where
  -- as in section 3, with names as plain `String`s
  layout : Option Layout
```

The parser always fills in `layout`. Then both properties can be tested:
(1) as is, and (2) with the layout dropped:
`(parse (encode { f with layout := none })).map ({ · with layout := none })
= some { f with layout := none }`.

### 5.4 The test

- The ELF parser, the encoder and the test live in Kraken.
- The test checks the round trip on every object file (`*.o`) and every
  executable (`*.elf`, e.g. `bl31.elf`) that it finds in a given directory,
  recursively.
- Kraken's own test suite runs it on a directory with a few small object
  files committed to Kraken, chosen especially among those that made the test
  fail at some point during development. TF-A is BSD-3-Clause, so they can be
  committed.
- During development, the exact same test is run on the BL31 build directory
  `imx-atf/build/imx93/release` (section 2).

### 5.5 A second round trip for the code layer

The same idea applies to instructions: `encodeInstr (decodeInstr w) = w`
for every word in a `$x` region. This needs an instruction encoder (Kraken
has none; it relies on an external assembler), which is about as much work
as the decoder and can be written from the same `sail-arm` encodings. It
catches decoder bugs that the objdump comparison of section 4.3 would also
catch, but needs no external tool. Expected obstacles:

- Encodings that Kraken's `Operation` does not distinguish, e.g. a field
  that the architecture ignores, or two encodings of the same operation.
  Such words need either an extra field in the decoded item or an exception
  list in the test.
- In object files, the decoded operand of a relocated field is a `ConstExpr`
  with a label, while the word holds 0 or the addend; the encoder has to
  write back the word as it is in the file, not as it will be after linking.

Not planned for now; the ELF round trip does not depend on it.

### 5.6 A third test: compare a pretty-printer with GNU objdump

`prettyPrint (parse file) = objdump file`: a Lean pretty-printer that
reproduces the text of GNU `objdump` (from the Arm GNU Toolchain, open
source). Unlike the round trips, this compares with an independent
implementation, so it catches a parser or decoder that misinterprets
something, including errors that an encoder with the mirror-image error
would hide (section 5.1). It is the only one of the three tests that checks
the decoder.

`objdump -d -r` on `bl31_main.o` prints e.g.:

```
Disassembly of section .text.get_arm_std_svc_args:

0000000000000000 <get_arm_std_svc_args>:
   0:	90000000 	adrp	x0, 0 <get_arm_std_svc_args>
			0: R_AARCH64_ADR_PREL_PG_HI21	.rodata.psci_args.0
   4:	91000000 	add	x0, x0, #0x0
			4: R_AARCH64_ADD_ABS_LO12_NC	.rodata.psci_args.0
   8:	d65f03c0 	ret
```

What the printer would have to reproduce, and what that costs:

- Aliases: objdump prints `mov x29, sp` for `add x29, sp, #0`, `cmp` for
  `subs xzr, ...`, `lsl` for `ubfm`, `cset` for `csinc`, and so on, following
  the "preferred disassembly" conditions of the Arm architecture. Kraken's
  printer prints the base instruction. The objdump-compatible printer needs
  these conditions for every alias. `sail-arm` does not contain them, since
  they are not part of the ASL pseudocode, so they would have to come from
  Arm's documentation or from binutils.
- Operands as objdump shows them: hexadecimal immediates (`#0x0`), branch
  targets as the unrelocated address followed by the nearest symbol
  (`0 <get_arm_std_svc_args>`), and comments such as `// #42`. In object
  files, the relocated operands are printed with their unrelocated values,
  so the printer must print the word's field, not Kraken's `ConstExpr`; the
  relocation appears on a separate line.
- Words that the decoder does not support yet: objdump disassembles them
  (e.g. SIMD), the printer cannot, so the test needs an exception, e.g.
  skipping lines whose word is `undecoded`.
- The exact text depends on the binutils version (here 2.44 in Arm GNU
  Toolchain 14.3.Rel1), so the expected output has to be produced with a
  fixed version.

A cheaper variant compares per instruction instead of per text: Kraken's
assembly parser reads objdump's text of each instruction, and the result
must equal the decoded `Operation` (section 4.3). Aliases and number
formats then do not matter, since Kraken's parser already accepts them
(`mov`, `cmp`, `lsl`, `cset`, `tst`, `ubfx`, `mul`, `neg`, ...); only
objdump's additions have to be removed first (the `<symbol>` after a branch
target, `//` comments), and branch targets have to be compared as offsets.
But it does not test the container layer's output (section and symbol names,
relocation lines). For the container layer, `readelf -h -S -s -r -W` is the
better oracle than objdump: it prints all header fields, sections, symbols
and relocations, and a printer for those is simple.

For Kraken's test suite, the expected `objdump`/`readelf` output of the
committed object files is committed next to them, so that the test does not
need the cross toolchain. During development, the same test runs the tools
on the BL31 build directory.

## 6. Decisions so far

- Goal: proofs about functions in AArch64 object files, composable under
  linking later. Success: a few interesting BL31 functions verified
  (section 1.1). The first milestone takes platform-independent functions,
  mostly from TF-A's `libc` (section 1.2.1); the TRDC functions come later,
  once a TRDC semantics from Sockeye's Lean backend can be combined with
  Kraken's (section 1.2.2).
- Proofs use instruction beacons, `instr "<objdump text>" at sym + off`,
  ported from ToySys to Kraken (section 1.3).
- Instructions come from `objdump -d -r` through Kraken's assembly parser
  (section 4.5); the Lean decoder is postponed. A Lean instruction encoder
  that checks objdump's output against the bytes is a later milestone
  (section 5.0).
- The container layer is architecture-independent (ELF64 little-endian) and
  kept in a separate directory or file; the code layer is instantiated only
  for AArch64 for now (section 3).
- Two layers: a container layer that mirrors the file, and a code layer that
  decodes executable sections into Kraken instructions.
- Section contents stay bytes in the container layer; decoded instructions
  are a view computed from them (section 3.1).
- Use the `$x`/`$d` mapping symbols to separate code from data. Files
  without them (stripped executables) are not a target, but can be handled
  by treating executable sections as code (section 2.1).
- Express relocated operands with Kraken's `ConstExpr` (`label`, `pg_hi21`,
  `lo12`, `add`).
- Words the decoder does not support are kept as `undecoded`, not rejected.
- If a decoder is written, it is agent-written Lean with encodings from
  `sail-arm` (section 4.3); postponed (section 1.5).
- Instructions missing from Kraken are added to Kraken's `Operation` without
  semantics; executing them yields `Effects.unimplemented` (section 4.4).
  Adding them to Kraken's assembly parser (and printer) is fine too, still
  without semantics (section 4.5).
- Postponed (section 5.0): an ELF encoder and a Kraken test of the round
  trip on all object files and executables in a directory, recursively;
  Kraken's test suite would run it on a few committed object files, and
  during development on the BL31 build directory (section 5.4). Postponed
  with it: the layout details needed for byte equality, kept in a separate
  `Layout` (section 5.3); the constant fields and the zero padding are
  checked by the parser instead of stored (section 5.2).

## 7. Next steps

1. Add the missing instructions to Kraken's `Operation` and parser, without
   semantics (section 4.4), so that the converter accepts every object file.
2. Write the objdump-to-Kraken converter, starting with `libc/strlen.o`
   (section 4.5).
3. Port the `instr _ at _` beacon tactic from ToySys to Kraken (section 1.3).
4. Verify `strlen`, then `memcpy`, `memcmp` and `memset` (section 1.2.1).
5. Calls: verify `memmove`, whose tail call to `memcpy` uses `memcpy`'s
   spec, then `strlcat`.
6. The ELF container parser for object files, when a target needs data
   sections or the symbol table beyond what objdump prints (first:
   `vsnprintf`'s jump table in `.rodata`).
