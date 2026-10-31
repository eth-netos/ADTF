# Verifying AArch64 object files in Lean: plan and design decisions

This document records the plan and the design decisions for verifying the
code in AArch64 object files with Kraken (the `kraken` submodule). It is
extended as the design develops. It started as the design of an ELF parser
(sections 2 to 5); section 1 describes the goal that replaced that, and
section 1.5 which parts of the parser design are still needed.

Headings say whether a section is about the first milestone or about later
work; the next section summarizes both.

## Scope at a glance

First milestone:

- Targets: the functions of TF-A's C library that make no calls, refer to
  no other section and contain no loop (section 1.2.1): `putchar`,
  `setjmp`, `longjmp`, 22 instructions without branches. Section 1.6 has
  sample specs. Proofs use instruction beacons that take objdump's text as
  a string (section 1.3).
- Input: the objdump listings of these functions, committed verbatim inside
  Lean files, turned into Kraken `Program`s by an elaborator; a script
  regenerates the listings from the pinned BL31 build and diffs them
  (section 4.7). No ELF parser (section 4.6).
- Work in Kraken: the elaborator; the beacon tactic; spec helpers
  (section 1.6).
- Not needed: the instructions that Kraken lacks (none of the targets
  contains one, section 4.4), symbols outside the function (section 4.6),
  relocations, branch targets (section 4.8), loop rules.
- Trusted base: objdump, the elaborator's conversion of the listing,
  Kraken's parser and Kraken's semantics. The layout of the object file
  (4-byte instructions, section 4.9) is a hypothesis of each theorem.

Later, roughly in this order:

- The 20 other C library functions without calls, which loop (section
  1.2.1): a loop rule, objdump's branch targets in Kraken's parser
  (section 4.8), conditional branches in the beacon tactic.
- Other platform-independent functions without calls (section 1.2.2),
  among them some that need symbols outside the function, such as `atexit`
  (section 4.6).
- Calls, inside and between object files; functions that read constant
  tables in `.rodata` (section 1.2.3).
- The instructions that Kraken lacks, added without semantics (section
  4.4), and a test that every instruction of all 114 object files parses
  (section 5.2).
- An ELF container parser for object files (sections 3 and 3.1), tested
  against `readelf` (section 5.3), once targets need the contents of data
  sections or relocations in them (section 4.5).
- Composition under linking, and the linked executable (section 1.4).
- MMIO with a device model, the TRDC functions with a TRDC semantics from
  Sockeye's Lean backend (section 1.2.4), and other platform-dependent
  functions (section 1.2.5).
- Semantics for the instructions added without semantics (section 4.4).
- A Lean decoder written from `sail-arm`'s encodings, to take objdump out of
  the trusted base (sections 4.1 to 4.3).

Not planned: ELF or instruction encoders, round-trip tests.

Open points are collected in section 8.

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

Tests of the converter and parsers (section 5) are not the goal: they say
that a file was read correctly, not that anything about its code was
proven.

Success is now: Lean theorems, checked by Lean, about a few interesting
functions of BL31, stated about the code as it is in the object files that
the BL31 build produced, and proven with instruction beacons (section 1.3).
For the first milestone, these are functions from TF-A's C library that
make no calls and contain no loops (section 1.2.1); the C library's
functions with loops come next, then other platform-independent functions
without calls (section 1.2.2), then calls (section 1.2.3). The TRDC
functions (the Trusted Resource Domain Controller, which the i.MX 93 uses to
restrict which bus masters may access which memory and peripherals) are the
eventual goal, but need a TRDC semantics combined with Kraken's ISA
semantics, planned via Sockeye's Lean backend (section 1.2.4).

Each theorem says what the function does to registers and memory, under
which preconditions, and that it returns to its caller.
What the trusted base of such a theorem is (objdump, the converter of
section 4.5, Kraken's semantics) is stated next to it.

### 1.2 Candidate functions

Each function is in its own section in its object file
(`-ffunction-sections`). Sizes are from the object files. The features that
a function exercises are what makes it interesting beyond its size.

#### 1.2.1 First milestone: TF-A's C library, functions without calls or loops

Verifying the TRDC functions (section 1.2.4) needs a semantics of the TRDC,
combined with Kraken's ISA semantics. That is planned via Sockeye's Lean
backend, but too big for a first milestone. Calls and loops are left for
later too (section 1.2.3, and below). The first milestone takes the
functions of TF-A's C library (`lib/libc`, built into
`build/imx93/release/libc/*.o`; not all of it is linked into `bl31.elf`,
but all of it is in object files) that

- make no calls: no `bl`, `blr`, `br`, and no `b` to another function (a
  tail call), i.e. no `CALL26` or `JUMP26` relocation;
- refer to no symbol outside their own section, i.e. have no relocation at
  all (section 4.6);
- contain no loop, i.e. no branch to the same or a lower offset.

The C library has 40 function symbols in 31 object files. 16 make calls
(`abort`, `__assert`, `exit`, `memcpy_s`, `memmove`, `printf`, `puts`,
`qsort`, `local_qsort`, `med3`, `snprintf`, `vsnprintf`, `vprintf`,
`unsigned_num_print.part.0` in `printf.o`, `strcpy_secure`, `strlcat`), and
`atexit` refers to the global `exitfun` (section 1.2.2). The remaining 23
contain no instruction that Kraken lacks (section 4.4), access no device or
system registers, and have no relocations. Only 3 of them have no loop, and
these 3 have no branch at all, apart from the final `ret`:

- `putchar` (1 instruction): `ret`; the C library's weak default, which
  returns its argument (`#pragma weak putchar`). A test of the whole path
  from objdump to a theorem.
- `setjmp` (10) and `longjmp` (11), assembly (`lib/libc/aarch64/setjmp.S`,
  both in `libc/setjmp.o`): save and restore the callee-saved registers,
  `x30` and `sp`, with `stp` and `ldp`. `longjmp` does not return to its
  caller but to where `setjmp` was called, so its spec is about control
  flow.

So the first milestone is 22 instructions in two object files, enough to
build and test the whole path: listings, elaborator, script, beacons, spec
helpers, memory reasoning for a 112-byte buffer.

Later, next: the other 20, which loop. Sizes are in instructions:

- `strlen` (7): the simplest loop; precondition: a NUL-terminated string.
- Read-only searches: `strnlen` (9), `strnlen_secure` (10), `memchr` (11),
  `strchr` (9), `strrchr` (10, `csel`), `memrchr` (14).
- Comparisons of two buffers: `memcmp` (13), `strcmp` (11), `strncmp` (14).
- `memcpy` (8): byte copy loop; two disjoint buffers.
- `memset` (26): aligns, then stores whole words whose value is the byte
  replicated by a `mul`, then the tail; bit-level reasoning.
- `strlcpy` (15), `strtok_r` (29): writes, and a pointer as result
  (`strtok_r` keeps its position in memory between calls).
- `swapfunc` (9, static, in `qsort.o`): swaps two buffers.
- `strtoul` (99), `strtol` (101), `strtoull` (104), `strtoll` (101): digit
  parsing with overflow detection (`udiv`, `madd`, `umulh`); the spec
  compares with a reference function in Lean.
- `unsigned_num_print` (76, static, in `snprintf.o`): number to digits with
  `udiv` and `msub`, into a buffer.

They need a loop rule, branch targets (section 4.8) and conditional
branches in the beacon tactic. Suggested order, each adding one thing:
`strlen` (a loop that ends on data), `memcpy` (writes, two buffers),
`memcmp` (a result computed from two buffers), `memset` (alignment, words,
bit-level reasoning), `strtoul` (arithmetic with overflow, a reference
function).

#### 1.2.2 Later: other platform-independent functions without calls

These were found by classifying every function in the 114 object files by
the mnemonics and relocations in `objdump -d -r`: of 698 function symbols
(assembly files' local labels included), 366 make calls, 87 contain an
instruction that Kraken lacks, 7 branch through a register, and 238 are
leaves, most of them in platform code or drivers that access device
registers (GIC, TRDC, DDR, LPUART). Sizes are in instructions. Most of
these refer to global variables or linker symbols, so they need symbols
outside the function (section 4.6).

- `atexit` (8, `libc/exit.o`): stores a function pointer in the global
  `exitfun` (`.bss.exitfun`).
- `__popcountsi2` (12), `__popcountdi2` (14), from `lib/compiler-rt`:
  population count with the usual bit tricks; the spec is a one-liner, the
  proof is bit-vector reasoning.
- `memcpy16` (12, assembly, `lib/aarch64/misc_helpers.S`): copies 16 bytes
  at a time with post-indexed `ldp`/`stp`, then bytes.
- `fixup_gdt_reloc` (38, assembly, same file): applies the dynamic
  relocations of a position-independent image to its global offset table;
  a loop over memory that itself does relocation processing.
- `per_cpu_base` (7, assembly, `lib/per_cpu`): address arithmetic on the
  linker symbols `__PER_CPU_START__` and `__PER_CPU_UNIT_END__`.
- PSCI (`lib/psci`): `psci_version` (2), `psci_find_target_suspend_lvl`
  (13), `psci_find_max_off_lvl` (19), `psci_set_req_local_pwr_state` (13),
  `psci_init_req_local_pwr_states` (15), `psci_register_spd_pm_hook` (15),
  `psci_features` (25): small functions on PSCI's power state arrays and
  its table of supported functions.
- Translation tables (`lib/xlat_tables_v2`): `find_xlat_table_entry` (37,
  static): walks translation tables in memory, loads only;
  `tcr_physical_addr_size_bits` (19), `xlat_arch_get_pas` (5),
  `xlat_arch_regime_get_xn_desc` (5): pure bit computations.
- Generic TF-A code (`common/`, `bl31/`, `plat/common/`):
  `page_align` (7), `tf_log_set_max_level` (5), `get_bl_params_node_index`
  (20), `get_bl_load_info_from_mem_params_desc` (24); `get_arm_std_svc_args`
  (3) and `get_version` (3) return the address of data in `.rodata`, not
  its contents; `get_scr_el3_from_routing_model` (11): lookup in a table in
  `.bss`; `bl31_set_next_image_type` (3), `bl31_register_bl32_init` (3):
  store into globals; `plat_ic_is_sgi` (3), `plat_ic_is_ppi` (4),
  `plat_ic_is_spi` (4): range checks on interrupt numbers;
  `plat_get_target_pwr_state` (10).
- The generic console framework (`drivers/console/multi_console.c`):
  `console_is_registered` (11), `console_unregister` (15),
  `console_switch_state` (3), `console_set_scope` (6), on its linked list of
  consoles; `console_unregister` removes a node, a classic separation logic
  proof.
- Pure functions from the i.MX 93 platform code: `plat_core_pos_by_mpidr`
  (7, `csinv`) and `imx_validate_ns_entrypoint` (5, a security check:
  rejects non-secure entry points below `PLAT_NS_IMAGE_OFFSET`,
  `0x80200000`).

#### 1.2.3 Later: platform-independent functions with calls or constant tables

Calls between object files (relocations `CALL26` and `JUMP26`), the first
step towards composition (section 1.4):

- `memmove` (13 instructions): copies backwards itself, and otherwise
  tail-calls `memcpy` (`b memcpy`, a `JUMP26` relocation).
- `memcpy_s` calls `memcpy`; `strlcat` calls `strlen`; `strcpy_secure`
  calls `strnlen_secure`.
- `qsort` tail-calls `local_qsort` (static), which is recursive and calls
  the comparison function through a function pointer (`blr`), so its spec
  takes the comparison function's spec as a parameter.
- `vsnprintf`: a `switch` compiled to a jump table (`adr`, `br`), and
  variadic arguments (`va_list`).
- `mmap_add_region_ctx` (`xlat_tables_core.o`): inserts a region into the
  sorted memory map, rejecting overlaps; calls `memmove` and `memcpy`. A
  security-relevant invariant (the map stays sorted and without overlaps).
- `xlat_tables_map_region`: recursive; calls `xlat_desc`.

Some of these call platform code on error paths only (`tf_log`,
`console_flush`, `el3_panic`, `plat_panic_handler`). Their specs enter as
hypotheses about undefined symbols, e.g. "does not return", or the
precondition excludes the error; both fit the composition plan of
section 1.4.

Two leaves without calls are left out of the first milestone because a
useful spec needs the initial contents of `.rodata`, which objdump's listing
does not give (section 4.6): `get_el_str` (8) and `plat_log_get_prefix`
(12) load a string pointer from a table in `.rodata` (`.rodata.CSWTCH.3`,
`.rodata.plat_prefix_str`), whose entries are `R_AARCH64_ABS64` relocations
into `.rodata.str1.1`. "Returns the string `EL3`" needs both.

#### 1.2.4 Later: TRDC functions

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

#### 1.2.5 Later: other platform-dependent functions

These exercise further features, but need device registers, system
registers, or instructions without semantics, or call platform code on
their main path:

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

### 1.3 Proof style: instruction beacons (first milestone)

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

In ToySys, `i` is a Lean term (`.cmp .X0 (.reg .X1)`). In the first
milestone, `i` is a string: the instruction as objdump prints it, parsed
with Kraken's existing assembly parser, including objdump's branch-target
form `14 <strlen+0x14>` (section 4.8). So a beacon can be pasted from the
committed objdump listing (section 4.7).

Kraken has no such tactic. Its `kstep` steps through straight-line code
without naming the instructions. Porting `instr` means:

- parsing the string with Kraken's assembly parser at elaboration time and
  comparing the result with the fetched `Instr`;
- expressing the address relative to the function's symbol, since an
  object file has no addresses (section 1.4); with the layout hypothesis
  of section 4.9, `strlen + 0x14` is the start address plus 0x14;
- the special cases that ToySys has: conditional branches give two goals,
  calls continue with the callee's spec.

#### 1.3.1 A minimal core for beacons (first milestone; proposal)

Kraken's machine model around `Operation.interp` is more general than
beacons need:

- a program is a list of directives (`instr`, `label`, `byteArray`), placed
  by a `Layout` that gives each directive an arbitrary size;
- `Executable.withAddresses`, `directivesAtAddress` and
  `directivesFromAddress` find the directives at the program counter by
  walking the list;
- `Executable.straightline` runs all directives from the program counter
  until a jump, `Executable.step` (used by `step1`) those at the program
  counter, i.e. labels and one instruction;
- `Executable.labels` takes symbol addresses from the program's own labels
  and gives all others the address -1 (section 4.6);
- `kprologue` and the `kstep` simproc are built around
  `Executable.straightline` and `Directives.interp`.

ToySys has none of this: a program is a map from addresses to
instructions, `Loaded prog f code` says that the list `code` is at address
`f` with 4 bytes per instruction, and `Core.step` fetches one instruction
and runs it. A beacon tactic for Kraken can be built the same way, using
from Kraken only what describes one instruction:

```lean
/-- The code in memory: the instruction at each address, if any. -/
abbrev Code := Int64 → Option Instr

/-- The byte offset of directive `k` of `prog` in an object file: the
sizes of the directives before it (`Directive.fakeSize`: 4 per
instruction, 0 per label). -/
def Program.offset (prog : Program) (k : Nat) : Nat :=
  ((prog.take k).map Directive.fakeSize).sum

/-- The instruction at byte offset `n` of `prog`, if any. -/
def Program.instrAt (prog : Program) (n : Nat) : Option Instr :=
  (prog.zipIdx.findSome? fun (d, k) => match d with
    | .instr i => if prog.offset k = n then some i else none
    | _ => none)

/-- `prog` is in `code` at `f`: each instruction at `f` plus its offset,
and each label at the address that the symbol map `syms` gives it. -/
def Loaded (syms : Label → Int64) (code : Code) (f : Int64)
    (prog : Program) : Prop :=
  f % 4 = 0 ∧ ∀ k d, prog[k]? = some d →
    match d with
    | .instr i => code (f + .ofNat (prog.offset k)) = some i
    | .label l => syms l = f + .ofNat (prog.offset k)
    | .byteArray _ => True

/-- Fetches and runs the instruction at the program counter. Symbol
addresses come from the `Labels` instance. -/
def Code.step [Labels] (code : Code) (s : MachineState) : Effects :=
  match code s.pc with
  | some i => i.interp s.data ⟨s.pc, s.pc + 4⟩
      (fun d => .done ⟨d, s.pc + 4⟩) (fun a d => .done ⟨d, a⟩)
  | none => .unimplemented "no instruction at the program counter"

def Code.stepWp [Labels] (code : Code) (s : MachineState)
    (post : MachineState → Prop) : Prop :=
  (code.step s).All post
```

The rest is ToySys's, translated: a fetch lemma (from `Loaded syms code f prog`
and `prog.instrAt n = some i`, proved by `rfl` for a concrete `prog`, conclude
`code (f + n) = some i`), `step_of_fetch` and `wp_of_pc`, and the `instr`
tactic, which parses its string with Kraken's parser, checks the address with
`bv_decide` and the instruction with `rfl`, and unfolds `Instr.interp` and the
declarations marked `@[kstep]`, splitting conditional branches into two goals.
About 150 lines, judging by ToySys.

Kept from Kraken: `Instr`, `Operation` and `Operation.interp` with all its
helpers, `ConstExpr` and `evalBranchTarget`, `MachineState`, `Effects`
and `Effects.All`, `Mem` and its separation logic, `Eventually`,
`step_cps` and `eventually_trans`, and the parser. Not used: `Layout`,
`Executable`, `Directives.interp`, `Executable.step` and `straightline`,
`Executable.labels`, `kprologue`.

This would not end up almost the same as Kraken's code. The new part is ToySys's
model, not a copy of Kraken's: an address map instead of a list of sized
directives, one instruction per step instead of straight-line runs, labels as
facts about a symbol map instead of a source of addresses. What overlaps is
`Code.step`, which is the one-directive case of `Directives.interp` (a few
lines). In exchange:

- The layout hypothesis of section 4.9 becomes `Loaded`, which states the
  4-byte spacing directly; `ObjLayout` (section 1.6) is not needed.
- Symbol addresses come from a `Labels` instance built from a symbol map
  (ToySys's `Symbols`), so a symbol outside the function gets a parameter
  as its address instead of -1 (section 4.6), and a branch target
  `strlen+0x14` is `syms "strlen" + 0x14` with
  `Loaded syms code (syms "strlen") strlen_o`.
- Proofs about several functions compose as in ToySys's `swap_swap_ok`:
  one `Loaded` hypothesis per function about the same `code`
  (section 1.4). Kraken's `NOTES.md` names composition as the weak point
  of its layout-based model.
- The program stays Kraken's `Program` (section 1.3.2).

What is lost: theorems are about `Code.step`, not about Kraken's
`Executable.step`, so Kraken's existing tools that work on `Executable`
(`kprologue`, `kstep`'s straight-line unrolling, `Executable.eval` for
testing) do not apply. If needed, a lemma relating the two can be proved
later: for a program whose only label is at the start and with
`Program.fakeLayout`-style sizes, `Executable.step` at an instruction's
address does what `Code.step` does. And whether `simp only` with the
`@[kstep]` declarations reduces `Operation.interp` fast enough is open;
Kraken's `kdeltaBetaOnly` simproc exists for this and could be reused,
since only its `Directives.interp` case is tied to straight-line code.

#### 1.3.2 Kraken's `Program` in the beacon core

The listing files and `objdumpAArch64` keep Kraken's type
`Program := List Directive`, as Kraken's parser produces it; the core of
section 1.3.1 reads it through `Loaded`:

- Instructions are at `f` plus `Program.offset`, which uses Kraken's
  `Directive.fakeSize`, so labels take no room, exactly as in the object
  file (section 4.9). The fetch lemma goes through `Program.instrAt`, the
  counterpart of ToySys's `code[(a - f) / 4]?`; for a program without
  labels after the start both are the same.
- Labels are not a source of addresses, as in `Executable.labels`, but
  facts about the symbol map: `Loaded` says that each label of the program
  is at its address in `syms`. The `Labels` instance for `Code.step` is
  `syms`, so the function's own symbol (`longjmp`), branch targets
  (`strlen+0x14`, later) and symbols outside the function (later) are all
  resolved the same way, and for the program's own labels consistently
  with where the code is.
- Data in code (`byteArray`, none in the targets) is skipped by `Loaded`
  but counted by `Program.offset`, so execution that reaches it gets
  stuck in the proof, as in Kraken.

So nothing has to convert between a `Program` and a list of instructions,
the same value can still be run with Kraken's `Program.fakeLayout` and
`Executable.eval` for testing, and a lemma relating `Code.step` to
`Executable.step` (if ever needed) is about the same `Program`. The cost is
`Program.offset` and `Program.instrAt` instead of plain list indexing, a
few lines and a slightly bigger fetch lemma. Section 1.3.3 compares this
with a plain list of instructions.

#### 1.3.3 Alternative: a list of instructions, as in ToySys

Staying as close as possible to ToySys means: `objdumpAArch64` returns a
`List Instr` (ToySys's `code`), checking and dropping the function's label,
and `Loaded`, the fetch lemma (`code[((a - f) / 4).toNat]? = some i`),
`step_of_fetch`, `wp_of_pc` and `instr` are ToySys's, with ToySys's
`Instr`, `State` and `Effects` replaced by Kraken's. The only differences
left are the ones Kraken's semantics forces: the program counter is an
`Int64`, not a `BitVec 64`, and the effects of an instruction are Kraken's
`Effects` with `Effects.All` instead of ToySys's `Effects.wp` on a
platform. These are the same for section 1.3.2.

For it:

- `Loaded` and the fetch lemma are ToySys's; the proof for `BitVec 64`
  should carry over to `Int64`. The address arithmetic is `(a - f) / 4`,
  with no sum of directive sizes.
- Proofs and specs read like ToySys's (`Loaded prog (syms "max3")
  max3_code` there, `Loaded code (syms "longjmp") longjmp_o` here).
- Less to explain and to trust: no `Program.offset`, no `Program.instrAt`,
  no statement about labels.
- For the first milestone (one label per function, at its start, no data)
  nothing is lost.

Against it:

- Assembly functions can have local symbols inside them, e.g.
  `flush_dcache_range` in `bl31/cache_helpers.o` has `<loop_civac>:` at
  0x20 and `<exit_loop_civac>:` at 0x34, and objdump prints its branches as
  `b.cc 20 <loop_civac>`. A `List Instr` has no place for them. The
  elaborator can still rewrite such a target to `flush_dcache_range +
  0x20` (it sees the label's offset in the listing), but then a beacon
  copied from the listing contains `<loop_civac>`, and the beacon tactic
  has to do the same rewriting from the number `20` and the function
  symbol of its `at` address. With `Program`, `Loaded` relates
  `loop_civac` to `syms` and nothing needs rewriting.
- Data in code (`.word` in assembly, `byteArray`) cannot be represented;
  such functions would be rejected (none so far).
- Running a listing with Kraken's `Program.fakeLayout` and
  `Executable.eval`, or relating `Code.step` to `Executable.step`, needs
  `instrs.map .instr` first. A one-liner, but a conversion.
- Moving to `Program` later changes the type of every `*_o` definition and
  `Loaded`; the proofs themselves should not change, since the `instr`
  tactic hides the fetch.

Recommendation: `List Instr` for the first milestone, since its three
functions have no internal labels, no data and no branches, and ToySys's
proofs can be reused unchanged. Switch to `Program` (section 1.3.2) when
the first assembly function with local symbols is verified.

### 1.4 Composability under linking (later)

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
  executables (section 3), and objdump's view of the relocated fields.
- Kraken's `NOTES.md` discusses why its layout-based semantics makes
  composition of programs hard, and plans to make the semantics depend only
  on the addresses of the current and the next instruction, which would help.

### 1.5 What of this design is needed when

Needed for the first milestone, and not in Kraken yet:

- The path from objdump's output into Lean (section 4.7): committed
  objdump listings, read by an elaborator that turns them into a Kraken
  `Program`, and a script that regenerates and diffs them.
- The layout hypothesis (section 4.9) and the spec conventions of
  section 1.6 (`Returns`, callee-saved registers, a buffer predicate).
- Instruction beacons taking a string (section 1.3).

Needed for the first milestone, and already in Kraken (`main` at
`c9aa45e`):

- The assembly parser, accepting objdump's aliases (`mov`, `cmp`, `lsl`,
  `cset`, `tst`, `ubfx`, ...), and `parseAArch64("...")` to write programs
  in Lean files, and `parseFileAArch64("path")`, which reads and parses a
  file at elaboration time. All mnemonics that the first-milestone
  functions use occur in the parser's source (`cinc`, `ccmn`, `umulh`,
  `ldurb`, ...), but whether objdump's exact operand syntax parses is only
  known once the listings are fed to it.
- `ConstExpr` with `label`, `add`, `pg_hi21` and `lo12`, and the `Labels`
  class for symbol addresses, which is what relocations need (later; the
  first-milestone functions have no relocations, section 4.6).
- `Directive.fakeSize` (4 bytes per instruction, 0 per label), which is
  exactly the layout hypothesis of section 4.9.
- `Effects.unimplemented`, whose weakest precondition is `False`.
- Symbolic execution (`kstep`, `kprologue`), separation logic for memory
  (`=⋆`, `ecancel`, `load_sep`, `store_sep`), and `Eventually` with
  `eventually_trans` and a loop rule (`reg_dec_loop`).
- Kraken's README says it verifies code "disassembled from compiler output
  (`.o` files)", but `main` contains no tool for that; the path of
  section 4.7 is new.

Later:

- For the C library functions with loops: Kraken's parser accepting
  objdump's branch-target form `14 <strlen+0x14>` (section 4.8), a loop
  rule, conditional branches in the beacon tactic, string predicates.
- Adding the instructions that Kraken lacks to `Operation` and the parser
  (section 4.4); no first-milestone function contains one.
- External symbols: Kraken's `Executable.step` resolves labels only from
  the program itself and gives every other label the address -1
  (section 4.6); needed for the first function that refers to another
  section, e.g. `atexit`.
- Calls: specs of callees as hypotheses, the link register, callee-saved
  registers and the stack frame. Kraken's AArch64 examples on `main` have
  no calls; the `vcgen` branch (Sebastian Graf's, not merged) has
  frame-based specs and a call example for x86-64 only.
- An ELF container parser for object files (section 3), because later
  proofs need what `objdump -d -r` does not give (section 4.5): the contents
  of data sections, relocations in data sections, and the symbol table. The
  first targets that need it are `get_el_str` and `plat_log_get_prefix`
  (constant tables, section 1.2.3) and `vsnprintf` (its jump table in
  `.rodata.vsnprintf`). The TRDC functions need it for `fuse_data`,
  `trdc_mgr_blks` and the configuration tables (with `R_AARCH64_ABS64`
  relocations in `.data.trdc_cfg_info`). Executables (`bl31.elf`) and
  segments can wait until the composition step.
- A way to state the initial contents of data sections in a precondition,
  from the parsed ELF file.
- MMIO with a device model, for the TRDC functions. Every TRDC function
  accesses device registers. Kraken's AArch64 semantics has `nonmem_load`
  and `nonmem_store` effects, but its `Effects.All` maps them to `False`, so
  no MMIO access can be verified yet. Kraken's x86-64 side has an example
  with a device state (`Kraken/X64/Examples/IncrementMMIO.lean`), and ToySys
  has a `Platform` with `read` and `write` relations; one of these designs
  has to come to AArch64, with the device semantics generated by Sockeye's
  Lean backend.
- The Lean instruction decoder (sections 4.1 to 4.3), to take objdump out of
  the trusted base; the `sail-arm` encodings stay the reference for it.

Background only: the mapping symbols (section 2.1) explain why objdump can
tell code from data; the converter itself does not need them.

Removed:

- ELF and instruction encoders, round-trip tests, and the layout details
  that byte-exact round trips need: producing files is not a goal, and
  comparing with `readelf` tests the parser better (section 5.3).
- A pretty-printer compared with objdump, since objdump is now the source of
  the instructions, not an oracle.
- The code-layer datatype `CodeItem`/`CodeSection` (section 3): replaced by
  one Kraken `Program` per section, as Kraken's parser produces it, plus the
  symbols of that section as labels.

### 1.6 Sample specs (first milestone)

Sketches, not yet checked by Lean. They use Kraken's vocabulary (`Layout`,
`straightlineStep`, `Eventually`, `MachineData` with `regs.X0` ...
`regs.SP` as `UInt64`, `dmem` with `=⋆` and `List.At`) and a few helpers
that are new. Each `*_o` program comes from the committed objdump listing
(section 4.7). With the beacon core of section 1.3.1, `ObjLayout` becomes
`Loaded syms code (syms "strlen") strlen_o`, and `Returns` uses
`Code.stepWp` instead of `straightlineStep`; the specs stay the same
otherwise.

The first milestone needs the specs of `putchar`, `setjmp` and `longjmp`,
and of the helpers `ObjLayout`, `CalleeSaved`, `Returns` and `Bytes`. The
others (`strlen` to `strtoul`, and `CString`) are for the functions with
loops, later; `strlen_o` shows what a listing with branches looks like.

```lean
/-- The code of `strlen` in `libc/strlen.o`, from the committed listing. -/
def strlen_o : Program := objdumpAArch64("
0000000000000000 <strlen>:
   0:	aa0003e1 	mov	x1, x0
   4:	39400022 	ldrb	w2, [x1]
   8:	35000062 	cbnz	w2, 14 <strlen+0x14>
   c:	cb000020 	sub	x0, x1, x0
  10:	d65f03c0 	ret
  14:	91000421 	add	x1, x1, #0x1
  18:	17fffffb 	b	4 <strlen+0x4>
")

/-- The layout of an object file's code (section 4.9): each instruction
takes 4 bytes, each label 0 bytes, and the code starts at a 4-byte-aligned
address. -/
def ObjLayout (prog : Program) (layout : Layout) : Prop :=
  (∀ i (h : i < prog.length), layout.size i = prog[i].fakeSize) ∧
  layout.start % 4 = 0

/-- The registers that a function must preserve (AAPCS64): `x19` to `x29`
and `sp`. -/
def CalleeSaved (s₀ s : MachineData) : Prop :=
  s.regs.X19 = s₀.regs.X19 ∧ s.regs.X20 = s₀.regs.X20 ∧ ... ∧
  s.regs.X29 = s₀.regs.X29 ∧ s.regs.SP = s₀.regs.SP

/-- Run from the start of `prog` in state `s₀`, the function eventually
returns to the address in `x30`, with the callee-saved registers
preserved, in a state that satisfies `post`. -/
def Returns [layout : Layout] (prog : Program) (s₀ : MachineData)
    (post : MachineData → Prop) : Prop :=
  Eventually (straightlineStep (layout prog))
    (fun s => s.pc = s₀.regs.X30.toInt64 ∧ CalleeSaved s₀ s.data ∧
      post s.data)
    ⟨s₀, layout.start⟩

/-- The bytes `bs` at address `a`, without wrapping around the end of the
address space. -/
def Bytes (bs : List UInt8) (a : UInt64) : DataMem → Prop :=
  fun m => a.toNat + bs.length ≤ 2 ^ 64 ∧ m = bs.At a.toBitVec

/-- A C string: the bytes `bs`, none of them NUL, then a NUL byte. -/
def CString (bs : List UInt8) (a : UInt64) : DataMem → Prop :=
  fun m => 0 ∉ bs ∧ Bytes (bs ++ [0]) a m
```

`putchar` returns its argument and changes nothing else:

```lean
theorem putchar_spec [layout : Layout] (h : ObjLayout putchar_o layout)
    (s₀ : MachineData) :
    Returns putchar_o s₀ (fun s =>
      s.regs.X0 = s₀.regs.X0 ∧ s.dmem = s₀.dmem)
```

`strlen` returns the length and does not write memory:

```lean
theorem strlen_spec [layout : Layout] (h : ObjLayout strlen_o layout)
    (s₀ : MachineData) (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ CString bs s₀.regs.X0 ⋆ R) :
    Returns strlen_o s₀ (fun s =>
      s.regs.X0.toNat = bs.length ∧ s.dmem = s₀.dmem)
```

`memcpy` copies `n` bytes between two disjoint buffers (the separating
conjunction makes them disjoint, as C requires) and returns `dst`:

```lean
theorem memcpy_spec [layout : Layout] (h : ObjLayout memcpy_o layout)
    (s₀ : MachineData) (src old : List UInt8) (R : DataMem → Prop)
    (h_n : s₀.regs.X2.toNat = src.length)
    (h_old : old.length = src.length)
    (h_mem : s₀.dmem =⋆ Bytes old s₀.regs.X0 ⋆ Bytes src s₀.regs.X1 ⋆ R) :
    Returns memcpy_o s₀ (fun s =>
      s.regs.X0 = s₀.regs.X0 ∧
      s.dmem =⋆ Bytes src s₀.regs.X0 ⋆ Bytes src s₀.regs.X1 ⋆ R)
```

`memcmp` returns the difference of the first differing bytes, as TF-A's C
source does (`return (sc - dc)`), in `w0`:

```lean
/-- TF-A's `memcmp` on two byte lists of equal length. -/
def memcmpRef : List UInt8 → List UInt8 → Int
  | a :: as, b :: bs =>
    if a = b then memcmpRef as bs else a.toNat - b.toNat
  | _, _ => 0

theorem memcmp_spec [layout : Layout] (h : ObjLayout memcmp_o layout)
    (s₀ : MachineData) (as bs : List UInt8) (R : DataMem → Prop)
    (h_len : as.length = bs.length) (h_n : s₀.regs.X2.toNat = as.length)
    (h_mem : s₀.dmem =⋆ Bytes as s₀.regs.X0 ⋆ Bytes bs s₀.regs.X1 ⋆ R) :
    Returns memcmp_o s₀ (fun s =>
      (s.regs.X0.toBitVec.setWidth 32).toInt = memcmpRef as bs ∧
      s.dmem = s₀.dmem)
```

C allows the two buffers of `memcmp` to overlap, which this precondition
excludes; a second spec with both buffers inside one region covers that.

`memset` fills `n` bytes with the low byte of `c` and returns `dst`:

```lean
theorem memset_spec [layout : Layout] (h : ObjLayout memset_o layout)
    (s₀ : MachineData) (old : List UInt8) (R : DataMem → Prop)
    (h_n : s₀.regs.X2.toNat = old.length)
    (h_mem : s₀.dmem =⋆ Bytes old s₀.regs.X0 ⋆ R) :
    Returns memset_o s₀ (fun s =>
      s.regs.X0 = s₀.regs.X0 ∧
      s.dmem =⋆ Bytes (List.replicate old.length s₀.regs.X1.toUInt8)
        s₀.regs.X0 ⋆ R)
```

`strtoul` is compared with a reference function that follows TF-A's C
source (which follows the C standard): skip white space, an optional sign,
an optional `0x` for base 16 or 0, digits; on overflow the result is
`ULONG_MAX`; a leading `-` negates. With `endptr` not `NULL`, the end of
the digits (or `nptr` if there were none) is stored there:

```lean
/-- The value that `strtoul` returns for the string `bs` in base `base`,
and the number of bytes it consumes (0 if it finds no digits). -/
def strtoulRef (bs : List UInt8) (base : Nat) : UInt64 × Nat := ...

theorem strtoul_spec [layout : Layout] (h : ObjLayout strtoul_o layout)
    (s₀ : MachineData) (bs old : List UInt8) (R : DataMem → Prop)
    (h_base : let b := s₀.regs.X2.toUInt32.toNat; b = 0 ∨ 2 ≤ b ∧ b ≤ 36)
    (h_old : old.length = 8)
    (h_mem : s₀.dmem =⋆ CString bs s₀.regs.X0 ⋆ Bytes old s₀.regs.X1 ⋆ R) :
    Returns strtoul_o s₀ (fun s =>
      let (v, n) := strtoulRef bs s₀.regs.X2.toUInt32.toNat
      s.regs.X0 = v ∧
      s.dmem =⋆ CString bs s₀.regs.X0 ⋆
        Bytes (s₀.regs.X0 + n.toUInt64).toBytes s₀.regs.X1 ⋆ R)
```

A second theorem covers `endptr = NULL`, where memory stays unchanged.

`setjmp` saves `x19` to `x30`, `sp` and a zero doubleword (14 doublewords,
112 bytes) into the buffer and returns 0. `longjmp` restores them and
"returns" to the saved `x30` with `x0` set to `val`, or 1 if `val` is 0, so
its postcondition is about the saved state, not about its own caller:

```lean
/-- The buffer contents that `setjmp` writes for the state `s`. -/
def jmpBuf (s : MachineData) : List UInt8 :=
  ([s.regs.X19, s.regs.X20, ..., s.regs.X30, s.regs.SP, 0].map
    UInt64.toBytes).flatten

theorem setjmp_spec [layout : Layout] (h : ObjLayout setjmp_o layout)
    (s₀ : MachineData) (old : List UInt8) (R : DataMem → Prop)
    (h_old : old.length = 112)
    (h_mem : s₀.dmem =⋆ Bytes old s₀.regs.X0 ⋆ R) :
    Returns setjmp_o s₀ (fun s =>
      s.regs.X0 = 0 ∧ s.dmem =⋆ Bytes (jmpBuf s₀) s₀.regs.X0 ⋆ R)

theorem longjmp_spec [layout : Layout] (h : ObjLayout longjmp_o layout)
    (s₀ saved : MachineData) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Bytes (jmpBuf saved) s₀.regs.X0 ⋆ R) :
    Eventually (straightlineStep (layout longjmp_o))
      (fun s => s.pc = saved.regs.X30.toInt64 ∧
        CalleeSaved saved s.data ∧
        s.data.regs.X0 = (if s₀.regs.X1 = 0 then 1 else s₀.regs.X1) ∧
        s.data.dmem = s₀.dmem)
      ⟨s₀, layout.start⟩
```

`longjmp` tests all 64 bits of `x1` (`ands x0, x1, x1; cinc x0, x0, eq`),
while C's `val` is an `int` in `w1`, whose upper 32 bits the caller need not
clear. The spec states what the code does; a C-level spec would add the
precondition that the upper bits are zero, or compare only `w0`.

## 2. Test inputs at hand (background)

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

### 2.1 Mapping symbols: `$x` and `$d` (background)

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

## 3. Lean datatype for an ELF file (later; first sketch)

Not needed for the first milestone (section 4.6). See section 1.5 for which
parts of this section are still needed later.

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

### 3.1 Why section contents stay bytes in the container layer (later)

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
- The container parser and its tests (section 5) can be finished before,
  and independently of, whatever turns instruction words into Kraken
  instructions.
- The container layer does not depend on the architecture. Kraken also has
  an x86-64 backend, and the same container parser could serve
  it, with only the code layer being specific to AArch64.
- Proofs can refer to the actual file: a statement like "the bytes at this
  offset decode to this `Operation`" keeps the decoder visible as a function
  that is part of the trusted base, instead of hiding it inside the parser.

The decoded view should still be as convenient as a decoded datatype. One
way is to make the container parametric in the section contents, e.g.
`File (Contents : Type)`, with `parse : ByteArray -> Except String (File
ByteArray)` and a `File.map` that turns `File ByteArray` into `File
CodeSection` for executable sections.

## 4. Where instruction decoding information comes from

Sections 4.1 to 4.3 are about a Lean decoder, which is later work. The first
milestone uses the objdump route of section 4.5 and the parser additions of
section 4.4.

### 4.1 Sail's Arm model (later)

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

### 4.2 Sail to Lean (later)

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

### 4.3 Options (later)

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

### 4.4 Instructions that Kraken lacks (later)

None of the first-milestone functions contains one of these instructions
(section 1.2.1), so this is not needed for the first milestone.

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

### 4.5 Without a decoder: objdump and Kraken's parser (first milestone)

How the listing gets into Lean in the first milestone is decided in
section 4.7; this section describes the general idea and what objdump does
not give.

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

Information that later verification steps need from the ELF file itself,
since `objdump -d -r` does not print it or prints it only as comments (the
first milestone needs none of it, section 4.6):

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

Later, a hybrid: parse the ELF container in Lean (section 3), and use the
objdump route only for decoding instruction words until the Lean decoder
exists. The objdump route then also serves as the oracle for testing the
decoder (section 4.3).

### 4.6 What the first milestone needs from the ELF file

Nothing beyond what `objdump -d` prints, so the first milestone has no ELF
parser. For the C library functions of section 1.2.1:

- The instructions and their offsets: objdump's listing of the function's
  section (each function is its own section, section 2).
- Where the function starts: objdump's `<strlen>:` line.
- No relocations at all: none of the C library's 23 functions without
  calls except `atexit` refers to a symbol outside its own section, and
  branches inside a section need no relocation. `-r` prints nothing for
  them.

So the only label in a first-milestone `Program` is the function's own
symbol; the first-milestone functions have no branches, and the branch
targets of the later ones are relative to that symbol (section 4.8).

Symbols outside the function (later). Kraken's `Executable.step` and
`Executable.straightline` use `Executable.labels`, which gives each label
that the program defines its address in the layout, and every other label
the address -1 (`getD (-1)` in `Kraken/AArch64/Semantics.lean`). A theorem
about a function that refers to another section, e.g. `atexit` with
`.bss.exitfun`, would then be about code that accesses
`0xffff_ffff_ffff_ffff`: a valid theorem, but not about the linked
program. This does not matter for the first milestone, whose functions
refer to no such symbol (which is why `atexit` was left out). Later, Kraken
needs a `Labels` instance that takes the addresses of the program's own
labels from the layout and those of all other symbols from a parameter, and
step functions that use it.

Later targets (section 1.2.2) then need the relocation lines that `-r`
prints under an instruction, with symbol and addend, as `ConstExpr`
operands (section 4.5): global variables (`console_list`, `psci_caps`),
addresses of constants that are returned but not read (`get_version`'s
`.rodata.build_version`), and linker-script symbols (`fixup_gdt_reloc`'s
`__RELA_START__`, `per_cpu_base`'s `__PER_CPU_START__`).

What neither the first milestone nor these later targets need:

- Initial contents of `.data`, `.rodata` and `.bss`: the specs quantify
  over the memory at a global's address, e.g. `console_unregister` works on
  whatever list `console_list` points to, since functions can be called in
  any state. The two leaves that would need constant tables (`get_el_str`,
  `plat_log_get_prefix`) need the ELF parser (section 1.2.3).
- Relocations in data sections, symbol sizes and bindings, section flags
  and alignment, segments and the entry point: these matter for calls
  through pointers in data and for composition (section 1.4).
- Whether a symbol is a function or a local label in assembly: the proofs
  name their targets. Picking the targets used `readelf -s` once, which is
  not part of any proof.

### 4.7 From objdump's output to a Lean `Program` (first milestone)

Options:

1. Generated assembly: a script converts the listing into Kraken assembly
   and writes `def strlen_o : Program := parseAArch64("...")` into a
   committed Lean file. Simple, and Lake rebuilds the proofs when the file
   changes. But the committed text is no longer objdump's, the conversion
   runs outside Lean, and beacons cannot be pasted from it.
2. A committed listing file plus an elaborator:
   `objdumpFileAArch64("libc/strlen.objdump")` reads the file at
   elaboration time, like Kraken's existing `parseFileAArch64`, converts it
   in Lean and parses it with Kraken's parser. The conversion is Lean code.
   (`parseFileAArch64("path")` reads the file with `IO.FS.readFile`, so a
   relative path is relative to the working directory of the Lean process,
   not to the Lean file; drops every line that starts with `.` and has no
   `:`, i.e. assembler directives but not labels like `.L3:`; parses the
   rest with `parse`; and returns the `Program` as a term, reporting parse
   errors at the path. Nothing in Kraken uses it. It cannot read objdump's
   output, whose lines start with offsets and instruction words.)
   But Lake does not know that the module depends on the listing file (to
   be confirmed for the Lean version used), so a changed listing need not
   trigger a rebuild of the proofs.
3. The listing verbatim inside a Lean file:
   `def strlen_o : Program := objdumpAArch64("<listing>")` (as in
   section 1.6), with an elaborator that converts and parses the string
   literal at elaboration time. The conversion is Lean code (as in 2), Lake
   tracks the file (as in 1), the committed text is objdump's own (so a
   diff against a fresh objdump run is readable), and beacons are copied
   from it.
4. Running objdump from Lean at elaboration time: needs the cross toolchain
   and the object files on every build, and the result depends on the
   machine. Rejected.

Decision: option 3.

- One Lean file per function to verify (section 4.7.1), named after it
  (`strlen_o.lean`), holds the output of
  `aarch64-none-elf-objdump -d -r --disassemble=strlen libc/strlen.o`,
  verbatim. A comment above it records the command; the inputs are pinned
  elsewhere (section 4.10).
- The elaborator `objdumpAArch64` skips objdump's header lines, checks the
  `<strlen>:` line and that the offsets start at 0 and grow by 4, drops
  the offset and instruction word columns, turns `<strlen>:` into the
  label `strlen:`, and passes the rest to Kraken's parser, which skips
  objdump's `//` comments (and later reads its branch targets,
  section 4.8). It rejects everything else: relocation lines, data lines
  (`.word`), further symbols.
- A script in ADTF (it needs the imx-atf build, section 4.7.2) overwrites these
  files with fresh output from the object files of the pinned build. `git diff`
  shows what changed; CI runs the script on a clean checkout and fails if `git
  diff` is then not empty. The script only writes the listing files, never the
  proofs. The C library's object files contain no time stamps or build paths
  (checked with `strings`), so a rebuild at the pinned commit with the pinned
  toolchain should give the same listings.

Why the proofs are then about this output: each theorem mentions `strlen_o`,
whose value Lean computes from the string literal while elaborating
the listing file, and Lean checks the proof against that value. The CI
check ties the string literal to objdump's output for the object file of
the pinned build. Beacons add a redundant check inside the proofs. What remains
trusted is objdump, the elaborator's conversion, and Kraken's parser and
semantics.

#### 4.7.1 A listing file

There is one Lean file per function to verify, named after the function,
e.g. `src/lean/ADTF/AtfLibc/Listing/longjmp_o.lean` (proofs go into
separate files, section 4.10). The script fills it with:

```lean
-- Generated by src/scripts/atf-listings.py. Do not edit; rerun the script.
import Kraken.AArch64.Objdump

namespace ADTF.AtfLibc.Listing

/-- `aarch64-none-elf-objdump -d -r --disassemble=longjmp libc/setjmp.o`,
run in `imx-atf/build/imx93/release`. -/
def longjmp_o : Program := objdumpAArch64(r#"

libc/setjmp.o:     file format elf64-littleaarch64


Disassembly of section .text.asm.setjmp:

Disassembly of section .text.asm.longjmp:

0000000000000000 <longjmp>:
   0:	a9467c07 	ldp	x7, xzr, [x0, #96]
   4:	a9405013 	ldp	x19, x20, [x0]
   8:	a9415815 	ldp	x21, x22, [x0, #16]
   c:	a9426017 	ldp	x23, x24, [x0, #32]
  10:	a9436819 	ldp	x25, x26, [x0, #48]
  14:	a944701b 	ldp	x27, x28, [x0, #64]
  18:	a945781d 	ldp	x29, x30, [x0, #80]
  1c:	910000ff 	mov	sp, x7
  20:	ea010020 	ands	x0, x1, x1
  24:	9a801400 	cinc	x0, x0, eq	// eq = none
  28:	d65f03c0 	ret
"#)

end ADTF.AtfLibc.Listing
```

- The string is objdump's standard output, byte for byte, including its
  tabs and the header lines. objdump runs in the build directory with a
  relative path, so the header line contains no absolute path. A raw string
  literal (`r#"..."#`) needs no escaping; Lean accepts tabs in it (checked
  with the pinned Lean version, also with a custom `str` elaborator
  argument like `objdumpAArch64`'s).
- objdump prints a `Disassembly of section` line for every executable
  section of the file, even with `--disassemble=longjmp`. The elaborator
  skips these and the file header line, and requires exactly one symbol
  block, `<longjmp>:`, at offset 0.
- `--disassemble=sym` takes one symbol (with several, objdump uses only
  the last), so one file per function also means one objdump run per
  file.
- The type is Kraken's `Program` (section 1.3.2), or `List Instr` with
  the alternative of section 1.3.3.

#### 4.7.2 The script

Python 3, standard library only (`subprocess`, `pathlib`): it calls the
toolchain, looks up symbols and writes files, which is awkward in Bash and
has no advantage in Lean. It does not parse objdump's output; all
interpretation of the listing is in the Lean elaborator, so there is one
converter, checked by Lean, not two. It does not compare anything with the
committed files either; that is `git diff`'s job. What it does:

1. Toolchain check: compares the first lines of `gcc --version` and
   `objdump --version` (prefix from `CROSS_COMPILE`, as for TF-A's build)
   with the committed version file, and fails with a message that names
   the file (section 4.10).
2. Build: runs `make PLAT=imx93 bl31` in `imx-atf` with that toolchain
   (incremental, so a few seconds when nothing changed).
3. The functions to list are the files `Listing/*_o.lean`: `longjmp_o.lean`
   means `longjmp`. To add a function, create the file
   (`touch Listing/strlen_o.lean`) and run the script.
4. For each function, finds the object file in the build directory that
   defines it as a function symbol (`readelf -sW` on all object files,
   read once). Exactly one must; otherwise the script fails and names the
   candidates (static functions can have the same name in several object
   files; section 8).
5. Runs objdump, checks that the output contains the line
   `0000000000000000 <sym>:` exactly once (for an unknown symbol objdump
   prints only the headers and still exits with 0) and does not contain
   `"#`, which would end the raw string.
6. Overwrites the file with the template filled in.

About 60 lines of Python. Afterwards `git diff` shows what changed. CI
runs the script on a clean checkout, so with a fresh build of the pinned
imx-atf commit, and fails if `git diff --exit-code` reports a change (on
an incremental local build, objects compiled before a toolchain change
are not rebuilt by `make`; a clean build avoids that). The script is
hardly part of the trusted base: it copies objdump's output verbatim, and
a reader can compare a listing with objdump's output by eye.

### 4.8 Branch targets (later)

The first-milestone functions have no branches apart from `ret`; the C
library's functions with loops need this section.

objdump prints a branch inside a function as `cbnz w2, 14 <strlen+0x14>`:
`14` is the target's offset in the section, in hexadecimal without `0x`,
and `<strlen+0x14>` the same target as symbol plus offset. Kraken's parser
does not expect the `<...>` part. Dropping it, as the
converter of section 4.5 originally planned, would be wrong silently:
Kraken's parser reads `14` as decimal, and Kraken's semantics treats a
numeric branch target as relative to the branch instruction
(`ConstExpr.evalBranchTarget`), so `cbnz` at offset 8 would branch to
offset 8 + 14 = 22 instead of 0x14 = 20.

Kraken's `ConstExpr` can express the target: `.add (.label "strlen")
(.int64 0x14)`. `evalBranchTarget` interprets a target that is not a plain
number as an absolute address, so this is the address of `strlen` plus
0x14, which is right under the layout hypothesis of section 4.9.

Ways to produce it:

1. The converter computes the offset relative to the branch
   (`cbnz w2, #12`): no parser change, but the text differs from objdump's
   and is hard to read, and beacons cannot be pasted.
2. The converter inserts a label before each branch target (`strlen.0x14:`)
   and branches to it: no parser change, and branches do not depend on the
   layout, but the text again differs from objdump's.
3. Kraken's parser learns objdump's form: a hexadecimal number followed by
   `<sym>` or `<sym+0xoff>` becomes `.add (.label sym) (.int64 off)`, and
   it also accepts `sym+off` on its own, which relocations with an addend
   need later (`trdc_mgr_blks+0x10`). The elaborator checks that `sym` is
   the function's symbol and that the number equals `off`.

Decision: option 3. Listing lines then reach Kraken's parser unchanged
apart from the dropped columns, and a beacon's string is objdump's text.

### 4.9 The layout hypothesis (first milestone)

A theorem about an object file holds for every address the linker may
choose, so it quantifies over the `Layout`. Kraken's `Layout` lets every
directive have an arbitrary size, so branch targets like `strlen+0x14` and
beacon addresses are only right with a hypothesis that the layout is the
object file's: each instruction takes 4 bytes, each label 0 bytes, and the
code starts at a multiple of 4 (`ObjLayout` in section 1.6; `Loaded` with
the beacon core of section 1.3.1).

This holds for AArch64. Every A64 instruction is 4 bytes; AArch64 has no
variable-length or compressed encodings (unlike T32 in AArch32, or
x86-64). Labels occupy no bytes, and data in code sections (`byteArray`,
none in the first-milestone functions) takes its length. Kraken already has
this function: `Directive.fakeSize`, used by `Program.fakeLayout` for
testing. Each function's section has alignment 4 (`.text.strlen` in
`readelf -S`), so the linker places it at a multiple of 4, which the
architecture requires anyway for instruction addresses.

### 4.10 Where things live and what is pinned (first milestone)

Kraken, on a new branch `aarch64-atf` of the `kraken` submodule:

- `Kraken/AArch64/Parser/Basic.lean`, later: objdump's branch-target form
  and `sym+off` (section 4.8).
- A new file for the `objdumpAArch64` elaborator (section 4.7).
- New files for the beacons, separate from Kraken's existing files: the
  core of section 1.3.1, the `instr` tactic, and their tests.

ADTF, on `main`:

- `src/lean/ADTF/AtfLibc/`, a new subfolder of ADTF's Lean project (which
  depends on the `kraken` submodule): in `Listing/`, one file per function
  with its listing, regenerated by the script; next to it, files with the
  specs and proofs, which the script never touches; spec helpers
  (`Returns`, `CalleeSaved`, `Bytes`) in a common file.
- The listing script of section 4.7.2 (`src/scripts/atf-listings.py`),
  and a script that builds BL31, outside the Lean project.
- The toolchain version file (e.g. `src/toolchain/arm-gnu-toolchain.version`).

Pinned inputs:

- imx-atf: by the commit of the `imx-atf` submodule, which a clean CI
  checkout builds.
- The Arm GNU Toolchain: the committed version file holds the expected
  first lines of `aarch64-none-elf-gcc --version` and
  `aarch64-none-elf-objdump --version`, currently
  `aarch64-none-elf-gcc (Arm GNU Toolchain 14.3.Rel1 (Build arm-14.174))
  14.3.1 20250623` and `GNU objdump (Arm GNU Toolchain 14.3.Rel1 (Build
  arm-14.174)) 2.44.0.20250616`. Both the build script and the listing
  script compare them with the installed tools and fail on a mismatch,
  naming the version file and saying that either the pinned toolchain has
  to be installed or the file updated and the listings regenerated.

## 5. Testing and checking

Producing ELF files or instruction words is not a goal, so there is no ELF
encoder and no instruction encoder, and no round-trip test. What the proofs
rely on is checked against independent GNU binutils tools (open source,
part of the Arm GNU Toolchain installed for section 2).

### 5.1 The committed listings (first milestone)

CI builds BL31 from a clean checkout, runs the listing script of section 4.7.2,
which overwrites the committed listings, and fails if `git diff` is not empty;
it also builds the Lean project. Together with Lean checking the proofs against
the programs elaborated from these listings, this ties each theorem to the
object file.

### 5.2 Coverage of the whole build (later)

Every instruction line of `objdump -d -r` of every object file must be
converted and parsed by Kraken's parser. This measures coverage, and shows
which aliases and instructions Kraken's parser still lacks (section 4.4).
Whether the parsed `Operation` means what objdump's text means is part of
the trusted base (Kraken's parser), not tested here.

The test takes a directory and checks every object file (`*.o`) in it,
recursively. Kraken's test suite runs it on a few small object files
committed to Kraken (TF-A is BSD-3-Clause), chosen among those that made a
test fail during development, with the expected `objdump` (and later
`readelf`) output committed next to them, so that the test suite does not
need the cross toolchain. During development, the same test runs the tools
on the BL31 build directory `imx-atf/build/imx93/release` (section 2).

### 5.3 The ELF container parser (later)

The ELF container parser (section 3) is compared with `readelf -h -S -s -r
-W`, which prints all header fields, sections, symbols and relocations. A
printer for the parsed value in that format is simple. Comparing with an
independent tool catches misinterpreted fields, e.g. the binding and type in
a symbol's `st_info` byte swapped, which a round trip with an encoder that
makes the mirror-image error would not catch. It runs on the same
directories as the test of section 5.2.

## 6. Decisions so far

For the first milestone:

- Goal: proofs about functions in AArch64 object files, composable under
  linking later. Success: a few interesting BL31 functions verified
  (section 1.1). The first milestone takes the functions of TF-A's C
  library that make no calls, refer to no other section and contain no
  loop: `putchar`, `setjmp`, `longjmp` (section 1.2.1).
- Proofs use instruction beacons, `instr "<objdump text>" at sym + off`,
  whose string is parsed by Kraken's assembly parser (section 1.3).
- The objdump listings of the verified functions are committed verbatim
  inside Lean files and elaborated into Kraken `Program`s; a script
  regenerates and diffs them (section 4.7). No ELF parser and no Lean
  decoder in the first milestone (section 4.6).
- The listing files hold objdump's output verbatim in raw string
  literals; the script is Python with the standard library only, and does
  not parse objdump's output (sections 4.7.1 and 4.7.2).
- Each theorem assumes the object file's layout: 4-byte instructions,
  0-byte labels, 4-byte-aligned start (section 4.9).
- No encoders and no round trips (section 5).
- Kraken changes go on the branch `aarch64-atf` of the `kraken` submodule,
  the beacons in separate files there; the listings, specs and proofs go
  into `src/lean/ADTF/AtfLibc/` on ADTF's `main` (section 4.10).
- imx-atf is pinned by its submodule commit, the toolchain by a committed
  version file that the scripts check (section 4.10). CI runs the listing
  script on a clean checkout and fails if `git diff` is not empty.
- The listing files and `objdumpAArch64` use a `List Instr`, as in ToySys,
  for the first milestone, and Kraken's `Program` once a function with
  local symbols is verified (sections 1.3.2 and 1.3.3).

For later:

- Kraken's parser accepts objdump's branch-target form `14 <strlen+0x14>`
  as `.add (.label "strlen") (.int64 0x14)` (section 4.8).
- The C library's functions with loops (section 1.2.1), then other
  platform-independent functions without calls (section 1.2.2), then
  calls (section 1.2.3); the TRDC functions come after that, once a TRDC
  semantics from Sockeye's Lean backend can be combined with Kraken's
  (section 1.2.4).
- Instructions missing from Kraken are added to Kraken's `Operation`, its
  assembly parser and its printer without semantics; executing them yields
  `Effects.unimplemented` (section 4.4).
- Relocated operands are expressed with Kraken's `ConstExpr` (`label`,
  `pg_hi21`, `lo12`, `add`).
- The ELF container layer is architecture-independent (ELF64 little-endian)
  and kept in a separate directory or file; the code layer is instantiated
  only for AArch64 for now (section 3).
- Two layers: a container layer that mirrors the file, and a code layer that
  decodes executable sections into Kraken instructions. Section contents
  stay bytes in the container layer; decoded instructions are a view
  computed from them (section 3.1).
- Use the `$x`/`$d` mapping symbols to separate code from data. Files
  without them (stripped executables) are not a target, but can be handled
  by treating executable sections as code (section 2.1).
- Words the decoder does not support are kept as `undecoded`, not rejected.
- If a decoder is written, it is agent-written Lean with encodings from
  `sail-arm` (section 4.3).
- The converter's coverage is tested on all object files (section 5.2), the
  ELF parser against `readelf` (section 5.3).

## 7. Next steps

First milestone:

1. Write the `objdumpAArch64` elaborator, the toolchain version file, the
   build script, the listing script and the CI job (sections 4.7 and
   4.10), for `putchar`, `setjmp` and `longjmp`.
2. Write the beacon core and the `instr _ at _` tactic, taking a string,
   in separate files in Kraken (sections 1.3.1 and 4.10).
3. Define `Returns`, `CalleeSaved` and `Bytes` (section 1.6), with
   `Loaded` instead of `ObjLayout` if section 1.3.1 is adopted.
4. Verify `putchar`, then `setjmp` and `longjmp`.

Later: the C library's functions with loops (section 1.2.1): the parser
extension for branch targets (section 4.8), a loop rule, conditional
branches in the beacon tactic, `CString`, in the order suggested in
section 1.2.1. Then the other functions without calls (section 1.2.2),
external symbols (section 4.6), calls (section 1.2.3), then the ELF
container parser for object files when a target needs data sections
(first: the constant tables of `get_el_str` and `plat_log_get_prefix`, and
`vsnprintf`'s jump table in `.rodata`), then the rest of the "Later" list
in "Scope at a glance".

## 8. Open points

For the first milestone:

1. Whether the beacon core of section 1.3.1 replaces Kraken's
   `Executable` for these proofs, with `Program` (section 1.3.2) or
   `List Instr` (section 1.3.3, recommended for now), and whether
   `simp only` reduces `Operation.interp` fast enough or Kraken's
   `kdeltaBetaOnly` simproc is needed.
2. Whether objdump's exact operand syntax parses for the three
   functions (`mov x0, #0x0  // #0` in `setjmp`, `cinc x0, x0, eq  // eq =
   none` in `longjmp`, tabs between mnemonic and operands). All their
   mnemonics occur in Kraken's parser, but only feeding the listings to it
   will tell (step 1 of section 7).
3. The beacon tactic: parsing the string at elaboration time, comparing it
   with the fetched instruction, the address as symbol plus offset
   (section 1.3).
4. Spec conventions (section 1.6): returning means reaching the initial
   `x30`; `CalleeSaved` lists `x19` to `x29` and `sp`; all other registers
   and the flags may change. Whether `Returns` should also say that the
   function does not touch memory outside its precondition (it does, via
   the frame `R`, but only when the postcondition mentions `R`).
5. The `Bytes` predicate (section 1.6), including the no-wrap side
   condition, and how `setjmp`'s 14 `stp` stores into a 112-byte buffer
   are best related to `jmpBuf` with Kraken's separation logic.
6. `setjmp`/`longjmp`: `longjmp` does not fit `Returns`; its 64-bit test of
   `x1` versus C's `int val` (section 1.6).
7. Confirming that rebuilding at the pinned imx-atf commit with the
   pinned toolchain gives the same listings (section 4.10), and where CI
   runs: it needs the Arm GNU Toolchain and a BL31 build.
8. Stating the trusted base next to each theorem (section 1.1).

For later:

1. Symbols outside the functionFor later:

1. Symbols outside the function: Kraken gives them the address -1
   (section 4.6); needed for `atexit` and most of section 1.2.2.
2. Relocations with an addend (`trdc_mgr_blks+0x10`), via the parser
   extension of section 4.8.
3. Name clashes between object files: static functions and section symbols
   (`.rodata.str1.1`, `.text.unsigned_num_print`) repeat across files, so
   label names need to be qualified by object file before proofs about
   several files are combined.
4. The instructions that Kraken lacks, and the coverage test (sections 4.4
   and 5.2).
5. For the C library's functions with loops: whether objdump's syntax
   parses for all 20; a loop rule (Kraken's `reg_dec_loop` counts a
   register down and is used only in an x86-64 example; `strlen`,
   `memchr`, `strcmp` and `strtoul` loop until they see a certain byte, so
   they need a rule with an invariant and a measure, e.g. the bytes left
   before the NUL); two goals for a conditional branch in the beacon
   tactic; `CString`; a second spec form for overlapping read-only buffers
   (`memcmp`, `strcmp`); reference functions in Lean (`strtoulRef` and its
   relatives, `strtok_r`'s state, the digits of `unsigned_num_print`), each
   following the C source closely, since a reader has to trust them.
