# AArch64 ELF parser in Lean: plan and design decisions

This document records the plan and the design decisions for an AArch64 ELF
parser written in Lean. It is extended as the design develops.

## 1. Goal

Read AArch64 ELF files into Lean, so that their code can be reasoned about
with Kraken (the `kraken` submodule). The first use case is the object files
and the linked `bl31.elf` of TF-A for the i.MX 93 (the `imx-atf` submodule).

- Both relocatable object files (`.o`, `ET_REL`) and executables
  (`ET_EXEC`) are in scope. They share the ELF container format (file
  header, section headers, symbol table, string tables), but differ in what
  is filled in: an object file has relocation sections, section addresses of
  0 and possibly undefined symbols, while an executable has program headers
  (segments), final addresses and usually no relocations.
- Instructions are decoded into Kraken's `AArch64.Operation` inductive, so
  that Kraken's semantics and tactics apply to them.
- Kraken's `Directive`/`Program`/`Executable` layer, which describes one
  contiguous program with a single start address, probably does not match an
  ELF file; see section 3.

Constraint: only open-source software is used (the two proprietary NXP
firmware files that the i.MX 93 boot image needs are the only exception, and
they are not needed for this parser).

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
- The toolchain emits the AArch64 mapping symbols `$x` (code starts here) and
  `$d` (data starts here); `bl31.elf` has 472 of them. They tell code apart
  from literal pools and other data in executable sections. Without them,
  `objdump -d` decodes the strings in `bl31.elf`'s `.ro` section as
  instructions.
- Instructions in `bl31.elf` that Kraken's `Operation` does not cover yet
  (counts from `objdump -d`, about 9,700 instructions in total): `mrs` (130),
  `msr` (115), `isb` (36), `dsb` (26), `dc` (7), `wfi` (7), `eret` (3),
  `wfe` (2), and one each of `tlbi`, `sev`, `sevl`, `udf`, `ldaxr`, `stxr`,
  `stlr`, `stlrb`, `ldarb`. Roughly 4% of the code; the rest are
  integer, load/store and branch instructions that Kraken has (`objdump`
  prints aliases such as `mov`, `cmp`, `tst`, `lsl`, `ubfx`, `cset`).
  How they are handled is decided in section 4.4.

## 3. Lean datatype for an ELF file (first sketch)

Two layers:

1. A faithful container layer that mirrors the file: header, sections with
   their raw bytes, segments, symbols and relocations. Parsing it needs no
   knowledge of instructions. Unknown enum values are kept (`other n`) rather
   than rejected, so that any valid ELF file parses.
2. A code layer on top: the executable sections decoded into Kraken
   instructions, with relocations and symbols folded into the operands.

Only ELF64, little-endian, `EM_AARCH64` (183) is accepted; anything else is
a parse error.

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

## 5. Round-trip testing

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
- The test checks the round trip on every object file that it finds in a
  given directory, recursively. (Suggestion: also every `*.elf` file, so that
  executables such as `bl31.elf` are covered.)
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

## 6. Decisions so far

- Parse ELF64 little-endian AArch64 only.
- Two layers: a container layer that mirrors the file, and a code layer that
  decodes executable sections into Kraken instructions.
- Use the `$x`/`$d` mapping symbols to separate code from data.
- Express relocated operands with Kraken's `ConstExpr` (`label`, `pg_hi21`,
  `lo12`, `add`).
- Words the decoder does not support are kept as `undecoded`, not rejected.
- The decoder is agent-written Lean with encodings from `sail-arm`
  (section 4.3).
- Instructions missing from Kraken are added to Kraken's `Operation` without
  semantics; executing them yields `Effects.unimplemented` (section 4.4).
- An ELF encoder is written too. A Kraken test checks the round trip on all
  object files in a directory, recursively; Kraken's test suite runs it on a
  few committed object files, and during development it runs on the BL31
  build directory (section 5.4).
- The layout details needed for byte equality are kept in a separate
  `Layout` (section 5.3); the constant fields and the zero padding are
  checked by the parser instead of stored (section 5.2).

## 7. Next steps

To be decided in the next prompts.
