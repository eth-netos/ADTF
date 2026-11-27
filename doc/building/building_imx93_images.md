# Building Linux images for the FRDM i.MX93 board

Living planning document: decisions, verified facts, the build procedure,
and open questions. Nothing has been built yet.

Status as of 2026-11-27: planning; BitBake is downloaded to
`~/tools/bitbake` (D16); of `meta-adtf`, only the fragment exists; no
build started.

Decisions (D…) and open questions (Q…) keep their numbers. A resolved
question is removed from "Open questions" and becomes a decision that names
it, so gaps in the question numbering are expected.

## Decisions

D1. **The NXP firmware binaries are never modified.** The boot firmware
    (EdgeLock Secure Enclave container `mx93a1-ahab-container.img`, from
    `firmware-ele-imx`) and the LPDDR4 training firmware
    (`lpddr4_{i,d}mem_{1,2}d_v202201.bin`, from `firmware-imx`) are only
    available under the NXP Software License Agreement (LA_OPT_NXP v64.2).
    The human project owner accepts using them unmodified. Neither the human
    nor any agent may modify these files. (See also D11 about packaging.)

D2. **No other software under the NXP Software License Agreement** (or any
    other proprietary license) goes into the image or the build, apart from
    the two firmware packages of D1.

D3. **`meta-imx` is not used.** Its release is distributed under the NXP
    Software License Agreement (`LICENSE.txt` and
    `SCR-6.18.37-2.1.0.txt` in `meta-imx` tag `rel_imx_6.18.37_2.1.0`).
    `meta-freescale` (MIT metadata) is used instead.

D4. **Submodules**: See D7.

D5. **We use `meta-freescale`'s `wrynose` branch**

D6. **The NXP EULA is never accepted in this repository** (resolves Q1).
    Each person who builds reads `meta-freescale/EULA` and decides for
    themselves. If they accept, they enable the `meta-freescale` fragment
    `freescale-layer/eula/accept-fsl-eula` in their own build directory
    (step 5 of the build procedure). Nothing committed to this
    repo may set `ACCEPT_FSL_EULA`, enable that fragment, or record anyone's
    acceptance. Agents never enable the fragment.
    Enabling the fragment only changes the build directory's
    `conf/toolcfg.conf` (step 5 of the build procedure). The build
    directory is outside this repo (`~/yocto-builds/imx93-frdm/build`,
    D10), and `.gitignore` excludes `bitbake-builds/`, where
    `bitbake-setup` would put it if run from the repo root without the
    top-directory settings, so the acceptance cannot be committed by
    accident. `bitbake-setup update` regenerates `conf/` when the
    configuration changed (keeping the old one as `conf-backup-<time>`),
    so the fragment may have to be enabled again after an update.
    Two consequences of how `meta-freescale/classes/fsl-eula-unpack.bbclass`
    checks `ACCEPT_FSL_EULA`: the check is in `do_unpack`, so the NXP
    archives are already *downloaded* (`do_fetch`) before acceptance is
    checked. And the `firmware-imx` archive holds many other blobs (VPU,
    SDMA, HDMI, EPDC, …) that get unpacked under the same EULA, even though
    only the DDR files are installed.

D7. **Only code we modify becomes a submodule** (resolves Q3; revised on
2026-11-27, when the human project owner decided against submodules for
unmodified code).
Removal of unused git submodules is only done by the human project owner.
Addition of git submodules can be done by the agent if the human project
owner asks for it explicitly.

- **Source code we modify:** submodule, built through an override in
  `meta-adtf` (D8): `imx-atf`, `linux`.
- **Our own layer:** committed directly in this repo: `meta-adtf` (D8).
- **Layers and BitBake, unmodified:** not submodules. A layer setup tool
  puts them on disk at pinned versions (`bitbake-setup`, D10):
  `bitbake`, `openembedded-core`, `meta-yocto` (if poky, Q4),
  `meta-freescale`.
- **Recipe sources we don't modify:** downloaded by BitBake: U-Boot,
  `imx-mkimage`, the firmware, GCC, BusyBox and so on.

Layers have to be on disk because BitBake reads them from local
directories and never downloads them. `imx-manifest` is not read by BitBake
at all; we only use it as a reference for which versions go together,
which is recorded in this document (`imx-6.18.37-2.1.0.xml`, commit
`66a5b81`). The `linux` submodule is marked `shallow = true` and
`update = none` in `.gitmodules` (see "Shallow submodules" for why).

D8. **Our own layer `meta-adtf/`** at the repo root holds everything we
change about the build, so that `meta-freescale` and the other layers
stay unmodified:

```
meta-adtf/
  conf/layer.conf                        # declares the layer
  conf/fragments/board/imx93-frdm.conf   # committed build config
  bitbake-setup/imx93-frdm.conf.json     # layer setup (D10)
  recipes-bsp/imx-atf/imx-atf_%.bbappend
  recipes-kernel/linux/linux-fslc-imx_%.bbappend
```

- `.bbappend` files point recipes at our submodules.
- The fragment `adtf/board/imx93-frdm` holds the build configuration
  that everyone shares: `MACHINE`, `DISTRO`, the license policy
  (`INCOMPATIBLE_LICENSE` and its two exceptions from D1), and removing
  the Wi-Fi machine features and `optee` (D15). See step 4 of the build
  procedure.
- Only per-person settings live outside the repo: thread counts in
  `~/yocto-builds/site.conf` (D10), and the person's own EULA acceptance
  in the build directory's `conf/toolcfg.conf` (D6).
- Fragments are parsed after `local.conf` (`bitbake.conf` line 822 vs.
  817), so plain `=` assignments in the fragment win over `local.conf`.
  Settings people may want to tune use `?=` in the fragment.
- `layer.conf` computes the repo root from its own location, so nothing
  committed contains an absolute path:

  ```
  ADTF_REPO_ROOT := "${@os.path.normpath(d.getVar('LAYERDIR') + '/..')}"
  ```

D9. **Linux is built with `externalsrc` from the `linux` submodule:**

```
# meta-adtf/recipes-kernel/linux/linux-fslc-imx_%.bbappend
inherit externalsrc
EXTERNALSRC = "${ADTF_REPO_ROOT}/linux"
```

The submodule tracks `https://github.com/Freescale/linux-fslc`, branch
`6.18-2.1.x-imx`, starting at the commit the recipe pins (`0eb3d176c`,
Linux 6.18.65). `externalsrc` builds directly from the working tree,
including uncommitted changes, and skips BitBake's own fetch, unpack
and patch steps. That avoids a second multi-GB copy of the kernel in
`DL_DIR`, which a `git://…;protocol=file` URL would create. (Building
with it is not yet tested.)

Added by an agent on 2026-11-27, at the human project owner's request:

```
git clone --depth 1 --branch 6.18-2.1.x-imx \
    https://github.com/Freescale/linux-fslc.git linux
git submodule add https://github.com/Freescale/linux-fslc.git linux
git config -f .gitmodules submodule.linux.branch 6.18-2.1.x-imx
git config -f .gitmodules submodule.linux.shallow true
git config -f .gitmodules submodule.linux.update none
git submodule absorbgitdirs linux
```

`git submodule add --depth 1 -b 6.18-2.1.x-imx …` does not work: its
shallow clone only fetches the default branch `7.2.x+fslc`, so the branch
is not found. The `git clone` took 53 s and received 99264 objects,
277 MiB (at 16 MiB/s); the result is 290 MB of git data and 1.8 GB in
total on disk.

D10. **Layers are set up with `bitbake-setup`** (resolves Q14), from our
own configuration file committed at
`meta-adtf/bitbake-setup/imx93-frdm.conf.json`, with the top directory
`~/yocto-builds` outside this repo.
We do not use Google's `repo` tool, even though some NXP setups do that,
we use `bitbake-setup` instead to download the right repos.

- The configuration pins every source to an exact commit (the
  `yocto-6.0.2` commits for `bitbake`, `openembedded-core` and
  `meta-yocto`; `meta-freescale` `wrynose` at `89e6e24b5`, D5). Moving to
  newer commits is a deliberate edit of this file.
- `meta-adtf` is added with `bb-layers-file-relative: [".."]`, which
  `bitbake-setup` resolves relative to the configuration file, so nothing
  committed contains an absolute path. This only works when the
  configuration is given as a local file (not from a registry or URL).
- The setup directory is `~/yocto-builds/imx93-frdm`, with `layers/`,
  `build/` and `config/`. Layer clones, recipe downloads and sstate are
  shared under `~/yocto-builds` (`.bitbake-setup-downloads`,
  `.sstate-cache`, written into `~/yocto-builds/site.conf`).
- Per-person settings that should survive `bitbake-setup update` go into
  `~/yocto-builds/site.conf` (created once, never overwritten) rather
  than the build directory's `conf/local.conf`.
- `bitbake-setup` itself runs from `~/tools/bitbake` (D16). The build then
  uses the copy that `bitbake-setup` clones into
  `~/yocto-builds/imx93-frdm/layers/bitbake`, at the same commit.
- Sketch of the configuration (not yet written or tested):

```
{
  "description": "ADTF: FRDM i.MX93 image, Yocto 6.0 wrynose",
  "sources": {
    "bitbake": {"git-remote": {
      "remotes": {"origin": {"uri": "https://github.com/openembedded/bitbake"}},
      "branch": "2.18",
      "rev": "acfe02fa38b5da9e6a36c6cedcf91d4fcbefbfbd"}},
    "openembedded-core": {"git-remote": {
      "remotes": {"origin":
        {"uri": "https://github.com/openembedded/openembedded-core"}},
      "branch": "wrynose",
      "rev": "5d1aa5c806c061a2994f4decb59016610f093213"}},
    "meta-yocto": {"git-remote": {
      "remotes": {"origin": {"uri": "https://git.yoctoproject.org/meta-yocto"}},
      "branch": "wrynose",
      "rev": "24c24cef5d1523fefe43a3e3d34667b37ae551f3"}},
    "meta-freescale": {"git-remote": {
      "remotes": {"origin":
        {"uri": "https://github.com/Freescale/meta-freescale"}},
      "branch": "wrynose",
      "rev": "89e6e24b57d513dced917e5aaadcf855a700ca7f"}}
  },
  "bitbake-setup": {"configurations": [{
    "name": "imx93-frdm",
    "description": "core-image-minimal for imx93-11x11-lpddr4x-frdm",
    "bb-layers": ["openembedded-core/meta", "meta-yocto/meta-poky",
                  "meta-freescale"],
    "bb-layers-file-relative": [".."],
    "oe-fragments": ["adtf/board/imx93-frdm"],
    "setup-dir-name": "imx93-frdm"
  }]}
}
```

D11. **Packaging the firmware into the boot image is not modification**
(resolves Q6). `imx-mkimage` pads and concatenates the DDR firmware files
and embeds the ELE container into `flash.bin`; the files' contents stay
unchanged, so this is allowed under D1.

D12. **Board setup** (resolves Q7): we assume `meta-freescale`'s default
silicon revision (`IMX_SOC_REV = "A1"`, so `mx93a1-ahab-container.img`).
The human project owner sets the DIP switch SW1 (`BOOT_MODE`) to `0001`:
the boot core is the Cortex-A core (not the Cortex-M), and the boot device
is the serial downloader (USB). How images get onto the board is out of
scope for now.

D13. **BitBake tasks are not cut off from the network** (resolves Q10).
Unprivileged user namespaces do not work in the container (`unshare -Urn`
returns EPERM, because of `--cap-drop ALL`, Docker's seccomp profile, and
the host's `apparmor_restrict_unprivileged_userns=1`). OE's `check_userns`
sanity check still passes, because `unshare` fails cleanly. The effect is
that tasks other than `do_fetch` can reach the network. We accept this
reproducibility risk and do not change the container setup for it.

D14. **The image is `core-image-minimal`** (resolves Q11): BusyBox, serial
console on `ttyLP0` at 115200, no SSH server.

D15. **No OP-TEE** (resolves Q12, option a): the `optee` machine feature is
removed in the `meta-adtf` fragment, so the five OP-TEE `.inc` files that
`meta-freescale` copied from `meta-imx` are not used, and the boot chain is
simpler.

D16. **BitBake tools come from `~/tools/bitbake`, never from
`/opt/bitbake`.** `~/tools/bitbake` is a full clone of
https://github.com/openembedded/bitbake, checked out at `yocto-6.0.2`
(`acfe02fa3`, BitBake 2.18.0), and goes first on `PATH` (step 1 of the
build procedure). This works the same in a future container without
`/opt/bitbake`, lets BitBake write `pyshtables.py` into its own
installation directory (checked: `lib/bb/pysh/pyshtables.py`, ignored by
BitBake's git, nothing written to the current directory), and allows
switching versions with `git checkout` without a new container.

## Verified facts

Checked by an agent on 2026-11-26. Facts about `meta-freescale` refer to
`wrynose` `89e6e24b5` unless stated otherwise.

### Licenses

- `imx-atf`: `docs/license.rst` says BSD-3-Clause, with bundled third-party
  code under permissive licenses (BSD-2-Clause, NCSA, Zlib, MIT,
  Apache-2.0). All 261 `SPDX-License-Identifier` tags under `plat/imx` are
  BSD-3-Clause.
- `meta-freescale`: metadata is MIT (`COPYING.MIT`). Its recipes fetch
  software under many licenses. `LICENSE` lists them, including
  `LicenseRef-Proprietary` ones (firmware, ISP, Wi-Fi firmware). Recipes
  under the NXP EULA use `fsl-eula=true` and only build if
  `ACCEPT_FSL_EULA = "1"` is set.
- `imx-manifest`: `LICENSE.txt` is MIT. **But** the manifest XML files list
  `meta-imx`, `meta-nxp-connectivity` and `meta-nxp-demo-experience`, so
  `repo sync` with an unmodified manifest would download NXP-EULA layers.
  The manifest is therefore used only as a reference for which revisions of
  the other layers work together.
- Not everything under https://github.com/nxp-imx is under the NXP license.
  `linux-imx` (GPL-2.0), `uboot-imx` (GPL-2.0), `imx-mkimage` (GPL-2.0-only)
  and `imx-atf` (BSD-3-Clause) are open source. The NXP license covers
  `meta-imx` and the binary firmware/driver packages.

### What the build pulls in for `imx93-11x11-lpddr4x-frdm`

`meta-freescale` has the machine
`conf/machine/imx93-11x11-lpddr4x-frdm.conf`. On `wrynose`, all i.MX93
machines use the NXP BSP: `imx93-evk.inc` sets `IMX_DEFAULT_BSP = "nxp"`
with a hard assignment, and the FRDM machine has no mainline U-Boot
settings. (On `master`, `fe15edb0a`, the same file uses `?=`, and the FRDM
machine also supports a mainline BSP with `u-boot-fslc` 2026.10, U-Boot
binman instead of `imx-mkimage`, and `linux-fslc` 7.2.)

| Part      | Recipe                         | Source               | License  |
|-----------|--------------------------------|----------------------|----------|
| TF-A      | `imx-atf` 2.14 `af9eb2c17`     | nxp-imx/imx-atf      | BSD-3    |
| U-Boot    | `u-boot-imx` 2026.04           | nxp-imx/uboot-imx    | GPL-2.0+ |
| Container | `imx-boot` (`imx-mkimage`)     | nxp-imx/imx-mkimage  | GPL-2.0  |
| Kernel    | `linux-fslc-imx` 6.18          | Freescale/linux-fslc | GPL-2.0  |
| ELE fw    | `firmware-ele-imx` 2.0.7       | NXP mirror           | NXP EULA |
| DDR fw    | `imx-boot-firmware-files` 8.33 | NXP mirror           | NXP EULA |
| OP-TEE    | `optee-os` 4.10.0.imx          | nxp-imx/imx-optee-os | BSD-2    |

Source repos are on GitHub. OP-TEE is included by default because `optee`
is in the NXP BSP's `MACHINE_FEATURES`; we remove it (D15).

Notes:
- The `imx-atf` recipe in `meta-freescale` fetches the same commit as our
  submodule (`af9eb2c17`), but then applies
  `0001-feat-imx952-support-full-system-power-control-option.patch` on
  top. Judging by its name it targets the i.MX952, but the TF-A that gets
  built is not exactly the submodule's contents (see Q13).
- The kernel recipe `linux-fslc-imx` sets `SRC_URI` directly. TF-A, U-Boot,
  `imx-mkimage` and OP-TEE set their source URL with `?=` (`ATF_SRC`,
  `UBOOT_SRC`, `IMX_MKIMAGE_SRC`, `OPTEE_OS_SRC`), so it can be replaced
  without editing `meta-freescale`.
- With the NXP BSP, `MACHINE_FEATURES` also includes `nxpiw612-sdio` and
  `nxpwifi-all-sdio`, which bring in `firmware-nxp-wifi`
  (`LicenseRef-Proprietary`). This is not covered by D1 and must be kept
  out (see step 4 of the build procedure).
- Both firmware archives can be downloaded from the NXP mirror
  (HTTP 200 on 2026-11-26).

### Dependencies, and references to `meta-imx`

- `imx-atf` refers to neither `meta-freescale`, `imx-manifest` nor
  `meta-imx`. It is a standalone source tree.
- `meta-freescale` depends on `imx-atf`: its `imx-atf_2.14.bb` recipe
  fetches https://github.com/nxp-imx/imx-atf at `af9eb2c17` (the
  submodule's commit, but fetched separately, not from the submodule). It
  only refers to `imx-manifest` in comments and in an NXP SCR text file.
  The only layer it needs is OE-core (`LAYERDEPENDS = "core"`). It does not
  need `meta-imx`, including for `IMX_DEFAULT_BSP = "nxp"`: `linux-fslc-imx`
  and `u-boot-imx` are its own recipes.
- `imx-manifest` depends on `meta-freescale`. Each release manifest pins it
  (`imx-6.18.37-2.1.0.xml`: branch `wrynose`, `ca31f33c5`). It refers to
  `imx-atf` only indirectly, through the layers.
- References to `meta-imx`:
  - `imx-manifest`: the release manifests list `meta-imx` (and, in the
    `_orangebox` variants, `meta-imx-orangebox`) as projects to download,
    and `README.md` mentions it. This is the problematic reference: an
    unmodified `repo sync` downloads it.
  - `meta-freescale`, `conf/fragments/bsp/nxp.conf`: an opt-in
    configuration fragment that says it "Requires a layer providing
    linux-imx and u-boot-imx (e.g. meta-imx)". It only takes effect if
    explicitly enabled. We will not enable it.
  - `meta-freescale`, `recipes-security/optee-imx/*-fslc-imx.inc` (5 files
    used by the `*.imx` OP-TEE recipes): their headers say they were
    "Copied from meta-imx/meta-imx-bsp/recipes-security/optee/...". All
    `meta-imx` release tags checked (`rel_imx_5.4.70_2.3.0` to
    `rel_imx_6.18.37_2.1.0`) have an NXP license file (`EULA.txt`, later
    `LICENSE.txt`) at the top level and no separate license for the
    metadata, so the license of this copied metadata is unclear. The NXP
    BSP for i.MX93 uses these files when `optee` is in `MACHINE_FEATURES`
    (the default), which is why we remove it (D15).
  - `meta-freescale`, comments only (not used by the i.MX93 build): a patch
    in `recipes-graphics/devil` "Taken from meta-imx", a note on a
    `imx-seco-libs` patch, a comment in `imx-base.inc`, and the NXP SCR
    text file `SCR/SCR-6.6.3-1.0.0.txt`.

### Shallow submodules

Tested by an agent on 2026-11-27 with a throwaway parent repo and the
`bitbake` (GitHub) and `meta-yocto` (git.yoctoproject.org) repos, pinned to
`yocto-6.0.2`, which is not the tip of their branches:

- `git submodule add --depth 1 -b <branch> …` fails ("'origin/2.18' is not
  a commit"). Cloning with `git clone --depth 1 --branch <tag>` first and
  then running `git submodule add <url> <path>` on the existing clone
  works.
- With `shallow = true` in `.gitmodules`:
  - `git clone --recurse-submodules` and
    `git submodule update --init --depth 1` give 1-commit clones.
  - A plain `git submodule update --init` makes a depth-1 clone of the
    remote's *default branch* and then fetches the pinned commit *with its
    full history* if it is not part of that clone (`bitbake`: 9533
    commits).
- `.gitmodules` has no setting that makes a plain `git submodule init` /
  `update` shallow in that case: the `branch` setting is ignored for the
  initial clone (tested again with the pin at the tip of a non-default
  branch, like `linux`: 9555 commits).
- `update = none` in `.gitmodules` makes a plain `git submodule update`
  and `git clone --recurse-submodules` skip the submodule ("Skipping
  submodule"). An explicit
  `git submodule update --init --depth 1 --checkout <path>` still works and
  gives a 1-commit clone. Without `--depth 1`, that command would fetch
  the full history (same mechanism as above; not tested separately).
- Both servers allow fetching a commit by its hash with `--depth 1`.

This matters for `linux`: the default branch of `Freescale/linux-fslc` is
`7.2.x+fslc`, so a plain `git submodule update --init` would download the
full history of `6.18-2.1.x-imx` (several GB). Hence `update = none` for
`linux` (D7).

## Build procedure

Incomplete: the distro depends on Q4, `meta-adtf` has only its fragment
so far (no `layer.conf` or `bitbake-setup` configuration yet), and only
step 1 has been run. Commands run from the root of this repo unless
stated otherwise.

**Layer set:** `bitbake` and `openembedded-core` at tag `yocto-6.0.2`
("wrynose", the revisions `imx-6.18.37-2.1.0.xml` pins), `meta-yocto` at
`yocto-6.0.2` for the `poky` distro (MIT, only if Q4 = poky),
`meta-freescale` on `wrynose` (D5), and `meta-adtf` (D8). No `meta-imx`,
`meta-nxp-*`, `meta-qt6`, `meta-browser` and so on. `meta-openembedded`
and `meta-arm` are not needed for a minimal image; they are only added if
parsing shows they are required.

**Linux source** (D9): after cloning this repo, get the `linux` submodule
with exactly this command (a plain `git submodule update --init` or
`git clone --recurse-submodules` skips it, see "Shallow submodules"):

```
git submodule update --init --depth 1 --checkout linux
```

Tested on a fresh clone of this repo on 2026-11-27: one commit at
`0eb3d176c`, 70 s, 500 MB of git data. That is more than the 290 MB of a
direct `git clone --depth 1 --branch 6.18-2.1.x-imx`, probably because
git first clones the remote's default branch (`7.2.x+fslc`) at depth 1 and
then fetches our commit, so it downloads two kernel snapshots.

**Directory layout** (D10): top directory `~/yocto-builds`, setup
directory `~/yocto-builds/imx93-frdm` with `layers/`, `build/` and
`config/`; downloads in `~/yocto-builds/.bitbake-setup-downloads` and
sstate in `~/yocto-builds/.sstate-cache`, shared by all setups.

1. **Get BitBake** (once per home directory, D16; done on 2026-11-27):

   ```
   mkdir -p ~/tools
   git clone https://github.com/openembedded/bitbake.git ~/tools/bitbake
   git -C ~/tools/bitbake checkout yocto-6.0.2
   ```

   In every new shell (or in `~/.bashrc`), put it first on `PATH`, then
   check that it is the one found and that it has the right version:

   ```
   export PATH="$HOME/tools/bitbake/bin:$PATH"
   which bitbake bitbake-setup  # expect ~/tools/bitbake/bin/... for both
   bitbake --version            # expect: BitBake Build Tool Core version 2.18.0
   git -C ~/tools/bitbake describe --tags   # expect: yocto-6.0.2
   ```

2. **Tell `bitbake-setup` where the top directory is** (once per person,
   stored in `~/.config/bitbake-setup/settings.conf`):

   ```
   bitbake-setup settings set --global default top-dir-prefix "$HOME"
   bitbake-setup settings set --global default top-dir-name yocto-builds
   ```

3. **Set up the layers and the build directory** (once; not yet tested):

   ```
   bitbake-setup init --non-interactive \
       meta-adtf/bitbake-setup/imx93-frdm.conf.json
   ```

   This clones the layers into `~/yocto-builds/imx93-frdm/layers`, writes
   `bblayers.conf`, and enables the fragment `adtf/board/imx93-frdm`.
   Then, in every new shell:

   ```
   source ~/yocto-builds/imx93-frdm/build/init-build-env
   which bitbake  # expect ~/yocto-builds/imx93-frdm/layers/bitbake/bin/bitbake
   ```

   This puts the setup's own BitBake copy (same commit as
   `~/tools/bitbake`) first on `PATH` and changes into the build directory.

4. **Configuration.** The shared configuration is committed in the
   fragment `meta-adtf/conf/fragments/board/imx93-frdm.conf` (D8), which
   step 3 enables.

   `rm_work` (`openembedded-core/meta/classes/rm_work.bbclass`) deletes
   each recipe's work directory (unpacked sources and build objects, but
   not its `temp/` logs) once the recipe is built. It saves tens of GB.
   Recipes listed in `RM_WORK_EXCLUDE` keep theirs; `externalsrc` adds its
   recipe there automatically, so the Linux build (D9) is kept.

   Per person, in `~/yocto-builds/site.conf`, below the `DL_DIR` and
   `SSTATE_DIR` lines that `bitbake-setup` writes there:

   ```
   BB_NUMBER_THREADS = "12"
   PARALLEL_MAKE = "-j 12"
   ```

5. **Accept the NXP EULA** for this build directory, only if you have read
   `~/yocto-builds/imx93-frdm/layers/meta-freescale/EULA` and accept it
   yourself (D6):

   ```
   bitbake-config-build enable-fragment freescale-layer/eula/accept-fsl-eula
   ```

   This changes only one file, the build directory's `conf/toolcfg.conf`
   (the default `--confpath` of `bitbake-config-build`): it adds the
   fragment's name to the `OE_FRAGMENTS += "…"` line, next to
   `adtf/board/imx93-frdm` from step 3. Nothing is downloaded or built.
   From then on, every BitBake run in this build directory parses
   `meta-freescale/conf/fragments/eula/accept-fsl-eula.conf`, which sets
   `ACCEPT_FSL_EULA = "1"` (`openembedded-core/meta/conf/bitbake.conf`
   includes `conf/toolcfg.conf` and then applies `addfragments`). To check
   and to undo:

   ```
   bitbake-getvar ACCEPT_FSL_EULA
   bitbake-config-build disable-fragment freescale-layer/eula/accept-fsl-eula
   ```

6. **Check before the long build**: parse, and compute the dependency
   graph:

   ```
   bitbake -p
   bitbake -g core-image-minimal
   ```

   From the result, list every recipe in the build together with its
   `LICENSE`. Confirm that the only `LicenseRef-Proprietary` recipes are
   `firmware-ele-imx` and `imx-boot-firmware-files`, and that the
   `INCOMPATIBLE_LICENSE` exception syntax works for them.

7. **Build** (D14), in `tmux` or with `nohup`, because it takes hours:

   ```
   bitbake core-image-minimal 2>&1 | tee build-core-image-minimal.log
   ```

8. **Review licenses after the build**: the rootfs's

   ```
   ~/yocto-builds/imx93-frdm/build/tmp/deploy/licenses/<image>/license.manifest
   ```

   and the recipes that went into `imx-boot`/`flash.bin`.

**Output:**

```
~/yocto-builds/imx93-frdm/build/tmp/deploy/images/imx93-11x11-lpddr4x-frdm/
```

containing `core-image-minimal-*.wic.zst` (+ `.bmap`) and the boot image
`imx-boot` / `flash.bin`. The path is `openembedded-core`'s default:
`TMPDIR ?= "${TOPDIR}/tmp"` (`TOPDIR` is the build directory),
`DEPLOY_DIR ?= "${TMPDIR}/deploy"` and
`DEPLOY_DIR_IMAGE ?= "${DEPLOY_DIR}/images/${MACHINE}"`
(`meta/conf/bitbake.conf`); neither `poky` nor our configuration changes
it. Getting the images onto the board is out of scope for now (D12).

**Using the `imx-atf` submodule:** until we change TF-A, the build can use
the recipe's own fetch of the same commit (plus its patch). Once we change
TF-A, `meta-adtf` points the recipe at the submodule (Q13).

## Open questions

Q4. **Distro:** `poky` (needs `meta-yocto`, well tested) or `nodistro`
    (OE-core only, fewer layers)? Proposal: `poky`.

Q5. **NXP BSP or mainline BSP?** Since D5, the NXP BSP is the only one
    `meta-freescale` sets up for this board, so using the mainline BSP
    would mean either our own machine configuration or going back to
    `master`. Both BSPs use `imx-atf` and the same two firmware packages,
    and both are GPL for U-Boot and the kernel. Proposal: use the NXP BSP.

Q13. **How to build TF-A from the `imx-atf` submodule:** `externalsrc` (as
     for Linux, D9; builds uncommitted changes; skips the recipe's patch)
     or replacing the source URL in a `.bbappend`
     (`ATF_SRC = "git://${ADTF_REPO_ROOT}/imx-atf;protocol=file"` plus
     `SRCREV`; builds only committed changes; applies the recipe's patch,
     which may conflict with our changes; needs our commits on the
     submodule's branch `lf_v2.14`, or `SRCBRANCH`/`nobranch=1` set)?
     With the second option, `SRCREV` could be read from the submodule at
     parse time, so the parent repo's submodule pointer is the only record
     of the commit.
