# Building Linux images for the FRDM i.MX93 board

Living planning document: decisions, verified facts, the proposed build
procedure, and open questions. Nothing has been built yet.

Status as of 2026-11-26: planning, no build started.

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
    nor any agent may modify these files. (See also Q6 about packaging.)

D2. **No other software under the NXP Software License Agreement** (or any
    other proprietary license) goes into the image or the build, apart from
    the two firmware packages of D1.

D3. **`meta-imx` is not used.** Its release is distributed under the NXP
    Software License Agreement (`LICENSE.txt` and
    `SCR-6.18.37-2.1.0.txt` in `meta-imx` tag `rel_imx_6.18.37_2.1.0`).
    `meta-freescale` (MIT metadata) is used instead.

D4. **Submodules in this repo** (added by the human project owner):

- `imx-atf`: https://github.com/nxp-imx/imx-atf, branch `lf_v2.14`,
  commit `af9eb2c17` (BSD-3-Clause).
- `meta-freescale`: https://github.com/Freescale/meta-freescale,
  branch `wrynose`, commit `89e6e24b5` (MIT metadata). See D5.
- `imx-manifest`: https://github.com/nxp-imx/imx-manifest, branch
  `imx-linux-wrynose`, commit `66a5b81` (MIT).

D5. **`meta-freescale` follows its `wrynose` branch** (resolves Q2),
    matching `openembedded-core` wrynose (Yocto 6.0). Switched on
    2026-11-26 from `master` `fe15edb0a` to `wrynose` `89e6e24b5`, and
    recorded as `branch = wrynose` in `.gitmodules`. `89e6e24b5`
    contains the commit `ca31f33c5` that `imx-6.18.37-2.1.0.xml` pins, plus
    596 later backport commits.

D6. **The NXP EULA is never accepted in this repository** (resolves Q1).
    Each person who builds reads `meta-freescale/EULA` and decides for
    themselves. If they accept, they enable the `meta-freescale` fragment
    `freescale-layer/eula/accept-fsl-eula` in their own build directory
    (step 1 of "Build instructions"). Nothing committed to this
    repo may set `ACCEPT_FSL_EULA`, enable that fragment, or record anyone's
    acceptance. Agents never enable the fragment.
    `bitbake-config-build enable-fragment` writes only
    `<build-dir>/conf/toolcfg.conf` (its default `--confpath`, which
    `openembedded-core/meta/conf/bitbake.conf` includes). The build
    directory is `yocto-build/` in this repo, which `.gitignore` excludes,
    so the acceptance cannot be committed by accident.
    Two consequences of how `meta-freescale/classes/fsl-eula-unpack.bbclass`
    checks `ACCEPT_FSL_EULA`: the check is in `do_unpack`, so the NXP
    archives are already *downloaded* (`do_fetch`) before acceptance is
    checked. And the `firmware-imx` archive holds many other blobs (VPU,
    SDMA, HDMI, EPDC, …) that get unpacked under the same EULA, even though
    only the DDR files are installed.

D7. **Which repos are submodules** (resolves Q3). The human project owner
adds and removes submodules; agents only propose the commands. All
paths are relative to the repo root.

- **Source code we modify:** submodule, built through an override in
  `meta-adtf` (D8): `imx-atf`, `linux`.
- **Layers and BitBake, unmodified:** submodule, only to pin the exact
  version: `bitbake`, `openembedded-core`, `meta-yocto` (if poky, Q4),
  `meta-freescale`.
- **Recipe sources we don't modify:** downloaded by BitBake: U-Boot,
  `imx-mkimage`, OP-TEE, the firmware, GCC, BusyBox and so on.
- **Reference only:** not a submodule: `imx-manifest`.

Layers have to be on disk because BitBake reads them from local
directories and never downloads them. Submodules (rather than `repo` or
`bitbake-setup`) record in each parent commit which layer versions it
was tested with. `imx-manifest` is not read by BitBake at all; we only
use it as a reference for which versions go together, which is recorded
in this document (`imx-6.18.37-2.1.0.xml`, commit `66a5b81`).
Submodules that are large or only needed for building are marked
`shallow = true` in `.gitmodules`, and `linux` also gets `update = none`
(see "Submodule commands" for why).

D8. **Our own layer `meta-adtf/`** at the repo root holds everything we
change about the build, so that `meta-freescale` and the other layers
stay unmodified:

```
meta-adtf/
  conf/layer.conf                        # declares the layer
  conf/fragments/board/imx93-frdm.conf   # committed build config
  recipes-bsp/imx-atf/imx-atf_%.bbappend
  recipes-kernel/linux/linux-fslc-imx_%.bbappend
```

- `.bbappend` files point recipes at our submodules.
- The fragment `adtf/board/imx93-frdm` holds the build configuration
  that everyone shares: `MACHINE`, `DISTRO`, the license policy
  (`INCOMPATIBLE_LICENSE` and its two exceptions from D1), and removing
  the Wi-Fi machine features (and `optee`, if Q12 goes that way).
- Only per-person settings live in the ignored build directory:
  thread counts and cache paths in `conf/local.conf`, and the person's
  own EULA acceptance in `conf/toolcfg.conf` (D6).
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
`DL_DIR`, which a `git://…;protocol=file` URL would create. (Not yet
tested.)

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

Source repos are on GitHub. OP-TEE is included because `optee` is in the
NXP BSP's `MACHINE_FEATURES`.

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

### Dependencies between the submodules, and references to `meta-imx`

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
    metadata, so the license of this copied metadata is unclear (see Q12).
    The NXP BSP for i.MX93 uses these files when `optee` is in
    `MACHINE_FEATURES` (the default).
  - `meta-freescale`, comments only (not used by the i.MX93 build): a patch
    in `recipes-graphics/devil` "Taken from meta-imx", a note on a
    `imx-seco-libs` patch, a comment in `imx-base.inc`, and the NXP SCR
    text file `SCR/SCR-6.6.3-1.0.0.txt`.

### How the tools fit together

- **BitBake** is the build engine: it parses configuration and recipes
  from the layers listed in `conf/bblayers.conf` (local directories),
  builds a task graph, runs the tasks in parallel and reuses earlier
  results from the sstate cache. Recipe tasks (`do_fetch`) download source
  code; layers themselves are never downloaded by BitBake.
- **`repo`** (Google's multi-repository tool) only checks out git
  repositories listed in a manifest XML such as `imx-manifest`'s. It knows
  nothing about BitBake, and BitBake does not know about it. NXP uses it to
  put the right layer versions on disk. **`bitbake-setup`** (in
  `bitbake/bin` at `yocto-6.0.2`) does the same from a JSON configuration.
  We use submodules instead (D7).
- `oe-init-build-env` finds BitBake at `openembedded-core/bitbake` or, if
  that does not exist, `openembedded-core/../bitbake`
  (`scripts/oe-buildenv-internal`). With both as submodules at the repo
  root, the second case applies.

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
- `update = none` in `.gitmodules` makes a plain `git submodule update`
  skip the submodule ("Skipping submodule"). An explicit
  `git submodule update --init --depth 1 --checkout <path>` still works and
  gives a 1-commit clone.
- Both servers allow fetching a commit by its hash with `--depth 1`.

This matters for `linux`: the default branch of `Freescale/linux-fslc` is
`7.2.x+fslc`, so a plain `git submodule update --init` would download the
full history of `6.18-2.1.x-imx` (several GB). Hence `update = none` for
`linux` (D7).

### Container and host tools

The container is built from `setup/adtf2-sandbox/docker/Dockerfile`.

- All Yocto host packages are present: gcc 13.3, make 4.3, git 2.43,
  tar 1.35, Python 3.12, chrpath, cpio, diffstat, gawk, socat, texinfo,
  wget, xz, zstd, lz4, GitPython, jinja2, pexpect, subunit. The locale
  `en_US.UTF-8` is set. The `repo` launcher 2.36 is installed.
  `bmap-tools` and `uuu` are installed for flashing.
- **Unprivileged user namespaces do not work** (`unshare -Urn` returns
  EPERM, because of `--cap-drop ALL`, Docker's seccomp profile, and the
  host's `apparmor_restrict_unprivileged_userns=1`). OE's `check_userns`
  sanity check still passes, because `unshare` fails cleanly. The only
  effect is that BitBake cannot cut tasks other than `do_fetch` off from
  the network. That's a reproducibility risk, not a blocker.
- `/opt/bitbake` (BitBake 2.20, upstream master) is too new for Yocto 6.0
  "wrynose". The build uses the BitBake revision that matches
  `openembedded-core`. `oe-init-build-env` puts it first on `PATH`.
- Read-only root filesystem: only `/home/ubuntu`, `/tmp` and `/var/tmp` are
  writable. All build directories must be under `/home/ubuntu`.
- No direct access to the board from inside the container (no USB or
  serial devices). Flashing happens outside the container (see Q8).

### Resources

- CPU: 16 cores. RAM: 24 GiB (cgroup limit; `free` shows the host's
  31 GiB). No swap. PID limit: 4096.
- Disk: `/home/ubuntu` is a 1 TB sparse ext4 image with about 956 GB free
  inside. How much space the host disk really has left is not visible from
  inside the container (see Q9).

Estimate for `core-image-minimal` from scratch:
- Disk: about 50 to 80 GB without `rm_work` (about 20 to 30 GB with
  `INHERIT += "rm_work"`), plus about 10 GB downloads and about 10 GB
  sstate cache.
- Time: about 1 to 2.5 hours on 16 cores, depending on network and disk
  speed. Rebuilds from sstate take minutes.
- RAM: 24 GiB is enough for 16 parallel tasks for this image, but not with
  much to spare if large Lean jobs run at the same time. The plan caps
  parallelism (see "Build procedure").

Conclusion: the resources should be enough.

## Proposed build procedure

Not yet executed. Pending answers to the open questions.

1. **Layer set.** Use only:
   - `bitbake` and `openembedded-core`, at the revisions from
     `imx-manifest/imx-6.18.37-2.1.0.xml` (tag `yocto-6.0.2`, "wrynose").
   - `meta-yocto`, at tag `yocto-6.0.2`, for the `poky` distro (MIT).
     Optional (see Q4).
   - `meta-freescale`, branch `wrynose` (D5).
   - `meta-adtf`, our own layer (D8).

   No `meta-imx`, `meta-nxp-*`, `meta-qt6`, `meta-browser` and so on.
   `meta-openembedded` and `meta-arm` are not needed for a minimal image.
   They are only added if parsing shows they are required.
2. **Fetching layers:** as git submodules of this repo (D7), see
   "Submodule commands".
3. **Directory layout:** the build directory (with `conf/` and `tmp/`) is
   `yocto-build/imx93-frdm` in this repo, ignored by `.gitignore` (D6).
   Downloads and sstate are shared between build directories and kept
   outside the repo: `~/yocto-cache/downloads` (`DL_DIR`) and
   `~/yocto-cache/sstate-cache` (`SSTATE_DIR`).
4. **Configuration** (sketch). Committed, in the fragment
   `meta-adtf/conf/fragments/board/imx93-frdm.conf` (D8):

   ```
   MACHINE = "imx93-11x11-lpddr4x-frdm"
   DISTRO = "poky"
   MACHINE_FEATURES:remove = "nxpiw612-sdio nxpwifi-all-sdio"
   INCOMPATIBLE_LICENSE = "LicenseRef-Proprietary"
   # plus exceptions for exactly the two firmware recipes from D1
   INHERIT += "rm_work"
   ```

   Per person, in the build directory's `conf/local.conf`:

   ```
   DL_DIR = "/home/ubuntu/yocto-cache/downloads"
   SSTATE_DIR = "/home/ubuntu/yocto-cache/sstate-cache"
   BB_NUMBER_THREADS = "12"
   PARALLEL_MAKE = "-j 12"
   ```
5. **Check before the long build.** Run a parse and dependency-graph pass
   (`bitbake -p`, `bitbake -g core-image-minimal`), and from it list every
   recipe in the build together with its `LICENSE`. Confirm that the only
   `LicenseRef-Proprietary` recipes are `firmware-ele-imx` and
   `imx-boot-firmware-files`, and that the `INCOMPATIBLE_LICENSE`
   exception syntax works for them.
6. **Build** `core-image-minimal`. Do it in `tmux`/`nohup` with a log,
   because it takes hours.
7. **Review licenses after the build:**
   `tmp/deploy/licenses/<image>/license.manifest` for the rootfs, and the
   recipes that went into `imx-boot`/`flash.bin`.
8. **Output:** `tmp/deploy/images/imx93-11x11-lpddr4x-frdm/`, containing
   `core-image-minimal-*.wic.zst` (+ `.bmap`) and the boot image
   `imx-boot` / `flash.bin`. Flash to microSD with `bmaptool`, or to eMMC
   with `uuu`, from outside the container (Q8).

Using the `imx-atf` submodule: until we change TF-A, the build can use the
recipe's own fetch of the same commit (plus its patch). Once we change
TF-A, `meta-adtf` points the recipe at the submodule (Q13).

## Submodule commands

Not yet run. The human project owner runs these (D7). All from the repo
root.

Add the layers and BitBake, shallow, at `yocto-6.0.2`:

```
git clone --depth 1 --branch yocto-6.0.2 \
    https://github.com/openembedded/bitbake.git bitbake
git submodule add https://github.com/openembedded/bitbake.git bitbake
git config -f .gitmodules submodule.bitbake.branch 2.18

git clone --depth 1 --branch yocto-6.0.2 \
    https://github.com/openembedded/openembedded-core.git openembedded-core
git submodule add https://github.com/openembedded/openembedded-core.git \
    openembedded-core
git config -f .gitmodules submodule.openembedded-core.branch wrynose

# only for DISTRO = "poky" (Q4)
git clone --depth 1 --branch yocto-6.0.2 \
    https://git.yoctoproject.org/meta-yocto meta-yocto
git submodule add https://git.yoctoproject.org/meta-yocto meta-yocto
git config -f .gitmodules submodule.meta-yocto.branch wrynose

for s in bitbake openembedded-core meta-yocto; do
    git config -f .gitmodules submodule.$s.shallow true
done
```

Add Linux, shallow, and protected against accidental deep clones:

```
git clone --depth 1 --branch 6.18-2.1.x-imx \
    https://github.com/Freescale/linux-fslc.git linux
git -C linux rev-parse HEAD   # expect 0eb3d176cb8c8ea0d6f6cbb0d39ea4699246b144
git submodule add https://github.com/Freescale/linux-fslc.git linux
git config -f .gitmodules submodule.linux.branch 6.18-2.1.x-imx
git config -f .gitmodules submodule.linux.shallow true
git config -f .gitmodules submodule.linux.update none
```

If the branch has moved past `0eb3d176c` by then, check out the recipe's
commit instead: `git -C linux fetch --depth 1 origin <commit>` and
`git -C linux checkout <commit>`.

Remove `imx-manifest` (D7):

```
git submodule deinit imx-manifest
git rm imx-manifest
rm -rf .git/modules/imx-manifest
```

Then commit `.gitmodules` and the new and removed submodule paths together.

How other people get the submodules after cloning this repo:

```
git submodule update --init --depth 1
git submodule update --init --depth 1 --checkout linux   # only if needed
```

## Build instructions

Incomplete: the distro depends on Q4, `meta-adtf` does not exist yet, and
none of this has been run yet. All commands run from the root of this repo.

Set up the build directory (once). Because `/opt/bitbake` is on `PATH` and
is the wrong BitBake version, `oe-init-build-env` must be used, which puts
`bitbake/bin` first:

```
source openembedded-core/oe-init-build-env yocto-build/imx93-frdm
bitbake-layers add-layer ../../meta-freescale
bitbake-layers add-layer ../../meta-yocto/meta-poky   # only for poky, Q4
bitbake-layers add-layer ../../meta-adtf
bitbake-config-build enable-fragment adtf/board/imx93-frdm
```

`oe-init-build-env` changes into the build directory. In a new shell, run
the `source` line again to get back into it. Then put the per-person
settings from step 4 of the proposed build procedure into
`conf/local.conf`.

1. Accept the NXP EULA for this build directory, only if you have read
   `meta-freescale/EULA` and accept it yourself (D6):

   ```
   bitbake-config-build enable-fragment freescale-layer/eula/accept-fsl-eula
   ```

2. Check, before the long build (step 5 of the proposed procedure):

   ```
   bitbake -p
   bitbake -g core-image-minimal
   ```

3. Build, in `tmux` or with `nohup`, because it takes hours:

   ```
   bitbake core-image-minimal 2>&1 | tee build-core-image-minimal.log
   ```

The images end up in `tmp/deploy/images/imx93-11x11-lpddr4x-frdm/`.

## Open questions

Q4. **Distro:** `poky` (needs `meta-yocto`, well tested) or `nodistro`
    (OE-core only, fewer layers)? Proposal: `poky`.

Q5. **NXP BSP or mainline BSP?** Since D5, the NXP BSP is the only one
    `meta-freescale` sets up for this board, so using the mainline BSP
    would mean either our own machine configuration or going back to
    `master`. Both BSPs use `imx-atf` and the same two firmware packages,
    and both are GPL for U-Boot and the kernel. Proposal: use the NXP BSP.
    Also: keep OP-TEE (BSD-2) or remove `optee` from `MACHINE_FEATURES` for
    a simpler boot chain? (See also Q12.)

Q6. **Does packaging count as modifying the firmware?** `imx-mkimage` (or
    binman) pads and concatenates the DDR firmware files and embeds the
    ELE container into `flash.bin`. The files' contents stay unchanged.
    Proposal: treat this as packaging, not modification, under D1.

Q7. **Board details:** which FRDM-IMX93 revision and silicon revision?
    `meta-freescale` assumes `IMX_SOC_REV = "A1"`
    (`mx93a1-ahab-container.img`). Boot from microSD or eMMC?

Q8. **Flashing:** the container has no USB/serial access to the board.
    Copy the images to the laptop or host and flash there (`bmaptool` or
    `uuu`)?

Q9. **Host disk space:** is there at least about 150 GB of real free space
    on the host disk behind `~/docker-volumes/adtf2-volume.img`?

Q10. **Network isolation:** accept that BitBake tasks are not cut off from
     the network (because user namespaces are unavailable), or change the
     container setup?

Q11. **Image contents:** is `core-image-minimal` (BusyBox, serial console
     on `ttyLP0` at 115200) enough as the "simple image", or are packages
     like `openssh` or `dropbear` needed?

Q12. **OP-TEE recipe files copied from `meta-imx`.** Five `.inc` files in
     `meta-freescale/recipes-security/optee-imx/` say in their headers that
     they were copied from `meta-imx`, whose releases are distributed under
     the NXP license. OP-TEE itself is BSD-2-Clause; the question is only
     about the license of this build metadata. Options: (a) remove `optee`
     from `MACHINE_FEATURES`, so these files are not used at all;
     (b) accept them as part of `meta-freescale` (MIT); (c) ask the
     `meta-freescale` maintainers about their provenance. Proposal: (a) for
     the first image.

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
