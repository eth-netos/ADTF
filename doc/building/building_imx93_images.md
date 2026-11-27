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
- The `imx-atf` recipe in `meta-freescale` pins **exactly the commit our
  submodule is on** (`af9eb2c17`), so the default build uses the same TF-A
  source.
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

   No `meta-imx`, `meta-nxp-*`, `meta-qt6`, `meta-browser` and so on.
   `meta-openembedded` and `meta-arm` are not needed for a minimal image.
   They are only added if parsing shows they are required.
2. **Fetching layers.** Either as further git submodules of this repo, or
   with `repo` and our own MIT manifest derived from `imx-manifest` that
   lists only the layers above (see Q3).
3. **Directory layout:** the build directory (with `conf/` and `tmp/`) is
   `yocto-build/imx93-frdm` in this repo, ignored by `.gitignore` (D6).
   Downloads and sstate are shared between build directories and kept
   outside the repo: `~/yocto-cache/downloads` (`DL_DIR`) and
   `~/yocto-cache/sstate-cache` (`SSTATE_DIR`).
4. **`local.conf`** (sketch):

   ```
   MACHINE = "imx93-11x11-lpddr4x-frdm"
   DISTRO = "poky"
   DL_DIR = "/home/ubuntu/yocto-cache/downloads"
   SSTATE_DIR = "/home/ubuntu/yocto-cache/sstate-cache"
   BB_NUMBER_THREADS = "12"
   PARALLEL_MAKE = "-j 12"
   INHERIT += "rm_work"
   MACHINE_FEATURES:remove = "nxpiw612-sdio nxpwifi-all-sdio"
   INCOMPATIBLE_LICENSE = "LicenseRef-Proprietary"
   # plus exceptions for exactly the two firmware recipes from D1
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

Using the `imx-atf` submodule: the first build uses the recipe's own fetch
of the identical commit. Once we change TF-A, we point the recipe at the
submodule (e.g. with `externalsrc` or a `.bbappend` that sets
`SRC_URI`/`SRCREV`).

## Build instructions

Incomplete: the layer checkout depends on Q3 and the distro on Q4, and
none of this has been run yet. Below, `$LAYERS` is the directory that holds
the checkouts of `bitbake`, `openembedded-core` and `meta-yocto` (not yet
decided, see Q3). All commands run from the root of this repo.

Set up the build directory (once). Because `/opt/bitbake` is on `PATH` and
is the wrong BitBake version, `oe-init-build-env` must be used, which puts
`$LAYERS/bitbake/bin` first:

```
source $LAYERS/openembedded-core/oe-init-build-env yocto-build/imx93-frdm
bitbake-layers add-layer ../../meta-freescale
bitbake-layers add-layer $LAYERS/meta-yocto/meta-poky   # only for poky, Q4
```

`oe-init-build-env` changes into the build directory. In a new shell, run
the `source` line again to get back into it. Then edit `conf/local.conf` as
in step 4 of the proposed build procedure.

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

Q3. **How to fetch the other layers:** git submodules (consistent with the
    rest of this repo, recorded in git history) or `repo` with our own
    trimmed manifest? Proposal: submodules.

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
