#!/usr/bin/env python3
"""Builds TF-A's BL31 for the i.MX 93 in imx-atf/build/imx93/release, with
the Arm GNU Toolchain pinned in src/toolchain/arm-gnu-toolchain.version.

The toolchain is found by the prefix in the environment variable
CROSS_COMPILE (default: aarch64-none-elf-), as in TF-A's build."""

import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
IMX_ATF = ROOT / "imx-atf"
BUILD_DIR = IMX_ATF / "build" / "imx93" / "release"
VERSION_FILE = ROOT / "src" / "toolchain" / "arm-gnu-toolchain.version"


def cross_compile():
    return os.environ.get("CROSS_COMPILE", "aarch64-none-elf-")


def tool(name):
    return cross_compile() + name


def first_line(cmd):
    try:
        out = subprocess.run(cmd, check=True, capture_output=True,
                             text=True).stdout
    except (OSError, subprocess.CalledProcessError) as e:
        sys.exit(f"error: cannot run {cmd[0]}: {e}")
    return out.splitlines()[0]


def check_toolchain():
    """Exits with an error unless gcc and objdump are the pinned versions."""
    expected = VERSION_FILE.read_text().splitlines()
    actual = [first_line([tool("gcc"), "--version"]),
              first_line([tool("objdump"), "--version"])]
    if actual != expected:
        rel = VERSION_FILE.relative_to(ROOT)
        sys.exit(
            f"error: the toolchain does not match {rel}:\n"
            f"  expected: {expected}\n  found:    {actual}\n"
            f"Either install the pinned Arm GNU Toolchain (and set "
            f"CROSS_COMPILE), or update {rel} and regenerate the listings "
            f"with src/scripts/atf-listings.py.")


def build():
    """Checks the toolchain and builds BL31 incrementally."""
    check_toolchain()
    subprocess.run(["make", f"CROSS_COMPILE={cross_compile()}",
                    "PLAT=imx93", "bl31"], cwd=IMX_ATF, check=True,
                   stdout=subprocess.DEVNULL)


if __name__ == "__main__":
    build()
