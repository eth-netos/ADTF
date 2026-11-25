FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

# ---- system, Yocto, i.MX93 build, and devboard packages ----
RUN apt-get update \
 && apt-get install --no-install-recommends -y \
      cbmc cloc poppler-utils racket z3 \
      less nano emacs-nox time \
      libgmp-dev opam pkg-config cmake clang \
      build-essential chrpath cpio debianutils diffstat file gawk gcc git \
      iputils-ping libacl1 locales python3 python3-git python3-jinja2 \
      python3-pexpect python3-pip python3-subunit repo socat texinfo \
      unzip wget xz-utils zstd lz4 \
      bc bison bmap-tools ca-certificates crossbuild-essential-arm64 curl \
      device-tree-compiler flex gnupg libcrypt-dev libssl-dev libusb-1.0-0 \
      minicom picocom python3-cryptography python3-dev python3-pyelftools \
      python3-serial python3-setuptools rsync swig u-boot-tools \
 && locale-gen en_US.UTF-8 \
 && rm -rf /var/lib/apt/lists/* \
 && raco setup --fail-fast --no-docs \
 && raco pkg install --scope installation --fail-fast --auto --no-docs rosette

# ---- Rust, Elan/Lake (no toolchain), BitBake, uuu, and VS Code CLI ----
RUN curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs \
      | RUSTUP_HOME=/usr/local/rustup CARGO_HOME=/usr/local/cargo \
          sh -s -- -y --no-modify-path --default-toolchain stable \
          --component rustfmt --target aarch64-unknown-linux-gnu \
 && chmod -R a+rX /usr/local/rustup /usr/local/cargo \
 && curl --proto '=https' --tlsv1.2 -fsSL https://elan.lean-lang.org/elan-init.sh \
      | ELAN_HOME=/usr/local/elan \
          sh -s -- -y --no-modify-path --default-toolchain none \
 && chmod -R a+rX /usr/local/elan \
 && git clone https://git.openembedded.org/bitbake /opt/bitbake \
 && curl -fsSLo /usr/local/bin/uuu \
      "https://github.com/nxp-imx/mfgtools/releases/latest/download/uuu" \
 && chmod +x /usr/local/bin/uuu \
 && curl -fsSLo /tmp/vscode-cli.tar.gz \
      "https://code.visualstudio.com/sha/download?build=stable&os=cli-alpine-x64" \
 && tar -xzf /tmp/vscode-cli.tar.gz -C /usr/local/bin code \
 && rm /tmp/vscode-cli.tar.gz

# ---- runtime environment for all users and shells ----
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/home/ubuntu/.cargo \
    LANG=en_US.UTF-8 \
    LC_ALL=en_US.UTF-8 \
    PATH=/home/ubuntu/.local/bin:/home/ubuntu/.cargo/bin:/home/ubuntu/.elan/bin:/usr/local/cargo/bin:/usr/local/elan/bin:/opt/bitbake/bin:${PATH}

RUN echo "export PATH=\"$PATH\"" > /etc/profile.d/docker-path.sh

USER ubuntu
WORKDIR /home/ubuntu
