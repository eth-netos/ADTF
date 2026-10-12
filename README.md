# ADTF: Agentic Development of Trustworthy Firmware

There are two kinds of tasks required to develop trustworthy systems software that used to be very-time consuming:

* Figuring out how to build firmware and software and getting it to run on real hardware
* Writing formal proofs

If we give an LLM agent access to an SoC so that it can autonomously boot many different images that it wrote and compiled, and give it access to a proof checker so that it can autonomously obtain feedback on whether its proofs are correct, these tasks now become orders of magnitude less time-consuming for humans.

Unlike firmware like ATF, which stands for Arm Trust*ed* Firmware, our firmware will be Trust*worthy*, because it will be verified using the Lean proof checker.

We will connect an imx93 to an Enzian blade and give Claude the ability to compile and run boot images on it. We will start with Joshua's setup and ask the agent to simplify it as much as possible.

The imx93 has no SMMU, so the TRDC needs to guarantee memory protection from devices.

Goal: Protect Linux from its own driver bugs.

Scenario: Linux driver bug picks bad physical page address that it hands to the USB controller, so a malicious USB device can overwrite Linux's memory, eg its kernel page tables, in arbitrary ways.

Solution: Use the TRDC to create a region that is exclusively used for DMA from devices, and block USB controller and other devices (using TRDC config) to write anywhere else. Needs cooperation from Linux: If Linux picks default addresses in its own region to hand to the USB controller, the TRDC will block them.

https://github.com/torvalds/linux/blob/master/Documentation/core-api/dma-api-howto.rst

To make the firmware trustworthy, verify it in Lean, at the assembly level, using Kraken AArch64 semantics.
To model the platform aspects outside the ISA spec scope, use a Lean translation of the imx93 Sockeye model.
