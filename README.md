
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
![Build Status](https://github.com/Anastasia-Labs/coq-uplc/actions/workflows/ci.yaml/badge.svg?branch=main)

# The `coq-uplc` Library

The `coq-uplc` library provides a Coq-based implementation of the Cardano CEK machine—the virtual
machine responsible for evaluating UPLC programs (validators), which serve as the on-chain
components of Cardano smart contracts.

---

## What is UPLC (Untyped Plutus Core)?

Cardano validators, the backbone of its smart contract ecosystem, can be written in various
high-level languages and dialects, such as:

- **Plutus**, **Plutarch**, **Aiken**, **Marlowe**, **Helios**, **OpShin**, and **plu-ts**.

To function on the Cardano blockchain, every validator must be compiled into **UPLC (Untyped Plutus
Core)**. This is crucial for Cardano nodes to evaluate and authorize transactions associated with
these validators.

Validators ensure the security of Cardano's protocols, safeguarding the transmission and storage of
funds. However, vulnerabilities in their implementation can lead to catastrophic outcomes, such as
funds being stolen, lost, or permanently locked.

---

## Why Use Coq?

**Coq** is a state-of-the-art interactive theorem prover renowned for its reliability and utility in
critical domains, including compiler construction. Built on first-order mathematical logic, type
theory, and the calculus of constructions, Coq is well-suited for defining and proving properties of
validator programs.

### Key Features of Coq:

- **Formal Verification**: ensures the mathematical soundness of validators.
- **Automation with Tactics**: simplifies proof scripts, aiding in proof maintenance and enabling
  efficient updates to existing validators.

Using Coq enhances confidence in the correctness of validator implementations, reducing risks in
Cardano's ecosystem.

---

## Building the Library

### Recommended: Build with Nix

1. Install [Nix](https://nixos.org/download/) and enable
   [Nix flakes](https://nixos.wiki/wiki/flakes).
2. In the project root, run:
   ```bash
   make shell
   ```
   This starts a development shell.
3. Build the library with:
   ```bash
   make build
   ```

### Alternative: Build with Opam

1. Install [Opam](https://opam.ocaml.org/doc/Install.html) and initialize it:
   ```bash
   opam init
   ```
2. Install the required dependencies:
   ```bash
   opam install coq dune
   ```
3. Build the library by running:
   ```bash
   opam exec -- dune build
   ```

---

## Using the library

Under construction...
