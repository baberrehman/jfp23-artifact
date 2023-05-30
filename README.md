# Artifact JFP 2023: Type Soundness with Unrestricted Merges

This repository contains artifact associated with JFP 2023 theoretical pearl.

1. `coq` folder contains the Coq formalization
2. `doc` folder contains a copy of the paper

## What does the artifact comprise?

This artifact contains the Coq formalization.

## Artifact Structure

The Coq formalization can be found in the folder `coq`. Description of each file in
`coq` folder is:

|  File         |   Description                                                                                  | Reference in paper |
| :------------ | :--------------------------------------------------------------------------------------------- | :----------------  |
| dunfield.v    | Dunfield's original system and a variant with switches                                         | Section 2,4        |
| syntax.v      | Types and subtyping of our system (λm)                                                         | Section 3          | 
| typing.v      | Type safety proofs of λm    | Discussed in section 5.1                                         | Section 3          |
| multi_step.v  | Multi-step reduction for Dunfield's system                                                     | Section 4          |
| equivalence.v | Soundness/completeness proofs of λm to Dunfield's system and two variants of Dunfield's system | Sections 2,3,4     |



Correspondence of important lemmas in paper and in artifact is:


|  Lemma in Paper  |   Coq file    |     Lemma(s) in Coq File     |
| :--------------- | :------------ | :--------------------------- |
| Theorem 1        | typing.v      | tred_preservation            |
| Theorem 2        | typing.v      | tred_progress                |
| Lemma 3          | typing.v      | getInTypeInv                 |
| Lemma 4          | typing.v      | dynSemanticsProgress         |
| Theorem 5        | typing.v      | preservation                 |
| Theorem 6        | typing.v      | progress                     |
| Lemma 7          | equivalence.v | dt_complete_our_system       |
| Lemma 8          | equivalence.v | dt_sound_our_system          |
| Lemma 9          | equivalence.v | dstep_sound_our_system       |


Moreover, the lemmas **dt_dt2_complete** and **dstep_dstep2_complete**
are the completeness lemmas for original Dunfield's system to a variant
with switches. These lemmas state that a variant of Dunfield's system with
switches is at least as expressive as original Dunfield's system.

## How to run?

### Dependencies

Artifact is compiled with **Coq version 8.13.2**. We recommend the same for the
sake of consistency. Detailed instructions of installing `Coq` are available
at: `https://coq.inria.fr/opam-using.html`.

Artifact also depends on an external library **Metalib**. Detailed installation
instructions of Metalib are available at: `https://github.com/plclub/metalib`.
**Recommended Metalib version is coq8.10**. This version compiles with Coq 8.13.2.

### Running the artifact

Clone the repo using command: `git clone https://github.com/baberrehman/jfp23-artifact.git`

We provide a `Makefile` in `coq` folder. Open a terminal in `coq` folder and
run `make` command. This command will compile all the Coq files. Reader may look into
each coq file to verify the claims using their preferred editor.

