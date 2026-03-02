# LeanQEC
Proving quantum error correction code properties by Lean


# Design

We gradually formalize all famous quantum error correction theories in Lean. The goal is to formalize the correctness of logical operation, magic state distillation, fault-tolerance, threshold across all different compilation scheme and error correction code structure.


# Formalize stabilizer formalism


The first step is the formalize the stabilizer formalism. The stabilizer formalism is described by a group of Pauli stablizers. 


# Formalize decoder property


# Formalize threshold theorem


# Proof of code distance

We formalize the proof of code distance.


# QStab: Fault-tolerance verification

We formalize the operational semantics of stabilizer code syndrome extraction and prove fault-tolerance via invariants. The framework models an adversarial error model with four error types (Type 0/I/II/III), deterministic stabilizer measurement, and a finite error budget. Key results include the error propagation bound, round inconsistency bound, syndrome correctness, and the main fault-tolerance theorem. See [QStab/README.md](QStab/README.md) for details.





