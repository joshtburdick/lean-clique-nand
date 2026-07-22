import CliqueNandBound.UndirectedGraph
import CliqueNandBound.NandCircuit

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/


/- Property that a NAND circuit correctly detects all k-vertex cliques. -/
def cliqueDetectorCircuit (n : Nat) (k : Fin (n.succ)) (num_gates : ℕ+)
(circuit : NandCircuit (trapezoid_size n 0) num_gates) : Prop :=
  ∀ (G : UndirectedGraphEncoding n), hasClique n k G
  ↔ eval_circuit (trapezoid_size n 0) num_gates circuit G.fn

/- There exists a clique-detecting circuit of a given size. -/
def existsCliqueDetectorCircuit (n : Nat) (k : Fin (n.succ)) (num_gates : ℕ+) : Prop :=
  ∃ (circuit : NandCircuit (trapezoid_size n 0) num_gates),
  cliqueDetectorCircuit n k num_gates circuit

/- A pretty minimal example. -/
/-
theorem exists_circuit_4_3_5 : existsCliqueDetectorCircuit 4 3 5 := sorry
-/

/- There does not exist a clique-detecting circuit of a given size. -/
def cliqueLowerBound (n : Nat) (k : Fin (n.succ)) (num_gates : ℕ+) : Prop :=
  ¬ (existsCliqueDetectorCircuit n k num_gates)

/- Another tiny example. -/
/-
theorem cliqueLowerBound_4_3_4 : cliqueLowerBound 4 3 4 := sorry
-/
