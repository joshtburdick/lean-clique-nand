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
  ↔ eval_circuit (trapezoid_size n 0) num_gates circuit G.bitvec

/- There exists a clique-detecting circuit of a given size. -/
def existsCliqueDetectorCircuit (n : Nat) (k : Fin (n.succ)) (num_gates : ℕ+) : Prop :=
  ∃ (circuit : NandCircuit (trapezoid_size n 0) num_gates),
  cliqueDetectorCircuit n k num_gates circuit

/- A pretty minimal example. -/
theorem exists_circuit_3_3_2 : existsCliqueDetectorCircuit 3 3 2 := sorry


/- The minimum number of gates required to detect all k-vertex cliques in n-vertex graphs. -/
/- FIXME not working
def minGatesForCliqueDetector (n : Nat) (k : Fin (n.succ)) : ℕ+ :=
  Nat.find (fun n_gates => existsCliqueDetectorCircuit n k n_gates)
-/
