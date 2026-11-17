import CliqueNandBound.UndirectedGraph
import CliqueNandBound.NandCircuit

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/


/-- Property that a NAND circuit correctly detects all `k`-vertex cliques. -/
def cliqueDetectorCircuit {n : ℕ} (k : Fin (n + 1)) {numGates : ℕ+}
    (circuit : NandCircuit (numGraphEdges n) numGates) : Prop :=
  ∀ G : UndirectedGraphEncoding n,
    hasClique n k G ↔ evalCircuit circuit G.fn

/-- There exists a `k`-clique-detecting circuit of a given size. -/
def existsCliqueDetectorCircuit (n : ℕ) (k : Fin (n + 1)) (numGates : ℕ+) : Prop :=
  ∃ circuit : NandCircuit (numGraphEdges n) numGates,
    cliqueDetectorCircuit k circuit

/- A pretty minimal example. -/
/-
theorem exists_circuit_4_3_5 : existsCliqueDetectorCircuit 4 3 5 := sorry
-/

/-- There does not exist a `k`-clique-detecting circuit of a given size. -/
def cliqueLowerBound (n : ℕ) (k : Fin (n + 1)) (numGates : ℕ+) : Prop :=
  ¬ existsCliqueDetectorCircuit n k numGates

/- Another tiny example. -/
/-
theorem cliqueLowerBound_4_3_4 : cliqueLowerBound 4 3 4 := sorry
-/
