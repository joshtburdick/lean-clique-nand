import CliqueNandBound.CliqueNandCircuit

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/-!
# Optimal NAND-gate bound for 3-cliques on 3-vertex graphs

For `n = 3` and `k = 3`, detecting a 3-clique is computing the 3-input AND of the
3 edge bits. We prove that:
1. 1 unbounded fan-in NAND gate is insufficient (`cliqueLowerBound 3 3 1`).
2. 2 unbounded fan-in NAND gates suffice (`existsCliqueDetectorCircuit 3 3 2`).
-/

private def triangleSdv : SortedDistinctVector 3 3 where
  elements := #v[0, 1, 2]
  distinct := by decide

/-- No 1-gate unbounded fan-in NAND circuit can detect 3-cliques on 3-vertex graphs. -/
theorem cliqueLowerBound_3_3_1 : cliqueLowerBound 3 3 1 := by
  rintro ⟨circuit, hDet⟩
  let k3 : UndirectedGraphEncoding 3 := ⟨fun _ => true⟩
  have hClique : hasClique 3 3 k3 := by
    refine ⟨triangleSdv, by decide, ?_⟩
    intro i j _
    rfl
  have hEval : evalCircuit circuit k3.fn = true := (hDet k3).mp hClique
  have hFalse : evalCircuit circuit k3.fn = false := by
    dsimp only [evalCircuit]
    have hGate0 : evalGate circuit k3.fn ⟨0, by decide⟩ = Fin.snoc k3.fn false := by
      unfold evalGate
      have hAny : (List.finRange (numGraphEdges 3)).any (fun _ => false) = false := by decide
      simp [k3, hAny]
    change evalGate circuit k3.fn ⟨0, by decide⟩ ⟨numGraphEdges 3 + 0, by decide⟩ = false
    rw [hGate0]
    rfl
  exact Bool.false_ne_true (hFalse.symm.trans hEval)

/-- A 2-gate unbounded fan-in NAND circuit that detects 3-cliques on 3-vertex graphs:
gate 0 computes `NAND(e₀, e₁, e₂)`, and gate 1 negates gate 0. -/
private def circuit332 : NandCircuit (numGraphEdges 3) 2 :=
  ⟨fun idx => idx.val ∈ [0, 1, 2, 6]⟩

private lemma sortedDistinctVector_3_3_eq (sdv : SortedDistinctVector 3 3) :
    sdv.elements.get 0 = 0 ∧ sdv.elements.get 1 = 1 ∧ sdv.elements.get 2 = 2 := by
  have h01 : sdv.elements.get 0 < sdv.elements.get 1 := sdv.distinct 0 1 (by decide)
  have h12 : sdv.elements.get 1 < sdv.elements.get 2 := sdv.distinct 1 2 (by decide)
  omega

/-- There exists a 2-gate unbounded fan-in NAND circuit detecting 3-cliques on 3-vertex graphs. -/
theorem exists_circuit_3_3_2 : existsCliqueDetectorCircuit 3 3 2 := by
  refine ⟨circuit332, fun G => ?_⟩
  have hGate0 :
      evalGate circuit332 G.fn ⟨0, by decide⟩ =
        Fin.snoc G.fn (!(G.fn ⟨0, by decide⟩ && G.fn ⟨1, by decide⟩ && G.fn ⟨2, by decide⟩)) := by
    funext i
    unfold evalGate
    simp only [circuit332, TrapezoidalBitArray.getRow, TrapezoidalBitArray.get,
      numGraphEdges, trapezoidSize, List.finRange_succ, List.finRange_zero,
      List.any_cons]
    congr 1
    simp [Bool.or_assoc]
  have hEval :
      evalCircuit circuit332 G.fn =
        (G.fn ⟨0, by decide⟩ && G.fn ⟨1, by decide⟩ && G.fn ⟨2, by decide⟩) := by
    dsimp only [evalCircuit]
    change evalGate circuit332 G.fn ⟨1, by decide⟩ ⟨numGraphEdges 3 + 1, by decide⟩ = _
    unfold evalGate
    dsimp only
    rw [hGate0]
    simp only [circuit332, TrapezoidalBitArray.getRow, TrapezoidalBitArray.get,
      numGraphEdges, trapezoidSize, Fin.snoc,
      List.finRange_succ, List.finRange_zero, List.any_cons, List.any_map]
    cases G.fn ⟨0, by decide⟩ <;> cases G.fn ⟨1, by decide⟩ <;>
      cases G.fn ⟨2, by decide⟩ <;> simp
  rw [hEval]
  constructor
  · rintro ⟨sdv, _, hEdges⟩
    obtain ⟨h0, h1, h2⟩ := sortedDistinctVector_3_3_eq sdv
    have e01 : G.fn ⟨0, by decide⟩ = true := by
      simpa [TrapezoidalBitArray.get, trapezoidSize, h0, h1] using
        hEdges ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    have e02 : G.fn ⟨1, by decide⟩ = true := by
      simpa [TrapezoidalBitArray.get, trapezoidSize, h0, h2] using
        hEdges ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    have e12 : G.fn ⟨2, by decide⟩ = true := by
      simpa [TrapezoidalBitArray.get, trapezoidSize, h1, h2] using
        hEdges ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
    simp [e01, e02, e12]
  · intro hAll
    rcases Bool.and_eq_true_iff.mp hAll with ⟨h01, h2⟩
    rcases Bool.and_eq_true_iff.mp h01 with ⟨h0, h1⟩
    refine ⟨triangleSdv, by decide, ?_⟩
    intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hij' : i < j := hij
    match i, j with
    | 0, 1 => exact h0
    | 0, 2 => exact h1
    | 1, 2 => exact h2
    | 0, 0 | 1, 0 | 1, 1 | 2, 0 | 2, 1 | 2, 2 => exfalso; omega
