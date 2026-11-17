import CliqueNandBound.TrapezoidalBitArray

/-
 Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/-- Number of unordered pairs of distinct vertices in an `n`-vertex graph. -/
abbrev numGraphEdges (n : ℕ) : ℕ :=
  trapezoidSize n 0

/-- Encoding of an `n`-vertex simple undirected graph as a lower-triangular bit array. -/
abbrev UndirectedGraphEncoding (n : ℕ) :=
  TrapezoidalBitArray n 0

/-- A vector of length `k`, with values in `0 .. n-1`, whose elements are strictly increasing. -/
structure SortedDistinctVector (n k : ℕ) where
  elements : Vector (Fin n) k
  distinct : ∀ (a b : Fin k), a < b → elements.get a < elements.get b

/-- The property of having a `k`-vertex clique. -/
def hasClique (n : ℕ) (k : Fin (n + 1)) (G : UndirectedGraphEncoding n) : Prop :=
  let getEdge (u v : Fin n) (h : v < u) : Bool :=
    TrapezoidalBitArray.get G u ⟨v.val, by omega⟩
  ∃ (sdv : SortedDistinctVector n k), k.val ≥ 1 ∧
    ∀ (i j : Fin k) (h : i.val < j.val),
      let u := sdv.elements.get j
      let v := sdv.elements.get i
      have hLt : v < u := sdv.distinct i j h
      getEdge u v hLt
