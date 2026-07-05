/-
 Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick -/

/-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
-- import Mathlib.Tactic.Omega

import Test0.TrapezoidalBitArray

abbrev UndirectedGraphEncoding (n : Nat) :=
  TrapezoidalBitArray n 0


/- A vector of length n, with values in 0 .. k-1, whose elements are strictly increasing. -/
structure SortedDistinctVector (n : Nat) (k : Nat) where
  elements : Vector (Fin n) k
  distinct : forall (a b : Fin k), a < b -> elements.get a < elements.get b


def hasClique (n : Nat) (k : Fin n) (G : UndirectedGraphEncoding n) : Prop :=
  let get_edge (u : Fin n) (v : Fin n) (h : v < u) : Bool :=
    TrapezoidalBitArray.get G u ⟨v.val, by omega⟩
  ∃ (sdv : SortedDistinctVector n k), (k.val ≥ 1) ∧
    (∀ (i : Fin k) (j : Fin k), (h : i.val < j.val) →
      let u := sdv.elements.get j
      let v := sdv.elements.get i
      have h_lt : v < u := sdv.distinct i j h
      get_edge u v h_lt)
