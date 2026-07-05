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
