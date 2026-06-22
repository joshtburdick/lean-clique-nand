/--
 Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick -/

/-
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity
-/
def hello := "world"



def x := 1
def y := 2

theorem x_le_x: x ≤ x := by
  apply Nat.le.refl

theorem x_le_y: x ≤ y := by
  apply Nat.le.step
  exact x_le_x
