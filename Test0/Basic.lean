/-
Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/
import Mathlib.Data.Nat.Basic

/-!
# This is mostly practice.
-/



/-
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity
-/

def hello := "world"



def x := 1
def y := 2

theorem x_le_x : x <= x := by
  apply Nat.le.refl

theorem x_le_y : x <= y := by
  apply Nat.le.step
  exact x_le_x


theorem foo (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro h_PQ h_QR h_P
  apply h_QR
  exact h_PQ h_P


/-  fun h_PQ h_QR h_P => h_QR (h_PQ h_P) -/

def foo3 : Nat × Nat := (3, 4)

#eval foo3.1
#eval foo3.2

/- Defines successive triangle indixes. -/
def next_index : Nat × Nat -> Nat × Nat :=
  fun (i, j) => if j + 1 < i then (i, j + 1) else (i + 1, 0)

/- Enumerates the triangle indices. -/
def get_index (n : Nat) : Nat × Nat :=
match n with
| 0 => (0, 0)
| n + 1 => next_index (get_index n)

/- some quick tests -/
#eval get_index 0
#eval get_index 1
#eval get_index 2
#eval get_index 3
#eval get_index 4
#eval get_index 5
#eval get_index 6
#eval get_index 7

-- add dependent types to this?
