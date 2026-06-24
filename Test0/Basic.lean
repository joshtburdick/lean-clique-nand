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

theorem foo_3 (a : Nat) : a * 3 >= a := by
  omega
