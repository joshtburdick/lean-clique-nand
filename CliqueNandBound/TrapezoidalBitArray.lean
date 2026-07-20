import Mathlib.Data.Fin.Basic

/-
Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/- A recursive definition of the number of cells in a trapezoid -/
def trapezoid_size : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => trapezoid_size n m + (n + m)

theorem trapezoid_size_mono (m : Nat) (i n : Nat) (h : i ≤ n) :
    trapezoid_size i m ≤ trapezoid_size n m := by
  induction h with
  | refl => rfl
  | step h_le ih =>
    simp only [trapezoid_size]
    omega

#eval trapezoid_size 3 2
#eval trapezoid_size 0 4


/- Implementation of a trapezoidal bit array as a function
  `Fin (trapezoid_size n_rows n_cols) → Bool`.
  n_rows : number of rows
  n_cols : number of columns (in the 0-th, a.k.a first, row;
    successive rows add one more column)
  fn : function mapping flat index to Bool
-/
structure TrapezoidalBitArray (n_rows : Nat) (n_cols : Nat) where
  fn : Fin (trapezoid_size n_rows n_cols) → Bool


/- Extracts one bit from the trapezoidal representation. -/
def TrapezoidalBitArray.get {n_rows n_cols : Nat}
    (t : TrapezoidalBitArray n_rows n_cols) (i : Fin n_rows)
    (j : Fin (i.val + n_cols)) : Bool :=
  let row_start : Nat := trapezoid_size i.val n_cols
  let bit_index : Nat := row_start + j.val
  have h_lt : bit_index < trapezoid_size n_rows n_cols := by
    have h1 : row_start + (i.val + n_cols) = trapezoid_size (i.val + 1) n_cols := rfl
    have h4 : i.val + 1 ≤ n_rows := i.isLt
    have h5 : trapezoid_size (i.val + 1) n_cols ≤ trapezoid_size n_rows n_cols :=
      trapezoid_size_mono n_cols (i.val + 1) n_rows h4
    dsimp [bit_index, row_start]
    omega
  t.fn ⟨bit_index, h_lt⟩


/- Extracts a row from the trapezoidal representation as a function
  `Fin (i.val + n_cols) → Bool`. -/
def TrapezoidalBitArray.get_row {n_rows n_cols : Nat}
    (t : TrapezoidalBitArray n_rows n_cols) (i : Fin n_rows) :
    Fin (i.val + n_cols) → Bool :=
  fun j => t.get i j


-- Helper to convert a function Fin n → Bool to a List Bool for easy testing/eval display
def rowToList {n : Nat} (f : Fin n → Bool) : List Bool :=
  (List.finRange n).map f

-- A small sample trapezoidal bit array:
-- rows 0 and 2 are all 0s, but row 1 is all 1s
def testTrapezoid1 : TrapezoidalBitArray 3 2 :=
  { fn := fun idx => idx.val ∈ [2, 3, 4] }

-- some tests of this
#eval rowToList (testTrapezoid1.get_row 0)
#eval rowToList (testTrapezoid1.get_row 1)
#eval rowToList (testTrapezoid1.get_row 2)
#eval testTrapezoid1.get 0 1
#eval testTrapezoid1.get 1 1
#eval testTrapezoid1.get 2 1
