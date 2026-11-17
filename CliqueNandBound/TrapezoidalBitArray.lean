import Mathlib.Data.Fin.Basic

/-
Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/-- A recursive definition of the number of cells in a trapezoid. -/
def trapezoidSize : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => trapezoidSize n m + (n + m)

theorem trapezoidSize_mono (m i n : ℕ) (h : i ≤ n) :
    trapezoidSize i m ≤ trapezoidSize n m := by
  induction h with
  | refl => rfl
  | step _ ih =>
    simp only [trapezoidSize]
    omega

/-- Implementation of a trapezoidal bit array as a function
  `Fin (trapezoidSize nRows nCols) → Bool`.
  - `nRows`: number of rows
  - `nCols`: number of columns in the 0-th (first) row;
    successive rows add one more column
  - `fn`: function mapping flat index to `Bool` -/
structure TrapezoidalBitArray (nRows nCols : ℕ) where
  fn : Fin (trapezoidSize nRows nCols) → Bool

/-- Extracts one bit from the trapezoidal representation. -/
def TrapezoidalBitArray.get {nRows nCols : ℕ}
    (t : TrapezoidalBitArray nRows nCols) (i : Fin nRows)
    (j : Fin (i.val + nCols)) : Bool :=
  let rowStart : ℕ := trapezoidSize i.val nCols
  let bitIndex : ℕ := rowStart + j.val
  have hLt : bitIndex < trapezoidSize nRows nCols := by
    have h1 : rowStart + (i.val + nCols) = trapezoidSize (i.val + 1) nCols := rfl
    have h4 : i.val + 1 ≤ nRows := i.isLt
    have h5 : trapezoidSize (i.val + 1) nCols ≤ trapezoidSize nRows nCols :=
      trapezoidSize_mono nCols (i.val + 1) nRows h4
    dsimp [bitIndex, rowStart]
    omega
  t.fn ⟨bitIndex, hLt⟩

/-- Extracts a row from the trapezoidal representation as a function
  `Fin (i.val + nCols) → Bool`. -/
def TrapezoidalBitArray.getRow {nRows nCols : ℕ}
    (t : TrapezoidalBitArray nRows nCols) (i : Fin nRows) :
    Fin (i.val + nCols) → Bool :=
  fun j => t.get i j

/-- Helper to convert a function `Fin n → Bool` to a `List Bool`. -/
def rowToList {n : ℕ} (f : Fin n → Bool) : List Bool :=
  (List.finRange n).map f

/-- A small sample trapezoidal bit array:
  rows 0 and 2 are all `false`, while row 1 is all `true`. -/
def testTrapezoid1 : TrapezoidalBitArray 3 2 :=
  { fn := fun idx => idx.val ∈ [2, 3, 4] }

example : trapezoidSize 3 2 = 9 := rfl
example : trapezoidSize 0 4 = 0 := rfl
example : rowToList (testTrapezoid1.getRow 0) = [false, false] := by decide
example : rowToList (testTrapezoid1.getRow 1) = [true, true, true] := by decide
example : rowToList (testTrapezoid1.getRow 2) = [false, false, false, false] := by decide
example : testTrapezoid1.get 0 1 = false := by decide
example : testTrapezoid1.get 1 1 = true := by decide
example : testTrapezoid1.get 2 1 = false := by decide
