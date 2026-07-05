import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finmap
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


/- Implementation of a trapezoidal bit array as a flat BitVec.
  n_rows : number of rows
  n_cols : number of columns (in the 0-th, a.k.a first, row;
    successive rows add one more column)
  bitvec : flat bit vector of size trapezoid_size n_rows n_cols

??? FIXME call this "TrapezoidalBitVec", as its size is "baked in"?
-/
structure TrapezoidalBitArray (n_rows : Nat) (n_cols : Nat) where
  bitvec : BitVec (trapezoid_size n_rows n_cols)


/- Extracts a substring of a BitVec. -/
def BitVec.substr {w : Nat}
    (start_index : Nat) (width : Nat) (_ : start_index + width ≤ w) (x : BitVec w) :
    BitVec width :=
  BitVec.ushiftRight x start_index |> BitVec.truncate width


/- Extracts a row from the single-BitVec representation. -/
def TrapezoidalBitArray.get_row {n_rows n_cols : Nat}
    (t : TrapezoidalBitArray n_rows n_cols) (i : Fin n_rows) : BitVec (i.val + n_cols) :=
  let row_width : Nat := i.val + n_cols
  let row_start : Nat := trapezoid_size i.val n_cols
  have h_le : row_start + row_width ≤ trapezoid_size n_rows n_cols := by
    have h1 : row_start + row_width = trapezoid_size (i.val + 1) n_cols := by rfl
    rw [h1]
    have h2 : i.val + 1 ≤ n_rows := i.isLt
    exact trapezoid_size_mono n_cols (i.val + 1) n_rows h2
  BitVec.substr row_start row_width h_le t.bitvec


/- Extracts one bit from the single-BitVec representation. -/
def TrapezoidalBitArray.get {n_rows n_cols : Nat}
    (t : TrapezoidalBitArray n_rows n_cols) (i : Fin n_rows) (j : Fin (i.val + n_cols)) : Bool :=
  let row_start : Nat := trapezoid_size i.val n_cols
  let bit_index : Nat := row_start + j.val
  t.bitvec.getLsbD bit_index

-- A small sample trapezoidal bit array:
-- rows 0 and 2 are all 0s, but row 1 is all 1s
def testTrapezoid1 : TrapezoidalBitArray 3 2 :=
  { bitvec := BitVec.ofNat (trapezoid_size 3 2) (4 + 8 + 16) }

-- some tests of this
#eval testTrapezoid1.bitvec
#eval testTrapezoid1.get_row 0
#eval testTrapezoid1.get_row 1
#eval testTrapezoid1.get_row 2
#eval testTrapezoid1.get 0 1
#eval testTrapezoid1.get 1 1
#eval testTrapezoid1.get 2 1
