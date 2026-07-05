import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finmap
/-
Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

def x1 := BitVec.fill 2 true
def x2 := BitVec.fill 2 false
#eval x1
#eval x2
#eval x1 ++ x2

#eval BitVec.fill 0 false

/- A trapezoidal bit array as a "ragged" array of bitstrings. -/
def TrapezoidalBitArray (n_rows : Nat) (n_cols : Nat) : Type :=
  (i : Fin n_rows) -> BitVec (i.val + n_cols)

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

def BitVec.toList {w : Nat} (x : BitVec w) : List Bool :=
  (List.range w).map (fun i => x.getLsbD i)

/- Flattens a trapezoidal bit array into a single bitstring by concatenating rows. -/
def flatten (n_rows : Nat) (n_cols : Nat) (t : TrapezoidalBitArray n_rows n_cols) :
  BitVec (trapezoid_size n_rows n_cols) :=
  match n_rows with
  | 0 => BitVec.fill 0 false
  | n_rows' + 1 =>
    let t_prev : TrapezoidalBitArray n_rows' n_cols := fun i => t (Fin.castSucc i)
    let last_row : BitVec (n_rows' + n_cols) := t ⟨n_rows', Nat.lt_succ_self n_rows'⟩
    (flatten n_rows' n_cols t_prev) ++ last_row

/- A quick test of this. -/
def testTrapezoid : TrapezoidalBitArray 3 2 :=
fun i => match i with
| 0 => BitVec.fill 2 true
| 1 => BitVec.fill 3 false
| 2 => BitVec.fill 4 false
#eval flatten 3 2 testTrapezoid



/- Alternative, experimental implementation of this
  as a single BitVec. -/
structure TrapezoidalBitArray1 (n_rows : Nat) (n_cols : Nat) where
  bitvec : BitVec (trapezoid_size n_rows n_cols)


/- Extracts a substring of a BitVec. -/

def BitVec.substr {w : Nat}
    (start_index : Nat) (width : Nat) (_ : start_index + width ≤ w) (x : BitVec w) :
    BitVec width :=
  BitVec.ushiftRight x start_index |> BitVec.truncate width


/- Extracts a row from the single-BitVec representation. -/
def TrapezoidalBitArray1.get_row {n_rows n_cols : Nat}
    (t : TrapezoidalBitArray1 n_rows n_cols) (i : Fin n_rows) : BitVec (i.val + n_cols) :=
  let row_width : Nat := i.val + n_cols
  let row_start : Nat := trapezoid_size i.val n_cols
  have h_le : row_start + row_width ≤ trapezoid_size n_rows n_cols := by
    have h1 : row_start + row_width = trapezoid_size (i.val + 1) n_cols := by rfl
    rw [h1]
    have h2 : i.val + 1 ≤ n_rows := i.isLt
    exact trapezoid_size_mono n_cols (i.val + 1) n_rows h2
  BitVec.substr row_start row_width h_le t.bitvec
