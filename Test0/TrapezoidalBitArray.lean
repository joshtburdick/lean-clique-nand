import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finmap
/-
Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/


/- Number of cells in a trapezoid, given the number of rows and columns -/
def trapezoid_size_1 (n_rows : Nat) (n_cols : Nat) : Nat :=
  match n_rows, n_cols with
  | 0, _ => 0
  | n+1, m => trapezoid_size_1 n m + n + m
#eval trapezoid_size_1 3 2


/- A trapezoidal bit array. -/
structure TrapezoidalBitArray (n_rows : Nat) (n_cols : Nat) : Type where
  bits : (i : Fin n_rows) → Fin (i.val + n_cols) → Bool

def ArrayType1 := TrapezoidalBitArray 3 2

-- from Gemini, two ways to create one of these
-- Option 1: Use `@` to make implicit arguments explicit
#check @TrapezoidalBitArray.mk 4 3 (fun _ => fun _ => true)
-- Option 2: Provide explicit types inside the function, letting Lean infer structure parameters
#check (TrapezoidalBitArray.mk (fun (i : Fin 4) (_ : Fin (i.val + 3)) => true))

-- example: creating a trapezoidal bit array containing "all ones"
def fullTrapezoidalBitArray (n_rows : Nat) (n_cols : Nat) : TrapezoidalBitArray n_rows n_cols :=
  @TrapezoidalBitArray.mk n_rows n_cols (fun _ => fun _ => true)





/- Converts from 2-D trapezoid indices to a 1-D index. -/
def index_1 (n_rows : Nat) (n_cols : Nat) (i : Nat) (j : Nat) : Nat :=
  match i with
  | 0 => j
  | i'+1 => index_1 n_rows n_cols (i') (j.succ) + n_cols + i'

/- A closed-form expression for the number of cells in a trapezoid -/
def trapezoid_size (n_rows : Nat) (n_cols : Nat) : Nat :=
  n_rows * (n_cols + (n_cols + n_rows - 1)) / 2
#eval trapezoid_size 3 2

def index (n_rows : Nat) (n_cols : Nat) (i : Fin n_rows) (j : Fin (i.val + n_cols)) : Nat :=
  trapezoid_size (i.val) (n_cols) + j.val

/-
theorem index_bound (n_rows : Nat) (n_cols : Nat) (i : Fin n_rows) (j : Fin (i.val + n_cols)) :
  index n_rows n_cols i j < trapezoid_size n_rows n_cols := by
-/



/- Use this to prove the index is in bounds
theorem index_bounds (n_rows : Nat) (n_cols : Nat) (i : Fin n_rows) (j : Fin (i.val + n_cols)) :
  index n_rows n_cols i j < trapezoid_size n_rows n_cols :=
  match i with
  | 0 => j.val

 := by
  induction i using Fin.induction with
  | zero =>
  | succ i' ih => sorry

-/

theorem math_1 (a b : Nat) : ( a + b <= (2 * a + 3 * b)) :=
by omega







/-
theorem trapezoid_size_eq (n_rows : Nat) (n_cols : Nat)
: trapezoid_size n_rows n_cols = trapezoid_size_2 n_rows n_cols :=
  by
    induction n_rows using Nat.strongInduction_on with
    | h =>
  -/
