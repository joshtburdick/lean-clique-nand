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




/- from Claude: indexing code -/

-- Pascal's rule, specialized: (i+1).choose 2 = i.choose 2 + i
theorem choose2_succ (i : Nat) : (i + 1).choose 2 = i.choose 2 + i := by
  have h := Nat.choose_succ_succ i 1
  simp [Nat.choose_one_right] at h
  omega

-- choose 2 is monotone
theorem choose2_mono {a b : Nat} (hab : a ≤ b) : a.choose 2 ≤ b.choose 2 := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    have := choose2_succ n
    omega

-- the enumeration itself
def triIndex (n : Nat) (i : Fin n) (j : Fin i) : Fin (n.choose 2) :=
  ⟨i.val.choose 2 + j.val, by
    have h1 : j.val + 1 ≤ i.val := j.is_lt
    have h2 : i.val + 1 ≤ n := i.is_lt
    have step := choose2_succ i.val
    have mono := choose2_mono h2
    omega⟩

-- injectivity, as a map out of the dependent pair type
/- Claude gave this proof; I may not need it.
theorem triIndex_injective (n : Nat) :
    Function.Injective (fun p : Σ i : Fin n, Fin (i : Nat) => triIndex n p.1 p.2) := by
  have key : ∀ {a b : Nat} (x y : Nat), x < a → a < b → a.choose 2 + x < b.choose 2 + y := by
    intro a b x y hx hab
    have step := choose2_succ a
    have mono := choose2_mono hab
    omega
  rintro ⟨i1, j1⟩ ⟨i2, j2⟩ heq
  simp only [triIndex, Fin.mk.injEq] at heq
  have hi : i1.val = i2.val := by
    rcases lt_trichotomy i1.val i2.val with h | h | h
    · exact absurd heq (ne_of_lt (key j1.is_lt h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (key j2.is_lt h))
  have hi' : i1 = i2 := Fin.ext hi
  subst hi'
  have hj : j1.val = j2.val := by omega
  exact Sigma.ext hi' (by simpa using Fin.ext hj)
-/


/-! Encoding of undirected graphs as bitmaps -/



/- A triangular matrix encoding an undirected graph with n vertices. -/
def UndirectedGraph (n : Nat) : Type :=
  (i j : Fin n) → i < j → Bool

/- The number of edges in an undirected graph with n vertices. -/
def num_edges (n : Nat) : Nat :=
  n * (n - 1) / 2

def UndirectedGraphEncoding1 (n : Nat) : Type :=
  Fin (num_edges n) → Bool


/- A tiny example graph. -/
def sillyFunction (n : Fin 6) : Bool :=
match n with
| 0 => true
| _ => false

def tinyGraph : UndirectedGraphEncoding1 4 :=
  fun n => sillyFunction n




/-
def encode_graph (n : Nat) (g : UndirectedGraph n) : UndirectedGraphEncoding n :=
match g with
| UndirectedGraph n edges =>
  UndirectedGraphEncoding n (encode_edges n g)
  -/

/- Convert from the triangular matrix encoding to the 1D encoding -/
/-
def of_triangular_matrix (n : Nat) (g : UndirectedGraph n) : UndirectedGraphEncoding n :=
  fun i => g (Fin.mk i) (Fin.mk (i + 1)) sorry
-/

/- Convert from this encoding to the corresponding bitmask. -/
/-
def undirected_graph_edge_to_index (n : Nat) (u v : Fin n) : Fin (n * (n - 1) / 2) :=
  let i := Fin.val u
  let j := Fin.val v
  if h_u_lt_v : u < v then
    Fin.mk (i * (n - 1) - i * (i + 1) / 2 + j - i - 1)
  else
    Fin.mk (j * (n - 1) - j * (j + 1) / 2 + i - j - 1)
-/


/- def convert_index (n : Nat) (i j : Fin n) ->
(1/2) * ( i^2 + i - j^2 - j )
-/

/-
def convert_index (n : Nat) (i : Fin (n * (n - 1) / 2)) : Nat :=
  match i with
  | 0 => 0
  | Nat.succ j => convert_index n j
-/


/-
if i == (Nat.ofNat 0 : Fin (n * (n-1) / 2)) then true else false
-/


/- Convert a graph encoding to a 1-D bitmask -/
/-def flatten (g : UndirectedGraph n) : (Fin (n * (n - 1) / 2) → Bool) :=

-/

/-
def UndirectedGraphEncoding.flatten (n : Nat) (g : UndirectedGraphEncoding n) : Array Bool :=
  List.toArray #[g i | i <- [0 : n * (n - 1) / 2]]
-/
