/-
 Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick -/

/-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

/-! Encoding of undirected graphs as bitmaps -/

/- A triangular matrix encoding an undirected graph with n vertices. -/
def UndirectedGraph (n : Nat) : Type :=
  (i j : Fin n) → i < j → Bool

/- The number of edges in an undirected graph with n vertices. -/
def num_edges (n : Nat) : Nat :=
  n * (n - 1) / 2

def UndirectedGraphEncoding (n : Nat) : Type :=
  Fin (num_edges n) → Bool


/- A tiny example graph. -/
def sillyFunction (n : Fin 6) : Bool :=
match n with
| 0 => true
| _ => false

def tinyGraph : UndirectedGraphEncoding 4 :=
  fun n => sillyFunction n



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
