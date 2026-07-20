import Mathlib.Data.PNat.Defs

import CliqueNandBound.TrapezoidalBitArray

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/- An unbounded fan-in NAND gate circuit.

We represent the inputs to each gate as a boolean function.
A trapezoidal bit array represents the inputs and/or previous
gates which are fed into each gate.
-/
def NandCircuit (num_inputs : Nat) (num_gates : PNat) : Type :=
  TrapezoidalBitArray num_gates num_inputs

/- Appends a single boolean value at index `n` to a function `Fin n → Bool`. -/
def Fin.snoc {n : Nat} (f : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  fun i =>
    if h : i.val < n then
      f ⟨i.val, h⟩
    else
      b

/- Evaluates a single gate.

Given a circuit, the inputs to gate g, and the index of g,
returns the function mapping available wires
(inputs + previous gate outputs + gate g's output) to their Bool values.
 -/
def eval_gate (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : Fin num_inputs → Bool) (gate : Fin num_gates) :
Fin (num_inputs + (gate.val + 1)) → Bool :=
  let previous_inputs : Fin (num_inputs + gate.val) → Bool :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g+1, h⟩ => eval_gate num_inputs num_gates circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let wires : Fin (num_inputs + gate.val) → Bool :=
    Nat.add_comm gate.val num_inputs ▸ circuit.get_row gate
  let output_bit : Bool :=
    (List.finRange (num_inputs + gate.val)).any (fun j => wires j && !previous_inputs j)
  Fin.snoc previous_inputs output_bit

/- Evaluates the entire circuit.  -/
def eval_circuit (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : Fin num_inputs → Bool) : Bool :=
  have h_pos : 0 < num_gates.val := num_gates.property
  let last_gate_index : Fin num_gates := ⟨num_gates.val - 1, by omega⟩
  let all_wires := eval_gate num_inputs num_gates circuit inputs last_gate_index
  have h_idx : num_inputs + (num_gates.val - 1) < num_inputs + (num_gates.val - 1 + 1) := by omega
  all_wires ⟨num_inputs + (num_gates.val - 1), h_idx⟩
