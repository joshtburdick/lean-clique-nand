
import Mathlib.Data.PNat.Defs

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/- An unbounded fan-in NAND gate circuit.

We represent the inputs to each gate as a bitmask.
The circuit is defined as a function from gate index,
to such a bitmask.
-/
def NandCircuit (num_inputs : Nat) (num_gates : PNat) : Type :=
  (g : Fin num_gates) → BitVec (num_inputs + g.val)

/- Evaluates a single gate.

Given a circuit, the inputs to gate g, and the index of g,
returns those inputs, with the output of gate g appended.

FIXME ???: is it confusing to call the outputs of gates "inputs"?
They are inputs to other gates, but still... maybe "wires"?
 -/
def eval_gate (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : BitVec num_inputs) (gate : Fin num_gates) :
BitVec (num_inputs + (gate.val + 1)) :=
  let previous_inputs : BitVec (num_inputs + gate.val) :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g+1, h⟩ => eval_gate num_inputs num_gates circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let output_bit : Bool := (previous_inputs &&& (circuit gate)) != (circuit gate)
  BitVec.cons output_bit previous_inputs

/- Evaluates the entire circuit.  -/
def eval_circuit (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : BitVec num_inputs) : Bool :=
  have : 0 < num_gates.val := num_gates.property
  let last_gate_index : Fin num_gates := ⟨num_gates.val - 1, by omega⟩
  BitVec.msb <| eval_gate num_inputs num_gates circuit inputs last_gate_index



/-
def f (x : Fin 3) : Nat :=
match x with
| (0 : Fin 3) => 0
| (1 : Fin 3) => 1
| (2 : Fin 3) => 2
-/
