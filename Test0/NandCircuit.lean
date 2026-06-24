
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

/- Evaluates a single gate. -/
def eval_gate (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : BitVec num_inputs) (gate : Fin num_gates) :
BitVec (num_inputs + (gate.val + 1)) :=
  let previous_inputs : BitVec (num_inputs + gate.val) :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g+1, h⟩ => eval_gate num_inputs num_gates circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let output_bit : Bool := true
  BitVec.cons output_bit previous_inputs

/- Evaluates the entire circuit.  -/
def eval_circuit (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : BitVec num_inputs) : Bool :=
BitVec.msb <| eval_gate num_inputs num_gates circuit inputs 0

/- FIXME: actually use num_gates - 1 !!! -/





/-
def f (x : Fin 3) : Nat :=
match x with
| (0 : Fin 3) => 0
| (1 : Fin 3) => 1
| (2 : Fin 3) => 2
-/
