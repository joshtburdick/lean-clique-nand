import Mathlib.Data.PNat.Defs

import CliqueNandBound.TrapezoidalBitArray

/- Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick
-/

/-- An unbounded fan-in NAND gate circuit.

We represent the inputs to each gate as a boolean function.
A trapezoidal bit array represents the inputs and/or previous
gates which are fed into each gate. -/
def NandCircuit (numInputs : ℕ) (numGates : ℕ+) : Type :=
  TrapezoidalBitArray numGates numInputs

/-- Appends a single boolean value at index `n` to a function `Fin n → Bool`. -/
def Fin.snoc {n : ℕ} (f : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  fun i =>
    if h : i.val < n then
      f ⟨i.val, h⟩
    else
      b

/-- Evaluates a single gate.

Given a circuit, the inputs to the circuit, and the index of gate `g`,
returns the function mapping available wires
(inputs + previous gate outputs + gate `g`'s output) to their `Bool` values. -/
def evalGate {numInputs : ℕ} {numGates : ℕ+}
    (circuit : NandCircuit numInputs numGates)
    (inputs : Fin numInputs → Bool) (gate : Fin numGates) :
    Fin (numInputs + (gate.val + 1)) → Bool :=
  let previousInputs : Fin (numInputs + gate.val) → Bool :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g + 1, h⟩ => evalGate circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let wires : Fin (numInputs + gate.val) → Bool :=
    Nat.add_comm gate.val numInputs ▸ circuit.getRow gate
  let outputBit : Bool :=
    (List.finRange (numInputs + gate.val)).any (fun j => wires j && !previousInputs j)
  Fin.snoc previousInputs outputBit

/-- Evaluates the entire circuit, returning the output of the final gate. -/
def evalCircuit {numInputs : ℕ} {numGates : ℕ+}
    (circuit : NandCircuit numInputs numGates)
    (inputs : Fin numInputs → Bool) : Bool :=
  have hPos : 0 < numGates.val := numGates.property
  let lastGateIndex : Fin numGates := ⟨numGates.val - 1, by omega⟩
  let allWires := evalGate circuit inputs lastGateIndex
  have hIdx : numInputs + (numGates.val - 1) < numInputs + (numGates.val - 1 + 1) := by omega
  allWires ⟨numInputs + (numGates.val - 1), hIdx⟩
