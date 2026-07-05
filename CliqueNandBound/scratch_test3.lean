import Mathlib.Data.PNat.Defs
import CliqueNandBound.TrapezoidalBitArray

def NandCircuit (num_inputs : Nat) (num_gates : PNat) : Type :=
  TrapezoidalBitArray num_gates num_inputs

def eval_gate (num_inputs : Nat) (num_gates : PNat)
(circuit : NandCircuit num_inputs num_gates)
(inputs : BitVec num_inputs) (gate : Fin num_gates) :
BitVec (num_inputs + (gate.val + 1)) :=
  let previous_inputs : BitVec (num_inputs + gate.val) :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g+1, h⟩ => eval_gate num_inputs num_gates circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let wires : BitVec (num_inputs + gate.val) := Nat.add_comm gate.val num_inputs
    ▸ TrapezoidalBitArray.get_row circuit gate
  let output_bit : Bool := (previous_inputs &&& wires) != wires
  BitVec.cons output_bit previous_inputs
