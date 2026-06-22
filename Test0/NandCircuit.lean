/--
 Copyright (c) 2026 Josh Burdick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Burdick -/


structure Test0.NandCircuit (num_inputs : Nat) (num_gates : Nat) : Type where
    gate_inputs : Fin num_gates → Fin 2 → Fin (num_inputs + num_gates)
