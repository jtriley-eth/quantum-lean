import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import QuantumLean.Gate

namespace Clifford

/-
## Identity Gate

The identity gate `I` performs no operation on the qubit state.

I |ψ⟩ = |ψ⟩

    ,---,
----| I |----
    '---'

-/
def Identity := OneQubitGate [
  [1, 0],
  [0, 1]
]

/-
## Pauli X Gate

The Pauli X gate `X` flips the qubit state. It is functionally comparable to the
classical logical "NOT" gate.

    ,---,
----| X |----
    '---'

-/
def PauliX := OneQubitGate [
  [0, 1],
  [1, 0]
]

/-
## Pauli Y Gate

The Pauli Y gate `Y` flips the qubit state and introduces a phase shift.

It is a composition of the Pauli X gate `X` and the Pauli Z gate `Z`.

    ,---,
----| Y |----
    '---'

-/
def PauliY := OneQubitGate [
  [0, -Complex.I],
  [Complex.I, 0]
]

/-

## Pauli Z Gate

The Pauli Z gate `Z` introduces a phase shift.

    ,---,
----| Z |----
    '---'

-/
def PauliZ := OneQubitGate [
  [1, 0],
  [0, -1]
]

/-
## Hadamard Gate

The Hadamard gate `H` creates a superposition of the qubit state.

> Note: `Complex.sqrt` depends on `Complex.instField` which is noncomputable,
> thus the `Hadamard` gate is also noncomputable.

    ,---,
----| H |----
    '---'

-/
noncomputable
def Hadamard := OneQubitGate [
  [(1 / √2), (1 / √2)],
  [(1 / √2), -(1 / √2)]
]

end Clifford
