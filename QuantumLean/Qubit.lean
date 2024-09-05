import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs

/-
## Qubit

We define a `Qubit` as a column vector of two complex numbers.

We construct the `Qubit` from a `List ℂ` for syntax convenience.
-/
def Qubit : List ℂ → Matrix (Fin 2) (Fin 1) ℂ
  | [a, b] => λ x => λ _ => match x with
    | 0 => a
    | 1 => b
  | _ => 0

/-
### Basis States

The basis states `∣0⟩` and `∣1⟩` are defined as `Qubit` vectors.
-/
def ZeroBasisState := Qubit [1, 0]

notation "∣0⟩" => ZeroBasisState

def OneBasisState  := Qubit [0, 1]

notation "|1⟩" => OneBasisState
