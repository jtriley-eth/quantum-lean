import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs

/-
## QubitGate

The `OneQubitGate` and `TwoQubitGate` represent `2×2` and `4×4` matrices
respectively. These transform the `Qubit` state.

We construct the `OneQubitGate` and `TwoQubitGate` from a `List (List ℂ)` for
syntax convenience.

-/
def OneQubitGate : List (List ℂ) → Matrix (Fin 2) (Fin 2) ℂ
  | [
      [a, b],
      [c, d]
    ] => λ x => λ y => match x, y with
      | 0, 0 => a
      | 0, 1 => b
      | 1, 0 => c
      | 1, 1 => d
      | _, _ => 0
  | _ => 0

def TwoQubitGate : List (List ℂ) → Matrix (Fin 4) (Fin 4) ℂ
  | [
      [a, b, c, d],
      [e, f, g, h],
      [i, j, k, l],
      [m, n, o, p]
    ] => λ x => λ y => match x, y with
      | 0, 0 => a
      | 0, 1 => b
      | 0, 2 => c
      | 0, 3 => d
      | 1, 0 => e
      | 1, 1 => f
      | 1, 2 => g
      | 1, 3 => h
      | 2, 0 => i
      | 2, 1 => j
      | 2, 2 => k
      | 2, 3 => l
      | 3, 0 => m
      | 3, 1 => n
      | 3, 2 => o
      | 3, 3 => p
      | _, _ => 0
  | _ => 0

/-
## Identity Gate

The identity gate `I` performs no operation on the qubit state.

I |ψ⟩ = |ψ⟩

-/
def Identity := OneQubitGate [
  [1, 0],
  [0, 1]
]
