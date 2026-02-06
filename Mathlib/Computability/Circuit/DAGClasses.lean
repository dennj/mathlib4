/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.DAGFamily

/-!
# Non-uniform DAG circuit complexity classes

This file provides non-uniform definitions of `AC0`, `ACC0`, and `TC0` as predicates on Boolean
function families `f : ∀ n, (Fin n → Bool) → Bool`, using *DAG circuits* (i.e. circuits with
explicit sharing).

Uniformity conditions are intentionally omitted here and should live in a separate development.
-/

@[expose] public section

namespace Computability

namespace Circuit

open DAG

namespace DAGCircuit

/-- Non-uniform DAG `AC0`: polynomial size, constant depth, with `AC0Gate` basis. -/
def AC0 (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  ∃ C : DAGCircuit.Family AC0Gate, Computes C f ∧ HasConstDepth C ∧ HasPolySize C

/-- Non-uniform DAG `ACC0 m`: polynomial size, constant depth, with `ACC0Gate m` basis.

This definition includes the standard side condition `2 ≤ m`. -/
def ACC0 (m : Nat) (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  2 ≤ m ∧ ∃ C : DAGCircuit.Family (ACC0Gate m), Computes C f ∧ HasConstDepth C ∧ HasPolySize C

/-- Non-uniform DAG `TC0`: polynomial size, constant depth, with `TC0Gate` basis. -/
def TC0 (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  ∃ C : DAGCircuit.Family TC0Gate, Computes C f ∧ HasConstDepth C ∧ HasPolySize C

end DAGCircuit

end Circuit

end Computability

