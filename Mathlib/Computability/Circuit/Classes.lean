/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Circuit.Family

/-!
# Non-uniform circuit complexity classes

This file provides non-uniform definitions of `AC0`, `ACC0`, and `TC0` as predicates on Boolean
function families `f : ∀ n, (Fin n → Bool) → Bool`, using *circuits* (DAGs with explicit sharing).

Uniformity conditions are intentionally omitted here and should live in a separate development.
-/

@[expose] public section

namespace Computability

open Gate

namespace Circuit

/-- Non-uniform `AC0`: polynomial size, constant depth, with `AC0Gate` basis. -/
def AC0 (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  ∃ C : Circuit.Family AC0Gate, Computes C f ∧ HasConstDepth C ∧ HasPolySize C

/-- Non-uniform `ACC0 m`: polynomial size, constant depth, with `ACC0Gate m` basis.

This definition includes the standard side condition `2 ≤ m`. -/
def ACC0 (m : Nat) (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  2 ≤ m ∧ ∃ C : Circuit.Family (ACC0Gate m), Computes C f ∧ HasConstDepth C ∧ HasPolySize C

/-- Non-uniform `TC0`: polynomial size, constant depth, with `TC0Gate` basis. -/
def TC0 (f : ∀ n : Nat, (Fin n → Bool) → Bool) : Prop :=
  ∃ C : Circuit.Family TC0Gate, Computes C f ∧ HasConstDepth C ∧ HasPolySize C

end Circuit

end Computability

