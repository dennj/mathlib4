/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.DAGComplexity
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Families of DAG circuits

This file defines non-uniform families of DAG circuits indexed by input length, together with
basic depth/size bounds.
-/

@[expose] public section

namespace Computability

namespace Circuit

namespace DAGCircuit

/-- A non-uniform family of DAG circuits indexed by input length. -/
abbrev Family (G : Nat → Type) : Type :=
  ∀ n : Nat, DAGCircuit G n

/-- A circuit family `C` computes a Boolean function family `f` if it agrees for every input
length `n` and input vector `x`. -/
def Computes {G : Nat → Type} [GateEval G] (C : Family G) (f : ∀ n : Nat, (Fin n → Bool) → Bool) :
    Prop :=
  ∀ n x, (C n).eval x = f n x

/-- The family has constant depth if there is a uniform bound on `depth (C n)`. -/
def HasConstDepth {G : Nat → Type} (C : Family G) : Prop :=
  ∃ d : Nat, ∀ n : Nat, DAGCircuit.depth (C n) ≤ d

/-- The family has polynomial size if `size (C n)` is bounded by some polynomial in `n`. -/
def HasPolySize {G : Nat → Type} (C : Family G) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : Nat, DAGCircuit.size (C n) ≤ p.eval n

end DAGCircuit

end Circuit

end Computability

