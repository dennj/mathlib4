/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Formula.Complexity
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Formula families

This file defines non-uniform formula families indexed by input length, together with basic
size/depth bounds.
-/

@[expose] public section

namespace Computability

open Gate

namespace Formula

/-- A non-uniform family of formulas indexed by input length. -/
abbrev Family (G : Nat → Type) : Type :=
  ∀ n : Nat, Formula G n

/-- A formula family `C` computes a Boolean function family `f` if it agrees for every input
length `n` and input vector `x`. -/
def Computes {G : Nat → Type} [GateEval G] (C : Family G) (f : ∀ n : Nat, (Fin n → Bool) → Bool) :
    Prop :=
  ∀ n x, eval (C n) x = f n x

/-- The family has constant depth if there is a uniform bound on `depth (C n)`. -/
def HasConstDepth {G : Nat → Type} (C : Family G) : Prop :=
  ∃ d : Nat, ∀ n : Nat, depth (C n) ≤ d

/-- The family has polynomial size if `size (C n)` is bounded by some polynomial in `n`. -/
def HasPolySize {G : Nat → Type} (C : Family G) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : Nat, size (C n) ≤ p.eval n

end Formula

end Computability
