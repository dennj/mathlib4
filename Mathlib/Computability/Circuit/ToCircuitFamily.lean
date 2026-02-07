/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Circuit.ToCircuit
public import Mathlib.Computability.Formula.Family
public import Mathlib.Computability.Circuit.Family

/-!
# Formula families to circuit families

This file lifts `Formula.toCircuit` pointwise to non-uniform families. Since `toCircuit` preserves
evaluation, size, and depth, it transfers the standard family predicates to the circuit setting.
-/

@[expose] public section

namespace Computability

open Gate

namespace Formula

variable {G : Nat → Type}

/-- Pointwise translation of a formula family into a circuit family. -/
def toCircuitFamily (C : Formula.Family G) : Circuit.Family G :=
  fun n => toCircuit (G := G) (n := n) (C n)

theorem toCircuitFamily_Computes [GateEval G] (C : Formula.Family G)
    (f : ∀ n : Nat, (Fin n → Bool) → Bool) (h : Formula.Computes C f) :
    Circuit.Computes (toCircuitFamily (G := G) C) f := by
  intro n x
  change (toCircuit (G := G) (n := n) (C n)).eval x = f n x
  calc
    (toCircuit (G := G) (n := n) (C n)).eval x = eval (C n) x :=
      Formula.eval_toCircuit (G := G) (n := n) (c := C n) (x := x)
    _ = f n x := h n x

theorem toCircuitFamily_HasConstDepth (C : Formula.Family G) (h : Formula.HasConstDepth C) :
    Circuit.HasConstDepth (toCircuitFamily (G := G) C) := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  intro n
  change Circuit.depth (toCircuit (G := G) (n := n) (C n)) ≤ d
  -- `toCircuit` preserves depth.
  rw [Formula.depth_toCircuit (G := G) (n := n) (c := C n)]
  exact hd n

theorem toCircuitFamily_HasPolySize (C : Formula.Family G) (h : Formula.HasPolySize C) :
    Circuit.HasPolySize (toCircuitFamily (G := G) C) := by
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro n
  change Circuit.size (toCircuit (G := G) (n := n) (C n)) ≤ p.eval n
  -- `toCircuit` preserves size.
  rw [Formula.size_toCircuit (G := G) (n := n) (c := C n)]
  exact hp n

end Formula

end Computability
