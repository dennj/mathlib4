/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.ToDAG
public import Mathlib.Computability.Circuit.Family
public import Mathlib.Computability.Circuit.DAGFamily

/-!
# Tree circuit families to DAG circuit families

This file lifts `Circuit.toDAG` pointwise to non-uniform families. Since `toDAG` preserves
evaluation, size, and depth, it transfers the standard family predicates to the DAG setting.
-/

@[expose] public section

namespace Computability

namespace Circuit

variable {G : Nat → Type}

/-- Pointwise translation of a tree-circuit family into a DAG-circuit family. -/
def toDAGFamily (C : Family G) : DAGCircuit.Family G :=
  fun n => toDAG (G := G) (n := n) (C n)

theorem toDAGFamily_Computes [GateEval G] (C : Family G)
    (f : ∀ n : Nat, (Fin n → Bool) → Bool) (h : Computes C f) :
    DAGCircuit.Computes (toDAGFamily (G := G) C) f := by
  intro n x
  change (toDAG (G := G) (n := n) (C n)).eval x = f n x
  calc
    (toDAG (G := G) (n := n) (C n)).eval x = eval (C n) x :=
      Circuit.eval_toDAG (G := G) (n := n) (c := C n) (x := x)
    _ = f n x := h n x

theorem toDAGFamily_HasConstDepth (C : Family G) (h : HasConstDepth C) :
    DAGCircuit.HasConstDepth (toDAGFamily (G := G) C) := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  intro n
  change DAGCircuit.depth (toDAG (G := G) (n := n) (C n)) ≤ d
  -- `toDAG` preserves depth.
  rw [Circuit.depth_toDAG (G := G) (n := n) (c := C n)]
  exact hd n

theorem toDAGFamily_HasPolySize (C : Family G) (h : HasPolySize C) :
    DAGCircuit.HasPolySize (toDAGFamily (G := G) C) := by
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro n
  change DAGCircuit.size (toDAG (G := G) (n := n) (C n)) ≤ p.eval n
  -- `toDAG` preserves size.
  rw [Circuit.size_toDAG (G := G) (n := n) (c := C n)]
  exact hp n

end Circuit

end Computability
