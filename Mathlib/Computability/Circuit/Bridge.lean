/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Classes
public import Mathlib.Computability.Circuit.ToDAGFamily

/-!
# Bridge lemmas: tree circuits to DAG circuits

This file transfers non-uniform complexity classes from the tree-circuit model to the DAG-circuit
model via the pointwise translation `toDAGFamily`.
-/

@[expose] public section

namespace Computability

namespace Circuit

variable {f : ∀ n : Nat, (Fin n → Bool) → Bool}

theorem AC0_toDAGCircuit (h : AC0 f) : DAGCircuit.AC0 f := by
  rcases h with ⟨C, hC, hdepth, hsize⟩
  refine ⟨toDAGFamily (G := AC0Gate) C, ?_, ?_, ?_⟩
  · exact toDAGFamily_Computes (G := AC0Gate) C f hC
  · exact toDAGFamily_HasConstDepth (G := AC0Gate) C hdepth
  · exact toDAGFamily_HasPolySize (G := AC0Gate) C hsize

theorem ACC0_toDAGCircuit (m : Nat) (h : ACC0 m f) : DAGCircuit.ACC0 m f := by
  rcases h with ⟨hm, ⟨C, hC, hdepth, hsize⟩⟩
  refine ⟨hm, ?_⟩
  refine ⟨toDAGFamily (G := ACC0Gate m) C, ?_, ?_, ?_⟩
  · exact toDAGFamily_Computes (G := ACC0Gate m) C f hC
  · exact toDAGFamily_HasConstDepth (G := ACC0Gate m) C hdepth
  · exact toDAGFamily_HasPolySize (G := ACC0Gate m) C hsize

theorem TC0_toDAGCircuit (h : TC0 f) : DAGCircuit.TC0 f := by
  rcases h with ⟨C, hC, hdepth, hsize⟩
  refine ⟨toDAGFamily (G := TC0Gate) C, ?_, ?_, ?_⟩
  · exact toDAGFamily_Computes (G := TC0Gate) C f hC
  · exact toDAGFamily_HasConstDepth (G := TC0Gate) C hdepth
  · exact toDAGFamily_HasPolySize (G := TC0Gate) C hsize

end Circuit

end Computability
