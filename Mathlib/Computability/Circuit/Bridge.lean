/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Formula.Classes
public import Mathlib.Computability.Circuit.ToCircuitFamily

/-!
# Bridge lemmas: formulas to circuits

This file transfers non-uniform complexity classes from the formula model (trees) to the circuit
model (DAGs) via the pointwise translation `toCircuitFamily`.
-/

@[expose] public section

namespace Computability

open Gate

namespace Formula

variable {f : ∀ n : Nat, (Fin n → Bool) → Bool}

theorem AC0_toCircuit (h : Formula.AC0 f) : Circuit.AC0 f := by
  rcases h with ⟨C, hC, hdepth, hsize⟩
  refine ⟨toCircuitFamily (G := AC0Gate) C, ?_, ?_, ?_⟩
  · exact toCircuitFamily_Computes (G := AC0Gate) C f hC
  · exact toCircuitFamily_HasConstDepth (G := AC0Gate) C hdepth
  · exact toCircuitFamily_HasPolySize (G := AC0Gate) C hsize

theorem ACC0_toCircuit (m : Nat) (h : Formula.ACC0 m f) : Circuit.ACC0 m f := by
  rcases h with ⟨hm, ⟨C, hC, hdepth, hsize⟩⟩
  refine ⟨hm, ?_⟩
  refine ⟨toCircuitFamily (G := ACC0Gate m) C, ?_, ?_, ?_⟩
  · exact toCircuitFamily_Computes (G := ACC0Gate m) C f hC
  · exact toCircuitFamily_HasConstDepth (G := ACC0Gate m) C hdepth
  · exact toCircuitFamily_HasPolySize (G := ACC0Gate m) C hsize

theorem TC0_toCircuit (h : Formula.TC0 f) : Circuit.TC0 f := by
  rcases h with ⟨C, hC, hdepth, hsize⟩
  refine ⟨toCircuitFamily (G := TC0Gate) C, ?_, ?_, ?_⟩
  · exact toCircuitFamily_Computes (G := TC0Gate) C f hC
  · exact toCircuitFamily_HasConstDepth (G := TC0Gate) C hdepth
  · exact toCircuitFamily_HasPolySize (G := TC0Gate) C hsize

end Formula

end Computability
