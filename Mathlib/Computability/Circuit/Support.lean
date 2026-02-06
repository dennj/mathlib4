/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Basic
public import Mathlib.Data.Finset.Union

/-!
# Circuit support

This file defines the (finite) set of input variables used by a circuit, and proves basic lemmas.

For tree circuits, the support is computed structurally:
- an input wire uses exactly that variable
- constants use no variables
- a gate uses the union of the supports of its children

The key semantic lemma is: if two assignments agree on the support, the circuit evaluates to the
same Boolean value.
-/

@[expose] public section

namespace Computability

namespace Circuit

variable {G : Nat → Type} {n : Nat}

/-- The set of input variables used by a circuit. -/
def support : Circuit G n → Finset (Fin n)
  | .input i => {i}
  | .const _ => ∅
  | .gate (k := k) _ f =>
      (Finset.univ : Finset (Fin k)).biUnion fun i => support (f i)

@[simp] theorem support_input (i : Fin n) : support (input (G := G) i) = {i} :=
  rfl

@[simp] theorem support_const (b : Bool) : support (const (G := G) (n := n) b) = ∅ :=
  rfl

@[simp] theorem support_gate {k : Nat} (g : G k) (f : Fin k → Circuit G n) :
    support (gate (G := G) (n := n) g f)
      = (Finset.univ : Finset (Fin k)).biUnion (fun i => support (f i)) :=
  rfl

theorem support_mapGate {H : Nat → Type} (φ : GateHom G H) (c : Circuit G n) :
    support (mapGate (G := G) (n := n) φ c) = support c := by
  classical
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [support, mapGate, ih]

theorem support_mapInputs {m n : Nat} (c : Circuit G n) (ρ : Fin n → Fin m) :
    support (mapInputs (G := G) c ρ) = (support c).image ρ := by
  classical
  induction c with
  | input i => simp [support, mapInputs]
  | const b => simp [support, mapInputs]
  | gate g f ih =>
      simp [support, mapInputs, ih, Finset.biUnion_image]

theorem support_subst {m n : Nat} (c : Circuit G n) (σ : Fin n → Circuit G m) :
    support (subst (G := G) c σ) = (support c).biUnion fun i => support (σ i) := by
  classical
  induction c with
  | input i =>
      simp [support, subst]
  | const b =>
      simp [support, subst]
  | gate g f ih =>
      simp [support, subst, ih, Finset.biUnion_biUnion]

theorem support_child_subset {k : Nat} (g : G k) (f : Fin k → Circuit G n) (i : Fin k) :
    support (f i) ⊆ support (gate (G := G) (n := n) g f) := by
  classical
  simpa [support] using
    (Finset.subset_biUnion_of_mem (s := (Finset.univ : Finset (Fin k)))
      (u := fun j => support (f j)) (x := i) (by simp))

theorem eval_eq_of_eqOn_support_finset [GateEval G] (c : Circuit G n) {x y : Fin n → Bool}
    (h : ∀ i, i ∈ support c → x i = y i) :
    eval c x = eval c y := by
  classical
  induction c with
  | input i =>
      exact h i (by simp [support])
  | const b =>
      rfl
  | gate g f ih =>
      have hxy : (fun i => eval (f i) x) = fun i => eval (f i) y := by
        funext i
        apply ih i
        intro j hj
        apply h j
        exact (support_child_subset (G := G) g f i) hj
      simpa [eval] using congrArg (fun v => GateEval.eval g v) hxy

theorem eval_eq_of_eqOn_support [GateEval G] (c : Circuit G n) {x y : Fin n → Bool}
    (h : Set.EqOn x y (support c : Set (Fin n))) :
    eval c x = eval c y :=
  eval_eq_of_eqOn_support_finset (G := G) c (fun _ hi => h hi)

end Circuit

end Computability
