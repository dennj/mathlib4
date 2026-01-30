/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Gate

/-!
# Circuits (syntax trees)

This file defines a basic notion of Boolean circuits as *syntax trees* over an abstract gate family
`G : Nat → Type` equipped with semantics `[GateEval G]`.

The representation deliberately does not include explicit sharing (DAG circuits). It is intended as
a minimal foundation for later definitions (size/depth measures, families, and non-uniform classes).

## Main definitions

* `Circuit G n`: Boolean circuit over gate family `G` with `n` input wires
* `Circuit.eval`: evaluate a circuit on an input assignment
* `Circuit.mapGate`: transform gate labels via a `GateHom`
* `Circuit.mapInputs`: rename/reindex circuit inputs
* `Circuit.subst`: substitute each input wire by a circuit

## Main theorems

* `Circuit.eval_mapGate`: evaluation commutes with gate mapping (given semantic compatibility)
* `Circuit.eval_mapInputs`: evaluation commutes with input renaming
* `Circuit.eval_subst`: evaluation commutes with substitution
* `Circuit.mapGate_comp`, `Circuit.subst_comp`: composition laws

## Tags

circuit, Boolean, syntax tree, evaluation
-/

@[expose] public section

namespace Computability

/-- A Boolean circuit over gate labels `G` with `n` input wires. -/
inductive Circuit (G : Nat → Type) (n : Nat) : Type where
  | input : Fin n → Circuit G n
  | const : Bool → Circuit G n
  | gate {k : Nat} : G k → (Fin k → Circuit G n) → Circuit G n

namespace Circuit

variable {G : Nat → Type} {n : Nat}

/-- Map gate labels along a `GateHom`. -/
def mapGate {H : Nat → Type} (φ : GateHom G H) : Circuit G n → Circuit H n
  | input i => input i
  | const b => const b
  | gate g f => gate (φ.map g) (fun i => mapGate φ (f i))

@[simp] theorem mapGate_input {H : Nat → Type} (φ : GateHom G H) (i : Fin n) :
    mapGate (G := G) (n := n) φ (input i) = input i :=
  rfl

@[simp] theorem mapGate_const {H : Nat → Type} (φ : GateHom G H) (b : Bool) :
    mapGate (G := G) (n := n) φ (const b) = const b :=
  rfl

@[simp] theorem mapGate_gate {H : Nat → Type} (φ : GateHom G H) {k : Nat} (g : G k)
    (f : Fin k → Circuit G n) :
    mapGate (G := G) (n := n) φ (gate g f) = gate (φ.map g) (fun i => mapGate φ (f i)) :=
  rfl

/-- Evaluate a circuit on an input assignment. -/
def eval [GateEval G] : Circuit G n → (Fin n → Bool) → Bool
  | input i, x => x i
  | const b, _ => b
  | gate g f, x => GateEval.eval g fun i => eval (f i) x

@[simp] theorem eval_input [GateEval G] (i : Fin n) (x : Fin n → Bool) :
    eval (input (G := G) i) x = x i :=
  rfl

@[simp] theorem eval_const [GateEval G] (b : Bool) (x : Fin n → Bool) :
    eval (const (G := G) (n := n) b) x = b :=
  rfl

@[simp] theorem eval_gate [GateEval G] {k : Nat} (g : G k) (f : Fin k → Circuit G n)
    (x : Fin n → Bool) :
    eval (gate (G := G) (n := n) g f) x = GateEval.eval g (fun i => eval (f i) x) :=
  rfl

/-- Rename/reindex circuit inputs. -/
def mapInputs {m n : Nat} (c : Circuit G n) (ρ : Fin n → Fin m) : Circuit G m :=
  match c with
  | input i => input (ρ i)
  | const b => const b
  | gate g f => gate g (fun i => mapInputs (f i) ρ)

@[simp] theorem mapInputs_input {m n : Nat} (ρ : Fin n → Fin m) (i : Fin n) :
    mapInputs (G := G) (input i) ρ = input (ρ i) :=
  rfl

@[simp] theorem mapInputs_const {m n : Nat} (ρ : Fin n → Fin m) (b : Bool) :
    mapInputs (G := G) (const (n := n) b) ρ = const (n := m) b :=
  rfl

@[simp] theorem mapInputs_gate {m n k : Nat} (ρ : Fin n → Fin m) (g : G k)
    (f : Fin k → Circuit G n) :
    mapInputs (G := G) (gate (n := n) g f) ρ = gate (n := m) g (fun i => mapInputs (f i) ρ) :=
  rfl

/-- Substitute each input wire by a circuit. -/
def subst {m n : Nat} (c : Circuit G n) (σ : Fin n → Circuit G m) : Circuit G m :=
  match c with
  | input i => σ i
  | const b => const b
  | gate g f => gate g (fun i => subst (f i) σ)

@[simp] theorem subst_input {m n : Nat} (σ : Fin n → Circuit G m) (i : Fin n) :
    subst (G := G) (input i) σ = σ i :=
  rfl

@[simp] theorem subst_const {m n : Nat} (σ : Fin n → Circuit G m) (b : Bool) :
    subst (G := G) (const (n := n) b) σ = const (n := m) b :=
  rfl

@[simp] theorem subst_gate {m n k : Nat} (σ : Fin n → Circuit G m) (g : G k)
    (f : Fin k → Circuit G n) :
    subst (G := G) (gate (n := n) g f) σ = gate (n := m) g (fun i => subst (f i) σ) :=
  rfl

theorem eval_mapInputs [GateEval G] {m n : Nat} (c : Circuit G n) (ρ : Fin n → Fin m)
    (x : Fin m → Bool) :
    eval (mapInputs (G := G) c ρ) x = eval c (fun i => x (ρ i)) := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [mapInputs, eval, ih]

theorem eval_subst [GateEval G] {m n : Nat} (c : Circuit G n) (σ : Fin n → Circuit G m)
    (x : Fin m → Bool) :
    eval (subst (G := G) c σ) x = eval c (fun i => eval (σ i) x) := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [subst, eval, ih]

theorem eval_mapGate {H : Nat → Type} [GateEval G] [GateEval H] (φ : GateHom G H)
    (hφ : ∀ {k : Nat} (g : G k) (x : Fin k → Bool), GateEval.eval (G := H) (φ.map g) x =
      GateEval.eval (G := G) g x)
    (c : Circuit G n) (x : Fin n → Bool) :
    eval (mapGate (G := G) (n := n) φ c) x = eval c x := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp only [mapGate, eval, ih, hφ]

@[simp]
theorem mapInputs_id (c : Circuit G n) :
    mapInputs c id = c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [mapInputs, ih]

theorem mapInputs_comp {m ℓ n : Nat} (c : Circuit G n) (ρ₁ : Fin n → Fin m) (ρ₂ : Fin m → Fin ℓ) :
    mapInputs (G := G) (mapInputs (G := G) c ρ₁) ρ₂ =
      mapInputs (G := G) c (fun i => ρ₂ (ρ₁ i)) := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [mapInputs, ih]

theorem subst_id (c : Circuit G n) :
    subst (G := G) c (fun i => input i) = c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [subst, ih]

theorem subst_comp {m ℓ n : Nat} (c : Circuit G n) (σ₁ : Fin n → Circuit G m)
    (σ₂ : Fin m → Circuit G ℓ) :
    subst (G := G) (subst (G := G) c σ₁) σ₂ =
      subst (G := G) c (fun i => subst (G := G) (σ₁ i) σ₂) := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [subst, ih]

@[simp]
theorem mapGate_id {G : ℕ → Type} {n : Nat} (c : Circuit G n) :
    mapGate (GateHom.id G) c = c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih => simp [ih]

theorem mapGate_comp {H K : Nat → Type} (g : GateHom H K) (f : GateHom G H) (c : Circuit G n) :
    mapGate (G := G) (n := n) (GateHom.comp g f) c =
      mapGate (G := H) (n := n) g (mapGate (G := G) (n := n) f c) := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g₀ f₀ ih => simp [ih]

end Circuit

end Computability
