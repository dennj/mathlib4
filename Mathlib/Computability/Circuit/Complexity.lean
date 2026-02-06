/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Syntactic complexity measures for circuits

This file defines the basic measures `size` and `depth` for syntax-tree circuits.
-/

@[expose] public section

namespace Computability

namespace Circuit

open scoped BigOperators

variable {G : Nat → Type} {n : Nat}

/-- Syntactic circuit size, counting all nodes (`input`, `const`, and `gate`). -/
def size : Circuit G n → Nat
  | .input _ => 1
  | .const _ => 1
  | .gate (k := k) _ f => (∑ i : Fin k, size (f i)) + 1

/-- Syntactic circuit depth. Inputs and constants have depth `0`. A gate increases depth by `1`
above the maximum depth of its children (with `0` for a nullary gate). -/
def depth : Circuit G n → Nat
  | .input _ => 0
  | .const _ => 0
  | .gate (k := k) _ f => (Finset.sup Finset.univ fun i : Fin k => depth (f i)) + 1

@[simp] theorem size_input (i : Fin n) : size (input (G := G) i) = 1 :=
  rfl

@[simp] theorem size_const (b : Bool) : size (const (G := G) (n := n) b) = 1 :=
  rfl

@[simp] theorem depth_input (i : Fin n) : depth (input (G := G) i) = 0 :=
  rfl

@[simp] theorem depth_const (b : Bool) : depth (const (G := G) (n := n) b) = 0 :=
  rfl

theorem size_mapInputs {m n : Nat} (c : Circuit G n) (ρ : Fin n → Fin m) :
    size (mapInputs (G := G) c ρ) = size c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [size, mapInputs, ih]

theorem depth_mapInputs {m n : Nat} (c : Circuit G n) (ρ : Fin n → Fin m) :
    depth (mapInputs (G := G) c ρ) = depth c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [depth, mapInputs, ih]

theorem size_mapGate {G H : Nat → Type} (φ : GateHom G H) {n : Nat} (c : Circuit G n) :
    size (mapGate (G := G) (n := n) φ c) = size c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [size, mapGate, ih]

theorem depth_mapGate {G H : Nat → Type} (φ : GateHom G H) {n : Nat} (c : Circuit G n) :
    depth (mapGate (G := G) (n := n) φ c) = depth c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | gate g f ih =>
      simp [depth, mapGate, ih]

end Circuit

end Computability
