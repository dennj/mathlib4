/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card

/-!
# Circuit gate labels

This file defines a lightweight interface for *arity-indexed* gate labels and their Boolean
semantics, together with standard bases used in circuit complexity (`AC0`, `ACC0`, `TC0`).

The key design choice is to keep **syntax** (gate labels) separate from **semantics**
(an evaluation function), so that later developments can swap representations without changing
core APIs.

## Main definitions

* `GateEval G`: typeclass providing Boolean semantics for a gate family `G : Nat → Type`
* `GateHom G H`: arity-preserving maps between gate families (purely syntactic)
* `countTrue x`: number of `true` values in a Boolean vector `x : Fin n → Bool`
* `AC0Gate`: unbounded fan-in `AND`, `OR`, and unary `NOT`
* `ACC0Gate m`: `AC0` extended with `MOD m` gates
* `TC0Gate`: `AC0` extended with threshold gates

## Implementation notes

Gate families are indexed by arity (`G : Nat → Type`) rather than being a single type with an
arity field. This design enables the type system to enforce arity constraints and allows
clean composition via `GateHom`.

`GateHom` satisfies the category laws (`comp_id`, `id_comp`, `comp_assoc`), so gate families
form a category. A `Category` instance can be defined by importing `CategoryTheory.Category.Basic`.

## Tags

circuit, Boolean, gate, AC0, ACC0, TC0, complexity
-/

@[expose] public section

namespace Computability

namespace Circuit

/-- Semantics for an arity-indexed family of gate labels `G : Nat → Type`. -/
class GateEval (G : Nat → Type) : Type where
  /-- Evaluate a gate of arity `n` on an `n`-bit input vector. -/
  eval : ∀ {n : Nat}, G n → (Fin n → Bool) → Bool

/-- An arity-preserving map between gate label families. This is purely *syntactic*; compatibility
with semantics is expressed separately when needed. -/
structure GateHom (G H : Nat → Type) : Type where
  /-- Map a gate label of arity `n` to a gate label of arity `n`. -/
  map : ∀ n : Nat, G n → H n

namespace GateHom

/-- Identity gate homomorphism. -/
def id (G : Nat → Type) : GateHom G G :=
  ⟨fun _ g => g⟩

/-- Composition of gate homomorphisms. -/
def comp {G H K : Nat → Type} (g : GateHom H K) (f : GateHom G H) : GateHom G K :=
  ⟨fun n x => g.map n (f.map n x)⟩

@[simp] theorem id_map {G : Nat → Type} (n : Nat) (x : G n) : (id G).map n x = x :=
  rfl

@[simp] theorem map_comp {G H K : Nat → Type} (g : GateHom H K) (f : GateHom G H) (n : Nat)
    (x : G n) :
    (comp g f).map n x = g.map n (f.map n x) :=
  rfl

@[simp] theorem comp_id {G H : Nat → Type} (f : GateHom G H) : comp f (id G) = f :=
  rfl

@[simp] theorem comp_id' {G H : Nat → Type} (f : GateHom G H) : comp (id H) f = f :=
  rfl

theorem comp_assoc {G H K L : Nat → Type} (h : GateHom K L) (g : GateHom H K) (f : GateHom G H) :
    comp (comp h g) f = comp h (comp g f) :=
  rfl

end GateHom

/-- Number of `true` inputs in a Boolean vector. -/
def countTrue {n : Nat} (x : Fin n → Bool) : Nat :=
  (Finset.univ.filter fun i : Fin n => x i = true).card

@[simp] theorem countTrue_def {n : Nat} (x : Fin n → Bool) :
    countTrue x = (Finset.univ.filter fun i : Fin n => x i = true).card :=
  rfl

theorem countTrue_le {n : Nat} (x : Fin n → Bool) : countTrue x ≤ n :=
  card_finset_fin_le _

theorem countTrue_snoc {n : Nat} (x : Fin n → Bool) (b : Bool) :
    countTrue (Fin.snoc x b) = countTrue x + (if b then 1 else 0) := by
  classical
  simp only [countTrue]
  -- The key is to split Fin (n+1) into {i.castSucc | i : Fin n} ∪ {last n}
  have himage : Finset.univ.filter (fun i : Fin (n + 1) =>
        Fin.snoc (α := fun _ => Bool) x b i = true) =
      (Finset.univ.filter (fun i : Fin n => x i = true)).image Fin.castSucc ∪
        (if b then {Fin.last n} else ∅) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      constructor
      · intro hb; simp [hb]
      · intro h
        rcases h with ⟨j, _, hj⟩ | h
        · exact (Fin.castSucc_ne_last j hj).elim
        · cases hb : b <;> simp_all
    | cast j =>
      simp only [Fin.snoc_castSucc]
      constructor
      · intro hxj
        left; exact ⟨j, hxj, rfl⟩
      · intro h
        rcases h with ⟨k, hk, hkj⟩ | h
        · have : k = j := Fin.castSucc_injective n hkj
          rwa [← this]
        · cases hb : b <;> simp_all [Fin.castSucc_ne_last]
  have hdisj : Disjoint
      ((Finset.univ.filter (fun i : Fin n => x i = true)).image Fin.castSucc)
      (if b then {Fin.last n} else ∅) := by
    cases b <;> simp [Finset.disjoint_singleton_right, Finset.mem_image, Fin.castSucc_ne_last]
  rw [himage, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
  cases b <;> simp

/-! ## Standard gate bases -/

/-- A simple `AC0` gate basis: unbounded fan-in `AND` / `OR` and unary `NOT`. -/
inductive AC0Gate : Nat → Type where
  | and : {n : Nat} → AC0Gate n
  | or : {n : Nat} → AC0Gate n
  | not : AC0Gate 1
  deriving DecidableEq

/-- Boolean semantics of `AC0Gate`. -/
def AC0Gate.eval : ∀ {n : Nat}, AC0Gate n → (Fin n → Bool) → Bool
  | _, .and, x => decide (∀ i, x i = true)
  | _, .or, x => decide (∃ i, x i = true)
  | _, .not, x => !(x 0)

instance (n : Nat) : Inhabited (AC0Gate n) :=
  ⟨AC0Gate.and⟩

instance : GateEval AC0Gate where
  eval := AC0Gate.eval

@[simp] theorem GateEval_eval_AC0Gate {n : Nat} (g : AC0Gate n) (x : Fin n → Bool) :
    GateEval.eval (G := AC0Gate) g x = AC0Gate.eval g x :=
  rfl

@[simp] theorem AC0Gate_eval_and {n : Nat} (x : Fin n → Bool) :
    AC0Gate.eval (n := n) AC0Gate.and x = decide (∀ i, x i = true) :=
  rfl

@[simp] theorem AC0Gate_eval_or {n : Nat} (x : Fin n → Bool) :
    AC0Gate.eval (n := n) AC0Gate.or x = decide (∃ i, x i = true) :=
  rfl

@[simp] theorem AC0Gate_eval_not (x : Fin 1 → Bool) :
    AC0Gate.eval (n := 1) AC0Gate.not x = !(x 0) :=
  rfl

/-- An `ACC0` gate basis: `AC0` plus a `MOD m` gate (unbounded fan-in). -/
inductive ACC0Gate (m : Nat) : Nat → Type where
  | ac0 : {n : Nat} → AC0Gate n → ACC0Gate m n
  | mod : {n : Nat} → ACC0Gate m n
  deriving DecidableEq

/-- Boolean semantics of `ACC0Gate m`. The `mod` gate outputs `true` iff the number of `true`
inputs is congruent to `0` modulo `m`.

Note: in the usual complexity-theoretic definition of `ACC0[m]`, one assumes `2 ≤ m`. -/
def ACC0Gate.eval (m : Nat) : ∀ {n : Nat}, ACC0Gate m n → (Fin n → Bool) → Bool
  | _, .ac0 g, x => AC0Gate.eval g x
  | _, .mod, x => decide (countTrue x % m = 0)

instance (m n : Nat) : Inhabited (ACC0Gate m n) :=
  ⟨ACC0Gate.mod⟩

instance (m : Nat) : GateEval (ACC0Gate m) where
  eval := ACC0Gate.eval m

@[simp] theorem GateEval_eval_ACC0Gate (m : Nat) {n : Nat} (g : ACC0Gate m n) (x : Fin n → Bool) :
    GateEval.eval (G := ACC0Gate m) g x = ACC0Gate.eval m g x :=
  rfl

@[simp] theorem ACC0Gate_eval_ac0 (m : Nat) {n : Nat} (g : AC0Gate n) (x : Fin n → Bool) :
    ACC0Gate.eval m (ACC0Gate.ac0 (m := m) g) x = AC0Gate.eval g x :=
  rfl

@[simp] theorem ACC0Gate_eval_mod (m n : Nat) (x : Fin n → Bool) :
    ACC0Gate.eval m (ACC0Gate.mod (m := m) (n := n)) x = decide (countTrue x % m = 0) :=
  rfl

/-- A `TC0` gate basis: `AC0` plus threshold gates (unbounded fan-in). -/
inductive TC0Gate : Nat → Type where
  | ac0 : {n : Nat} → AC0Gate n → TC0Gate n
  /-- Threshold gate: outputs `true` iff at least `t` of the inputs are `true`. -/
  | thr : {n : Nat} → Nat → TC0Gate n
  deriving DecidableEq

/-- Boolean semantics of `TC0Gate`. -/
def TC0Gate.eval : ∀ {n : Nat}, TC0Gate n → (Fin n → Bool) → Bool
  | _, .ac0 g, x => AC0Gate.eval g x
  | _, .thr t, x => decide (t ≤ countTrue x)

instance (n : Nat) : Inhabited (TC0Gate n) :=
  ⟨TC0Gate.ac0 AC0Gate.and⟩

instance : GateEval TC0Gate where
  eval := TC0Gate.eval

@[simp] theorem GateEval_eval_TC0Gate {n : Nat} (g : TC0Gate n) (x : Fin n → Bool) :
    GateEval.eval (G := TC0Gate) g x = TC0Gate.eval g x :=
  rfl

@[simp] theorem TC0Gate_eval_ac0 {n : Nat} (g : AC0Gate n) (x : Fin n → Bool) :
    TC0Gate.eval (n := n) (TC0Gate.ac0 g) x = AC0Gate.eval g x :=
  rfl

@[simp] theorem TC0Gate_eval_thr {n : Nat} (t : Nat) (x : Fin n → Bool) :
    TC0Gate.eval (n := n) (TC0Gate.thr (n := n) t) x = decide (t ≤ countTrue x) :=
  rfl

namespace AC0Gate

/-- The canonical injection of `AC0Gate` into `ACC0Gate m`. -/
def toACC0Gate (m : Nat) : GateHom AC0Gate (ACC0Gate m) :=
  ⟨fun n g => ACC0Gate.ac0 (m := m) (n := n) g⟩

/-- The canonical injection of `AC0Gate` into `TC0Gate`. -/
def toTC0Gate : GateHom AC0Gate TC0Gate :=
  ⟨fun n g => TC0Gate.ac0 (n := n) g⟩

@[simp] theorem toACC0Gate_map (m : Nat) (n : Nat) (g : AC0Gate n) :
    (toACC0Gate m).map n g = ACC0Gate.ac0 (m := m) (n := n) g :=
  rfl

@[simp] theorem toTC0Gate_map (n : Nat) (g : AC0Gate n) :
    toTC0Gate.map n g = TC0Gate.ac0 (n := n) g :=
  rfl

@[simp] theorem eval_toACC0Gate (m n : Nat) (g : AC0Gate n) (x : Fin n → Bool) :
    GateEval.eval (G := ACC0Gate m) ((toACC0Gate m).map n g) x =
      GateEval.eval (G := AC0Gate) g x :=
  rfl

@[simp] theorem eval_toTC0Gate (n : Nat) (g : AC0Gate n) (x : Fin n → Bool) :
    GateEval.eval (G := TC0Gate) (toTC0Gate.map n g) x =
      GateEval.eval (G := AC0Gate) g x :=
  rfl

end AC0Gate

end Circuit

end Computability
