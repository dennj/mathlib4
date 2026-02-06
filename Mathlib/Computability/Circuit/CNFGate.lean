/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.CNF

/-!
# CNF templates for common Boolean gates

This file provides small, tactic-free CNF templates (and correctness lemmas) for:

- equivalence `v ↔ w`
- constants `v = b`
- binary `AND` / `OR`
- unary `NOT`

These are intended as building blocks for compact SAT encodings (e.g. for `AC0` and `TC0`).
-/

@[expose] public section

namespace Computability

namespace Circuit

namespace CNFEnc

open CNF

variable {V : Type}

def eqvClauses (v w : V) : CNF.Formula V :=
  [ [Lit.negate v, Lit.pos w]
  , [Lit.pos v, Lit.negate w]
  ]

def constClauses (v : V) (b : Bool) : CNF.Formula V :=
  [ [if b then Lit.pos v else Lit.negate v] ]

def and2Clauses (x y out : V) : CNF.Formula V :=
  [ [Lit.negate out, Lit.pos x]
  , [Lit.negate out, Lit.pos y]
  , [Lit.pos out, Lit.negate x, Lit.negate y]
  ]

def or2Clauses (x y out : V) : CNF.Formula V :=
  [ [Lit.negate x, Lit.pos out]
  , [Lit.negate y, Lit.pos out]
  , [Lit.negate out, Lit.pos x, Lit.pos y]
  ]

def notClauses (x out : V) : CNF.Formula V :=
  [ [Lit.pos out, Lit.pos x]
  , [Lit.negate out, Lit.negate x]
  ]

theorem satisfies_eqvClauses_iff {σ : V → Bool} {v w : V} :
    CNF.Formula.Satisfies (eqvClauses (V := V) v w) σ ↔ σ v = σ w := by
  constructor
  · intro h
    have h₁ : CNF.Clause.Satisfies [Lit.negate v, Lit.pos w] σ := by
      exact h _ (by simp [eqvClauses])
    have h₂ : CNF.Clause.Satisfies [Lit.pos v, Lit.negate w] σ := by
      have : [Lit.pos v, Lit.negate w] ∈ eqvClauses (V := V) v w := by
        simp [eqvClauses]
      exact h _ this
    cases hv : σ v <;> cases hw : σ w <;>
      simp [CNF.Clause.Satisfies, hv, hw] at h₁ h₂ ⊢
  · intro hEq cl hcl
    rcases List.mem_cons.1 hcl with hcl | hcl
    · cases hcl
      cases hv : σ v <;> cases hw : σ w <;>
        simp [CNF.Clause.Satisfies, hv, hw] at hEq ⊢
    · rcases List.mem_singleton.1 hcl with hcl
      cases hcl
      cases hv : σ v <;> cases hw : σ w <;>
        simp [CNF.Clause.Satisfies, hv, hw] at hEq ⊢

theorem satisfies_constClauses_iff {σ : V → Bool} {v : V} {b : Bool} :
    CNF.Formula.Satisfies (constClauses (V := V) v b) σ ↔ σ v = b := by
  constructor
  · intro h
    have hcl : CNF.Clause.Satisfies [if b then Lit.pos v else Lit.negate v] σ := by
      exact h _ (by simp [constClauses])
    have hlit :
        Lit.eval σ (if b then Lit.pos v else Lit.negate v) = true := by
      simpa using (CNF.Clause.satisfies_singleton (σ := σ) _).1 hcl
    exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := v) (b := b)).1 hlit
  · intro hv cl hcl
    rcases List.mem_singleton.1 hcl with rfl
    refine ⟨if b then Lit.pos v else Lit.negate v, by simp, ?_⟩
    exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := v) (b := b)).2 hv

theorem satisfies_and2Clauses {σ : V → Bool} {x y out : V} :
    CNF.Formula.Satisfies (and2Clauses (V := V) x y out) σ → σ out = (σ x && σ y) := by
  intro h
  cases hout : σ out <;> cases hx : σ x <;> cases hy : σ y <;>
    simp [and2Clauses, CNF.Formula.Satisfies, CNF.Clause.Satisfies, hout, hx, hy] at h ⊢

theorem satisfies_and2Clauses_of_eq {σ : V → Bool} {x y out : V} (hout : σ out = (σ x && σ y)) :
    CNF.Formula.Satisfies (and2Clauses (V := V) x y out) σ := by
  intro cl hcl
  rcases List.mem_cons.1 hcl with rfl | hcl
  · -- `¬out ∨ x`
    cases hx : σ x <;> cases hy : σ y <;>
      (try
        have houtFalse : σ out = false := by
          simpa [hx, hy] using hout
        refine ⟨Lit.negate out, by simp, ?_⟩
        simp [houtFalse])
    · -- `x = true`, `y = true`
      refine ⟨Lit.pos x, by simp, ?_⟩
      simp [hx]
  · rcases List.mem_cons.1 hcl with rfl | hcl
    · -- `¬out ∨ y`
      cases hx : σ x <;> cases hy : σ y <;>
        (try
          have houtFalse : σ out = false := by
            simpa [hx, hy] using hout
          refine ⟨Lit.negate out, by simp, ?_⟩
          simp [houtFalse])
      · -- `x = true`, `y = true`
        refine ⟨Lit.pos y, by simp, ?_⟩
        simp [hy]
    · rcases List.mem_singleton.1 hcl with rfl
      -- `out ∨ ¬x ∨ ¬y`
      cases hx : σ x with
      | false =>
          refine ⟨Lit.negate x, by simp, ?_⟩
          simp [hx]
      | true =>
          cases hy : σ y with
          | false =>
              refine ⟨Lit.negate y, by simp, ?_⟩
              simp [hy]
          | true =>
              have houtTrue : σ out = true := by
                simpa [hx, hy] using hout
              refine ⟨Lit.pos out, by simp, ?_⟩
              simp [houtTrue]

theorem satisfies_or2Clauses {σ : V → Bool} {x y out : V} :
    CNF.Formula.Satisfies (or2Clauses (V := V) x y out) σ → σ out = (σ x || σ y) := by
  intro h
  cases hout : σ out <;> cases hx : σ x <;> cases hy : σ y <;>
    simp [or2Clauses, CNF.Formula.Satisfies, CNF.Clause.Satisfies, hout, hx, hy] at h ⊢

theorem satisfies_or2Clauses_of_eq {σ : V → Bool} {x y out : V} (hout : σ out = (σ x || σ y)) :
    CNF.Formula.Satisfies (or2Clauses (V := V) x y out) σ := by
  intro cl hcl
  rcases List.mem_cons.1 hcl with rfl | hcl
  · -- `¬x ∨ out`
    cases hx : σ x with
    | false =>
        refine ⟨Lit.negate x, by simp, ?_⟩
        simp [hx]
    | true =>
        have houtTrue : σ out = true := by
          cases hy : σ y <;> simpa [hx, hy] using hout
        refine ⟨Lit.pos out, by simp, ?_⟩
        simp [houtTrue]
  · rcases List.mem_cons.1 hcl with rfl | hcl
    · -- `¬y ∨ out`
      cases hy : σ y with
      | false =>
          refine ⟨Lit.negate y, by simp, ?_⟩
          simp [hy]
      | true =>
          have houtTrue : σ out = true := by
            cases hx : σ x <;> simpa [hx, hy] using hout
          refine ⟨Lit.pos out, by simp, ?_⟩
          simp [houtTrue]
    · rcases List.mem_singleton.1 hcl with rfl
      -- `¬out ∨ x ∨ y`
      cases hx : σ x with
      | false =>
          cases hy : σ y with
          | false =>
              have houtFalse : σ out = false := by
                simpa [hx, hy] using hout
              refine ⟨Lit.negate out, by simp, ?_⟩
              simp [houtFalse]
          | true =>
              refine ⟨Lit.pos y, by simp, ?_⟩
              simp [hy]
      | true =>
          refine ⟨Lit.pos x, by simp, ?_⟩
          simp [hx]

theorem satisfies_notClauses {σ : V → Bool} {x out : V} :
    CNF.Formula.Satisfies (notClauses (V := V) x out) σ → σ out = !(σ x) := by
  intro h
  cases hout : σ out <;> cases hx : σ x <;>
    simp [notClauses, CNF.Formula.Satisfies, CNF.Clause.Satisfies, hout, hx] at h ⊢

theorem satisfies_notClauses_of_eq {σ : V → Bool} {x out : V} (hout : σ out = !(σ x)) :
    CNF.Formula.Satisfies (notClauses (V := V) x out) σ := by
  intro cl hcl
  rcases List.mem_cons.1 hcl with rfl | hcl
  · -- `out ∨ x`
    cases hx : σ x with
    | true =>
        refine ⟨Lit.pos x, by simp, ?_⟩
        simp [hx]
    | false =>
        have houtTrue : σ out = true := by
          simpa [hx] using hout
        refine ⟨Lit.pos out, by simp, ?_⟩
        simp [houtTrue]
  · rcases List.mem_singleton.1 hcl with rfl
    -- `¬out ∨ ¬x`
    cases hx : σ x with
    | true =>
        have houtFalse : σ out = false := by
          simpa [hx] using hout
        refine ⟨Lit.negate out, by simp, ?_⟩
        simp [houtFalse]
    | false =>
        refine ⟨Lit.negate x, by simp, ?_⟩
        simp [hx]

end CNFEnc

end Circuit

end Computability
