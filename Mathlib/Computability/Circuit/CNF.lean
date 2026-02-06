/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

/-!
# CNF formulas

This file defines a minimal datatype for propositional CNF formulas (lists of clauses of literals)
and their semantics.

We intentionally keep the interface small and tactic-free; this is a foundation for SAT encodings
for circuits.
-/

@[expose] public section

namespace Computability

namespace Circuit

namespace CNF

/-- A literal over variables `Var`. `neg = true` means negated. -/
structure Lit (Var : Type) where
  var : Var
  neg : Bool

namespace Lit

variable {Var : Type}

/-- Positive literal. -/
def pos (v : Var) : Lit Var :=
  ⟨v, false⟩

/-- Negated literal. -/
def negate (v : Var) : Lit Var :=
  ⟨v, true⟩

/-- Evaluate a literal under an assignment. -/
def eval (σ : Var → Bool) (l : Lit Var) : Bool :=
  if l.neg then !(σ l.var) else σ l.var

@[simp] theorem eval_pos (σ : Var → Bool) (v : Var) : eval σ (pos v) = σ v := by
  rfl

@[simp] theorem eval_negate (σ : Var → Bool) (v : Var) : eval σ (negate v) = !(σ v) := by
  rfl

theorem eval_outLit_eq_true_iff (σ : Var → Bool) (v : Var) (b : Bool) :
    eval σ (if b then pos v else negate v) = true ↔ σ v = b := by
  cases b <;> cases hv : σ v <;> simp [eval, pos, negate, hv]

def mapVar {Var' : Type} (f : Var → Var') (l : Lit Var) : Lit Var' :=
  ⟨f l.var, l.neg⟩

@[simp] theorem mapVar_var {Var' : Type} (f : Var → Var') (l : Lit Var) :
    (mapVar (Var := Var) (Var' := Var') f l).var = f l.var :=
  rfl

@[simp] theorem mapVar_neg {Var' : Type} (f : Var → Var') (l : Lit Var) :
    (mapVar (Var := Var) (Var' := Var') f l).neg = l.neg :=
  rfl

@[simp] theorem eval_mapVar {Var' : Type} (f : Var → Var') (σ : Var' → Bool) (l : Lit Var) :
    eval σ (mapVar (Var := Var) (Var' := Var') f l) = eval (fun v => σ (f v)) l := by
  cases l <;> rfl

end Lit

abbrev Clause (Var : Type) : Type :=
  List (Lit Var)

abbrev Formula (Var : Type) : Type :=
  List (Clause Var)

namespace Clause

variable {Var : Type}

/-- A clause is satisfied if some literal is true. -/
def Satisfies (c : Clause Var) (σ : Var → Bool) : Prop :=
  ∃ l ∈ c, Lit.eval σ l = true

def mapVar {Var' : Type} (f : Var → Var') (c : Clause Var) : Clause Var' :=
  c.map (Lit.mapVar (Var := Var) (Var' := Var') f)

@[simp] theorem satisfies_mapVar_iff {Var' : Type} (f : Var → Var') (σ : Var' → Bool)
    (c : Clause Var) :
    Satisfies (mapVar (Var := Var) (Var' := Var') f c) σ ↔ Satisfies c (fun v => σ (f v)) := by
  constructor
  · rintro ⟨l, hl, h⟩
    rcases List.mem_map.1 hl with ⟨l', hl', rfl⟩
    refine ⟨l', hl', ?_⟩
    simpa using h
  · rintro ⟨l, hl, h⟩
    refine ⟨Lit.mapVar (Var := Var) (Var' := Var') f l, ?_, ?_⟩
    · exact List.mem_map.2 ⟨l, hl, rfl⟩
    · simpa using h

theorem satisfies_of_mem {c : Clause Var} {σ : Var → Bool} {l : Lit Var} (hl : l ∈ c)
    (h : Lit.eval σ l = true) : Satisfies c σ :=
  ⟨l, hl, h⟩

@[simp] theorem satisfies_nil (σ : Var → Bool) : Satisfies ([] : Clause Var) σ ↔ False := by
  simp [Satisfies]

@[simp] theorem satisfies_singleton (σ : Var → Bool) (l : Lit Var) :
    Satisfies [l] σ ↔ Lit.eval σ l = true := by
  constructor
  · rintro ⟨l', hl', h⟩
    rcases List.mem_singleton.1 hl' with rfl
    simpa using h
  · intro h
    exact ⟨l, by simp, h⟩

@[simp] theorem satisfies_pair (σ : Var → Bool) (l₁ l₂ : Lit Var) :
    Satisfies [l₁, l₂] σ ↔ Lit.eval σ l₁ = true ∨ Lit.eval σ l₂ = true := by
  constructor
  · rintro ⟨l, hl, h⟩
    rcases List.mem_cons.1 hl with rfl | hl
    · exact Or.inl h
    · rcases List.mem_singleton.1 hl with rfl
      exact Or.inr h
  · rintro (h | h)
    · exact ⟨l₁, by simp, h⟩
    · exact ⟨l₂, by simp, h⟩

end Clause

namespace Formula

variable {Var : Type}

/-- Number of clauses in a CNF formula. -/
abbrev numClauses (f : Formula Var) : Nat :=
  f.length

/-- Total number of literal occurrences in a CNF formula. -/
abbrev numLits (f : Formula Var) : Nat :=
  f.flatten.length

/-- A CNF formula is satisfied if every clause is satisfied. -/
def Satisfies (f : Formula Var) (σ : Var → Bool) : Prop :=
  ∀ c ∈ f, Clause.Satisfies c σ

def mapVar {Var' : Type} (g : Var → Var') (f : Formula Var) : Formula Var' :=
  f.map (Clause.mapVar (Var := Var) (Var' := Var') g)

@[simp] theorem numClauses_mapVar {Var' : Type} (g : Var → Var') (f : Formula Var) :
    numClauses (mapVar (Var := Var) (Var' := Var') g f) = numClauses f := by
  simp [numClauses, mapVar]

@[simp] theorem satisfies_mapVar_iff {Var' : Type} (g : Var → Var') (f : Formula Var) (σ : Var' → Bool) :
    Satisfies (mapVar (Var := Var) (Var' := Var') g f) σ ↔ Satisfies f (fun v => σ (g v)) := by
  constructor
  · intro h c hc
    have hc' :
        Clause.mapVar (Var := Var) (Var' := Var') g c ∈
          mapVar (Var := Var) (Var' := Var') g f := by
      -- `c` appears in the mapped list at the corresponding position.
      unfold mapVar
      exact List.mem_map.2 ⟨c, hc, rfl⟩
    have : Clause.Satisfies (Clause.mapVar (Var := Var) (Var' := Var') g c) σ :=
      h _ hc'
    exact (Clause.satisfies_mapVar_iff (Var := Var) (Var' := Var') g σ c).1 this
  · intro h c hc
    rcases List.mem_map.1 hc with ⟨c', hc', rfl⟩
    have : Clause.Satisfies c' (fun v => σ (g v)) := h _ hc'
    exact (Clause.satisfies_mapVar_iff (Var := Var) (Var' := Var') g σ c').2 this

/-- Satisfiability of a CNF formula. -/
def Satisfiable (f : Formula Var) : Prop :=
  ∃ σ, Satisfies f σ

@[simp] theorem numClauses_def (f : Formula Var) : numClauses f = f.length :=
  rfl

@[simp] theorem numLits_def (f : Formula Var) : numLits f = f.flatten.length :=
  rfl

theorem numLits_eq_sum_lengths (f : Formula Var) : numLits f = (List.map List.length f).sum := by
  simp [numLits, List.length_flatten]

theorem numLits_append (f g : Formula Var) : numLits (f ++ g) = numLits f + numLits g := by
  simp [numLits, List.flatten_append, List.length_append]

end Formula

end CNF

end Circuit

end Computability
