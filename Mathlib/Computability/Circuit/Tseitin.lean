/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.CNF
public import Mathlib.Computability.Circuit.DAG
import Mathlib.Data.List.OfFn

/-!
# Tseitin-style SAT encoding for DAG circuits

This file defines a Tseitin encoding from `DAGCircuit` to CNF, and proves equisatisfiability with
the circuit SAT problem.

The encoding is generic in the gate family `G`. For a gate label `g : G k`, we use a truth-table
CNF encoding of the relation `out = GateEval.eval g children` (exponential in `k`).
-/

@[expose] public section

namespace Computability

namespace Circuit

open DAG

namespace Tseitin

open CNF

variable {G : Nat → Type} {n : Nat}

variable [GateEval G]

/-- Variables for Tseitin encodings: either an input variable, or a node variable. -/
abbrev Var (n N : Nat) : Type :=
  Sum (Fin n) (Fin N)

namespace Var

variable {N : Nat}

def input (i : Fin n) : Var n N :=
  Sum.inl i

def node (i : Fin N) : Var n N :=
  Sum.inr i

end Var

/-- Two-clause encoding of equivalence `v ↔ w`. -/
def eqvClauses {N : Nat} (v w : Var n N) : CNF.Formula (Var n N) :=
  [ [Lit.negate v, Lit.pos w]
  , [Lit.pos v, Lit.negate w]
  ]

/-- Unit-clause encoding of `v = b`. -/
def constClauses {N : Nat} (v : Var n N) (b : Bool) : CNF.Formula (Var n N) :=
  [ [if b then Lit.pos v else Lit.negate v] ]

/-- Convert `j : Fin i` to an index into `Fin N`, given `i < N`. -/
def childToN {N : Nat} (i : Fin N) (j : Fin i.1) : Fin N :=
  ⟨j.1, lt_trans j.2 i.2⟩

/-- A single truth-table clause for `out = GateEval.eval g`. -/
def gateClause {N k : Nat} (g : G k) (child : Fin k → Var n N) (out : Var n N)
    (a : Fin k → Bool) : CNF.Clause (Var n N) :=
  let outLit := if GateEval.eval g a then Lit.pos out else Lit.negate out
  let mism : List (Lit (Var n N)) :=
    List.ofFn fun j : Fin k => if a j then Lit.negate (child j) else Lit.pos (child j)
  outLit :: mism

/-- A list of all Boolean assignments `Fin k → Bool`. -/
def allAssign : (k : Nat) → List (Fin k → Bool)
  | 0 => [Fin.elim0]
  | k + 1 =>
      List.flatMap (fun a => [Fin.cons false a, Fin.cons true a]) (allAssign k)

theorem mem_allAssign : ∀ {k : Nat} (a : Fin k → Bool), a ∈ allAssign k
  | 0, a => by
      have ha : a = Fin.elim0 := by
        funext i
        exact (Fin.elim0 i)
      simp [allAssign, ha]
  | k + 1, a => by
      classical
      let tail : Fin k → Bool := fun i => a i.succ
      have htail : tail ∈ allAssign k := mem_allAssign (k := k) tail
      have hcons : Fin.cons (a 0) tail = a := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      have : a ∈ List.flatMap (fun b => [Fin.cons false b, Fin.cons true b]) (allAssign k) := by
        refine (List.mem_flatMap.2 ?_)
        refine ⟨tail, htail, ?_⟩
        cases h0 : a 0 with
        | false =>
            have : Fin.cons false tail = a := by
              simpa [h0] using congrArg id hcons
            simp [this]
        | true =>
            have : Fin.cons true tail = a := by
              simpa [h0] using congrArg id hcons
            simp [this]
      simpa [allAssign, tail] using this

theorem sum_map_const_nat {α : Type} (l : List α) (m : Nat) :
    (List.map (fun _ : α => m) l).sum = l.length * m := by
  change (List.map (Function.const α m) l).sum = l.length * m
  rw [List.map_const]
  simp

theorem length_allAssign : ∀ k : Nat, (allAssign k).length = 2 ^ k
  | 0 => by
      simp [allAssign]
  | k + 1 => by
      have ih : (allAssign k).length = 2 ^ k :=
        length_allAssign k
      -- `allAssign (k+1)` is obtained by duplicating each assignment for `k`.
      -- First compute the `flatMap` length as a sum of constant `2`s.
      have hsum :
          (List.map (fun _ : Fin k → Bool => (2 : Nat)) (allAssign k)).sum =
            (allAssign k).length * 2 :=
        sum_map_const_nat (l := allAssign k) (m := 2)
      let cons : Bool → (Fin k → Bool) → Fin (k + 1) → Bool :=
        fun b a => Fin.cons (α := fun _ : Fin (k + 1) => Bool) b a
      -- Now unfold and simplify.
      calc
        (allAssign (k + 1)).length =
            (List.flatMap
                (fun a : Fin k → Bool => [cons false a, cons true a])
                (allAssign k)).length := by
              simp [allAssign, cons]
        _ = (List.map (fun _ : Fin k → Bool => (2 : Nat)) (allAssign k)).sum := by
              simp [List.length_flatMap]
        _ = (allAssign k).length * 2 := hsum
        _ = (2 ^ k) * 2 := by simp [ih]
        _ = 2 ^ (k + 1) := by
              simp [Nat.pow_succ]

/-- Truth-table CNF encoding of `out = GateEval.eval g`. -/
def gateClauses {N k : Nat} (g : G k) (child : Fin k → Var n N) (out : Var n N) :
    CNF.Formula (Var n N) :=
  (allAssign k).map fun a => gateClause (n := n) (N := N) g child out a

/-- CNF constraints for a single node of a DAG. -/
def nodeClauses (d : DAG G n) (i : Fin d.N) : CNF.Formula (Var n d.N) :=
  match d.node i.1 i.2 with
  | .input j =>
      eqvClauses (n := n) (N := d.N) (Var.node i) (Var.input (n := n) (N := d.N) j)
  | .const b =>
      constClauses (n := n) (N := d.N) (Var.node (n := n) (N := d.N) i) b
  | .gate g f =>
      gateClauses (n := n) (N := d.N) g
        (fun j => Var.node (n := n) (N := d.N) (childToN (N := d.N) i (f j)))
        (Var.node (n := n) (N := d.N) i)

/-- All node constraints for a circuit. -/
def core (c : DAGCircuit G n) : CNF.Formula (Var n c.N) :=
  List.flatten (List.ofFn fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i)

/-- SAT encoding: node constraints plus a unit clause forcing the output node to be true. -/
def sat (c : DAGCircuit G n) : CNF.Formula (Var n c.N) :=
  core (n := n) c ++ [ [Lit.pos (Var.node (n := n) (N := c.N) c.out)] ]

/-- The canonical assignment induced by an input assignment. -/
def assignmentOf (c : DAGCircuit G n) (x : Fin n → Bool) : Var n c.N → Bool
  | Sum.inl i => x i
  | Sum.inr j => c.toDAG.evalAt x j.1 j.2

/-- Circuit SAT as existence of an input making the output true. -/
def CircuitSAT (c : DAGCircuit G n) : Prop :=
  ∃ x, c.eval x = true

/-
## Size bounds

We provide simple size counts for the Tseitin encoding `sat c`.

For a `k`-ary gate node, the current encoding uses a truth table, yielding `2^k` clauses, each of
length `k+1`.
-/

/-- Size (number of clauses) contributed by a node in the Tseitin encoding. -/
def nodeNumClauses (c : DAGCircuit G n) (i : Fin c.N) : Nat :=
  match c.node i.1 i.2 with
  | .input _ => 2
  | .const _ => 1
  | .gate (k := k) _ _ => 2 ^ k

/-- Size (total number of literal occurrences) contributed by a node in the Tseitin encoding. -/
def nodeNumLits (c : DAGCircuit G n) (i : Fin c.N) : Nat :=
  match c.node i.1 i.2 with
  | .input _ => 4
  | .const _ => 1
  | .gate (k := k) _ _ => (2 ^ k) * (k + 1)

@[simp] theorem length_gateClause {N k : Nat} (g : G k) (child : Fin k → Var n N) (out : Var n N)
    (a : Fin k → Bool) : (gateClause (n := n) (N := N) g child out a).length = k + 1 := by
  simp [gateClause]

theorem length_nodeClauses (c : DAGCircuit G n) (i : Fin c.N) :
    (nodeClauses (n := n) (d := c.toDAG) i).length = nodeNumClauses (n := n) c i := by
  cases hnd : c.node i.1 i.2 <;>
    simp [nodeClauses, nodeNumClauses, eqvClauses, constClauses, gateClauses, length_allAssign, hnd]

theorem length_flatten_gateClauses {N k : Nat} (g : G k) (child : Fin k → Var n N) (out : Var n N) :
    (gateClauses (n := n) (N := N) g child out).flatten.length = (2 ^ k) * (k + 1) := by
  -- Sum the constant clause length `k+1` over all assignments.
  have hconst :
      (List.map (fun a : Fin k → Bool => (gateClause (n := n) (N := N) g child out a).length)
            (allAssign k)).sum =
        (allAssign k).length * (k + 1) := by
    have hf :
        (fun a : Fin k → Bool => (gateClause (n := n) (N := N) g child out a).length) =
          fun _ : Fin k → Bool => k + 1 := by
      funext a
      simp
    rw [hf]
    exact sum_map_const_nat (l := allAssign k) (m := k + 1)
  calc
    (gateClauses (n := n) (N := N) g child out).flatten.length
        = (List.map List.length (gateClauses (n := n) (N := N) g child out)).sum := by
            simp [List.length_flatten]
    _ = (List.map (List.length ∘ fun a : Fin k → Bool => gateClause (n := n) (N := N) g child out a)
            (allAssign k)).sum := by
            simp [gateClauses, List.map_map]
    _ = (List.map (fun a : Fin k → Bool => (gateClause (n := n) (N := N) g child out a).length)
            (allAssign k)).sum := by
            rfl
    _ = (allAssign k).length * (k + 1) := hconst
    _ = (2 ^ k) * (k + 1) := by
            simp [length_allAssign]

theorem length_flatten_nodeClauses (c : DAGCircuit G n) (i : Fin c.N) :
    (nodeClauses (n := n) (d := c.toDAG) i).flatten.length = nodeNumLits (n := n) c i := by
  cases hnd : c.node i.1 i.2 with
  | input j =>
      simp [nodeClauses, nodeNumLits, eqvClauses, hnd]
  | const b =>
      simp [nodeClauses, nodeNumLits, constClauses, hnd]
  | gate g f =>
      simpa [nodeClauses, nodeNumLits, hnd] using
        (length_flatten_gateClauses (n := n) (N := c.N) g
          (fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j)))
          (Var.node (n := n) (N := c.N) i))

theorem numClauses_core (c : DAGCircuit G n) :
    CNF.Formula.numClauses (core (n := n) c) =
      (List.ofFn fun i : Fin c.N => nodeNumClauses (n := n) c i).sum := by
  -- Expand `core` and count clauses by summing per-node clause counts.
  have hf :
      (List.length ∘ fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i) =
        fun i : Fin c.N => nodeNumClauses (n := n) c i := by
    funext i
    simpa [Function.comp] using length_nodeClauses (n := n) c i
  have hlist :
      List.ofFn (List.length ∘ fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i) =
        List.ofFn (fun i : Fin c.N => nodeNumClauses (n := n) c i) :=
    congrArg List.ofFn hf
  simp [CNF.Formula.numClauses, core, List.length_flatten, List.map_ofFn, hlist]

theorem numLits_core (c : DAGCircuit G n) :
    CNF.Formula.numLits (core (n := n) c) =
      (List.ofFn fun i : Fin c.N => nodeNumLits (n := n) c i).sum := by
  -- `core` is a flatten of per-node formulas; literal count is additive via `flatten_flatten`.
  have hf :
      (List.length ∘ List.flatten ∘ fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i) =
        fun i : Fin c.N => nodeNumLits (n := n) c i := by
    funext i
    simpa [Function.comp] using length_flatten_nodeClauses (n := n) c i
  have hlist :
      List.ofFn
          (List.length ∘ List.flatten ∘ fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i) =
        List.ofFn (fun i : Fin c.N => nodeNumLits (n := n) c i) :=
    congrArg List.ofFn hf
  -- Reduce to a sum of per-node literal counts.
  simp [CNF.Formula.numLits, core, List.flatten_flatten, List.length_flatten, List.map_ofFn, hlist]

theorem numClauses_sat (c : DAGCircuit G n) :
    CNF.Formula.numClauses (sat (n := n) c) =
      (List.ofFn fun i : Fin c.N => nodeNumClauses (n := n) c i).sum + 1 := by
  simp [CNF.Formula.numClauses, sat, numClauses_core]

theorem numLits_sat (c : DAGCircuit G n) :
    CNF.Formula.numLits (sat (n := n) c) =
      (List.ofFn fun i : Fin c.N => nodeNumLits (n := n) c i).sum + 1 := by
  -- One extra unit clause forces the output variable to be true.
  rw [sat, CNF.Formula.numLits_append, numLits_core]
  simp [CNF.Formula.numLits]

theorem satisfies_eqvClauses {N : Nat} {σ : Var n N → Bool} {v w : Var n N}
    (h : CNF.Formula.Satisfies (eqvClauses (n := n) (N := N) v w) σ) : σ v = σ w := by
  have h₁ : CNF.Clause.Satisfies [Lit.negate v, Lit.pos w] σ := by
    exact h _ (by simp [eqvClauses])
  have h₂ : CNF.Clause.Satisfies [Lit.pos v, Lit.negate w] σ := by
    exact h _ (by simp [eqvClauses])
  cases hv : σ v with
  | false =>
      have hwLit : Lit.eval σ (Lit.negate w) = true := by
        have := (CNF.Clause.satisfies_pair (σ := σ) (l₁ := Lit.pos v) (l₂ := Lit.negate w)).1 h₂
        rcases this with hvLit | hwLit
        · exfalso
          have hvtrue : σ v = true := by
            simpa using hvLit
          simp [hv] at hvtrue
        · exact hwLit
      have hw : σ w = false := by
        have :
            Lit.eval σ (if false then Lit.pos w else Lit.negate w) = true := by
          simpa using hwLit
        exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := w) (b := false)).1 this
      simp [hw]
  | true =>
      have hwLit : Lit.eval σ (Lit.pos w) = true := by
        have := (CNF.Clause.satisfies_pair (σ := σ) (l₁ := Lit.negate v) (l₂ := Lit.pos w)).1 h₁
        rcases this with hvLit | hwLit
        · exfalso
          have hvfalse : σ v = false := by
            have :
                Lit.eval σ (if false then Lit.pos v else Lit.negate v) = true := by
              simpa using hvLit
            exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := v) (b := false)).1 this
          simp [hv] at hvfalse
        · exact hwLit
      have hw : σ w = true := by
        simpa using hwLit
      simp [hw]

theorem satisfies_eqvClauses_iff {N : Nat} {σ : Var n N → Bool} {v w : Var n N} :
    CNF.Formula.Satisfies (eqvClauses (n := n) (N := N) v w) σ ↔ σ v = σ w := by
  constructor
  · exact satisfies_eqvClauses (n := n)
  · intro hEq cl hcl
    rcases List.mem_cons.1 hcl with hcl | hcl
    · cases hcl
      -- `¬v ∨ w`
      cases hv : σ v <;> cases hw : σ w <;> simp [CNF.Clause.Satisfies, hv, hw] at hEq ⊢
    · rcases List.mem_singleton.1 hcl with hcl
      cases hcl
      -- `v ∨ ¬w`
      cases hv : σ v <;> cases hw : σ w <;> simp [CNF.Clause.Satisfies, hv, hw] at hEq ⊢

theorem satisfies_constClauses {N : Nat} {σ : Var n N → Bool} {v : Var n N} {b : Bool}
    (h : CNF.Formula.Satisfies (constClauses (n := n) (N := N) v b) σ) : σ v = b := by
  have hcl : CNF.Clause.Satisfies [if b then Lit.pos v else Lit.negate v] σ := by
    exact h _ (by simp [constClauses])
  have hlit :
      Lit.eval σ (if b then Lit.pos v else Lit.negate v) = true := by
    simpa using (CNF.Clause.satisfies_singleton (σ := σ) _).1 hcl
  exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := v) (b := b)).1 hlit

theorem satisfies_constClauses_iff {N : Nat} {σ : Var n N → Bool} {v : Var n N} {b : Bool} :
    CNF.Formula.Satisfies (constClauses (n := n) (N := N) v b) σ ↔ σ v = b := by
  constructor
  · intro h
    exact satisfies_constClauses (n := n) (σ := σ) (v := v) (b := b) h
  · intro hv cl hcl
    rcases List.mem_singleton.1 hcl with rfl
    refine ⟨if b then Lit.pos v else Lit.negate v, by simp, ?_⟩
    exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := v) (b := b)).2 hv

theorem satisfies_gateClauses {N k : Nat} {σ : Var n N → Bool} {g : G k}
    {child : Fin k → Var n N} {out : Var n N}
    (h : CNF.Formula.Satisfies (gateClauses (n := n) (N := N) g child out) σ) :
    σ out = GateEval.eval g (fun j => σ (child j)) := by
  classical
  let a0 : Fin k → Bool := fun j => σ (child j)
  have ha0_mem : a0 ∈ allAssign k :=
    mem_allAssign (k := k) a0
  have ha0 :
      gateClause (n := n) (N := N) g child out a0 ∈ gateClauses (n := n) (N := N) g child out := by
    simpa [gateClauses] using (List.mem_map.2 ⟨a0, ha0_mem, rfl⟩)
  have hcl : CNF.Clause.Satisfies (gateClause (n := n) (N := N) g child out a0) σ :=
    h _ ha0
  have hm :
      ∀ j : Fin k,
        Lit.eval σ (if a0 j then Lit.negate (child j) else Lit.pos (child j)) = false := by
    intro j
    cases hsj : σ (child j) <;> simp [a0, hsj]
  rcases hcl with ⟨l, hl, hl_eval⟩
  rcases List.mem_cons.1 hl with rfl | hlm
  · have :
        Lit.eval σ (if GateEval.eval g a0 then Lit.pos out else Lit.negate out) = true := by
      simpa [gateClause] using hl_eval
    exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := out) (b := GateEval.eval g a0)).1 this
  · have : Lit.eval σ l = false := by
      rcases List.mem_ofFn.1 hlm with ⟨j, rfl⟩
      simpa [gateClause] using hm j
    simp [this] at hl_eval

theorem satisfies_gateClauses_of_eq {N k : Nat} {σ : Var n N → Bool} {g : G k}
    {child : Fin k → Var n N} {out : Var n N}
    (hout : σ out = GateEval.eval g (fun j => σ (child j))) :
    CNF.Formula.Satisfies (gateClauses (n := n) (N := N) g child out) σ := by
  classical
  intro cl hcl
  rcases List.mem_map.1 (by simpa [gateClauses] using hcl) with ⟨a, ha, rfl⟩
  -- Either `a` matches the child assignment, in which case `outLit` is true,
  -- or a mismatch literal is true.
  let a0 : Fin k → Bool := fun j => σ (child j)
  by_cases hEq : ∀ j : Fin k, a j = a0 j
  · have hout' : σ out = GateEval.eval g a := by
      have : a = a0 := by
        funext j
        simpa using (hEq j)
      simpa [a0, this] using hout
    refine ⟨if GateEval.eval g a then Lit.pos out else Lit.negate out, by simp [gateClause], ?_⟩
    exact (Lit.eval_outLit_eq_true_iff (σ := σ) (v := out) (b := GateEval.eval g a)).2 hout'
  · have :
        ∃ j : Fin k, a j ≠ a0 j := by
      simpa [not_forall] using hEq
    rcases this with ⟨j, hj⟩
    -- Pick the mismatch literal for `j`.
    let lit : Lit (Var n N) := if a j then Lit.negate (child j) else Lit.pos (child j)
    refine ⟨lit, ?_, ?_⟩
    · have hmemb :
          lit ∈
            List.ofFn (fun t : Fin k =>
              if a t then Lit.negate (child t) else Lit.pos (child t)) := by
        refine List.mem_ofFn.2 ⟨j, ?_⟩
        simp [lit]
      simp [gateClause, lit, hmemb]
    · -- `lit` evaluates to `true` exactly when there is a mismatch at `j`.
      cases ha' : a j <;> cases hx' : a0 j
      · exfalso
        apply hj
        simp [ha', hx']
      · have : σ (child j) = true := by
          simpa [a0] using hx'
        simp [lit, ha', this]
      · have : σ (child j) = false := by
          simpa [a0] using hx'
        simp [lit, ha', this]
      · exfalso
        apply hj
        simp [ha', hx']

theorem satisfies_gateClauses_iff {N k : Nat} {σ : Var n N → Bool} {g : G k}
    {child : Fin k → Var n N} {out : Var n N} :
    CNF.Formula.Satisfies (gateClauses (n := n) (N := N) g child out) σ ↔
      σ out = GateEval.eval g (fun j => σ (child j)) := by
  constructor
  · exact satisfies_gateClauses (n := n)
  · exact satisfies_gateClauses_of_eq (n := n)

theorem assignmentOf_satisfies_nodeClauses (c : DAGCircuit G n) (x : Fin n → Bool) (i : Fin c.N) :
    CNF.Formula.Satisfies (nodeClauses (n := n) (d := c.toDAG) i) (assignmentOf (n := n) c x) := by
  classical
  intro cl hcl
  cases hnd : c.toDAG.node i.1 i.2 with
  | input j =>
      have hmem :
          cl ∈ eqvClauses (n := n) (N := c.N) (Var.node i) (Var.input (n := n) (N := c.N) j) := by
        simpa [nodeClauses, hnd] using hcl
      let σ : Var n c.N → Bool := assignmentOf (n := n) c x
      have hv : σ (Var.node (n := n) (N := c.N) i) = x j := by
        simp [σ, assignmentOf, Var.node, hnd, DAG.evalAt_eq_node (d := c.toDAG) (x := x)]
      have hw : σ (Var.input (n := n) (N := c.N) j) = x j := by
        rfl
      rcases List.mem_cons.1 hmem with rfl | hmem'
      · -- `¬v ∨ w`
        cases hx : x j with
        | false =>
            refine ⟨Lit.negate (Var.node (n := n) (N := c.N) i), by simp, ?_⟩
            have hvn : σ (Var.node (n := n) (N := c.N) i) = false := by
              simpa [hv] using hx
            simpa [σ] using hvn
        | true =>
            refine ⟨Lit.pos (Var.input (n := n) (N := c.N) j), by simp, ?_⟩
            simpa [σ, assignmentOf, Var.input] using hx
      · rcases List.mem_singleton.1 hmem' with rfl
        -- `v ∨ ¬w`
        cases hx : x j with
        | false =>
            refine ⟨Lit.negate (Var.input (n := n) (N := c.N) j), by simp, ?_⟩
            simpa [σ, assignmentOf, Var.input] using hx
        | true =>
            refine ⟨Lit.pos (Var.node (n := n) (N := c.N) i), by simp, ?_⟩
            have hvn : σ (Var.node (n := n) (N := c.N) i) = true := by
              simpa [hv] using hx
            simpa [σ] using hvn
  | const b =>
      have hmem :
          cl ∈ constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b := by
        simpa [nodeClauses, hnd] using hcl
      rcases List.mem_singleton.1 hmem with rfl
      have hv :
          assignmentOf (n := n) c x (Var.node (n := n) (N := c.N) i) = b := by
        simp [assignmentOf, Var.node, hnd, DAG.evalAt_eq_node (d := c.toDAG) (x := x)]
      refine ⟨
        if b then
          Lit.pos (Var.node (n := n) (N := c.N) i)
        else
          Lit.negate (Var.node (n := n) (N := c.N) i),
        by simp, ?_⟩
      have :
          Lit.eval (assignmentOf (n := n) c x)
              (if b then
                Lit.pos (Var.node (n := n) (N := c.N) i)
              else
                Lit.negate (Var.node (n := n) (N := c.N) i)) =
            true :=
        (Lit.eval_outLit_eq_true_iff (σ := assignmentOf (n := n) c x)
          (v := Var.node (n := n) (N := c.N) i) (b := b)).2 hv
      simpa using this
  | gate g f =>
      have hmem :
          cl ∈ gateClauses (n := n) (N := c.N) g
              (fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j)))
              (Var.node (n := n) (N := c.N) i) := by
        simpa [nodeClauses, hnd] using hcl
      have hmem' :
          cl ∈
            (allAssign _).map fun a =>
              gateClause (n := n) (N := c.N) g
                (fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j)))
                (Var.node (n := n) (N := c.N) i) a := by
        simpa [gateClauses] using hmem
      rcases List.mem_map.1 hmem' with ⟨a, _, rfl⟩
      -- Show the truth-table clause for `a` is satisfied under the real semantics.
      let σ : Var n c.N → Bool := assignmentOf (n := n) c x
      by_cases hEq :
          ∀ j : Fin _, σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))) = a j
      · have hout :
            σ (Var.node (n := n) (N := c.N) i) = GateEval.eval g a := by
          have hEval :=
            DAG.evalAt_eq_node (d := c.toDAG) (x := x) (i := i.1) (hi := i.2)
          have hEval' :
              σ (Var.node (n := n) (N := c.N) i) =
                GateEval.eval g fun j =>
                  σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))) := by
            simpa [σ, assignmentOf, Var.node, hnd] using hEval
          have hfun :
              (fun j : Fin _ =>
                σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j)))) = a := by
            funext j
            simpa using (hEq j)
          simpa [hfun] using hEval'
        refine ⟨if GateEval.eval g a then Lit.pos (Var.node (n := n) (N := c.N) i)
          else Lit.negate (Var.node (n := n) (N := c.N) i), by simp [gateClause], ?_⟩
        have :
            Lit.eval σ
                (if GateEval.eval g a then
                    Lit.pos (Var.node (n := n) (N := c.N) i)
                  else
                    Lit.negate (Var.node (n := n) (N := c.N) i)) =
              true :=
          (Lit.eval_outLit_eq_true_iff (σ := σ) (v := Var.node (n := n) (N := c.N) i)
            (b := GateEval.eval g a)).2 hout
        simpa using this
      · have :
            ∃ j : Fin _,
              σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))) ≠ a j := by
          simpa [not_forall] using hEq
        rcases this with ⟨j, hj⟩
        set v : Var n c.N :=
          Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j)) with hv
        let lit : Lit (Var n c.N) := if a j then Lit.negate v else Lit.pos v
        have hm : Lit.eval σ lit = true := by
          have hj' : σ v ≠ a j := by
            simpa [hv] using hj
          have hiff : Lit.eval σ lit = true ↔ σ v ≠ a j := by
            cases ha : a j <;> cases hx : σ v <;> simp [lit, ha, hx]
          exact hiff.2 hj'
        refine ⟨lit, ?_, hm⟩
        have hmemb :
            lit ∈
              List.ofFn (fun t : Fin _ =>
                if a t then
                  Lit.negate
                    (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f t)))
                else
                  Lit.pos
                    (Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f t)))) := by
          refine List.mem_ofFn.2 ⟨j, ?_⟩
          simp [lit, hv]
        -- The chosen literal is in the mismatch list, hence in the whole clause.
        simpa [gateClause, lit] using
          (List.mem_cons_of_mem
            (if GateEval.eval g a then
              Lit.pos (Var.node (n := n) (N := c.N) i)
            else
              Lit.negate (Var.node (n := n) (N := c.N) i))
            hmemb)

theorem assignmentOf_satisfies_core (c : DAGCircuit G n) (x : Fin n → Bool) :
    CNF.Formula.Satisfies (core (n := n) c) (assignmentOf (n := n) c x) := by
  intro cl hcl
  rcases List.mem_flatten.1 hcl with ⟨cs, hcs, hclcs⟩
  rcases List.mem_ofFn.1 hcs with ⟨i, rfl⟩
  exact assignmentOf_satisfies_nodeClauses (n := n) c x i _ hclcs

theorem satisfiable_of_circuitSAT (c : DAGCircuit G n) :
    CircuitSAT (n := n) c → CNF.Formula.Satisfiable (sat (n := n) c) := by
  rintro ⟨x, hx⟩
  refine ⟨assignmentOf (n := n) c x, ?_⟩
  intro cl hcl
  rcases List.mem_append.1 hcl with hcore | hout
  · exact assignmentOf_satisfies_core (n := n) c x _ hcore
  · rcases List.mem_singleton.1 hout with rfl
    refine ⟨Lit.pos (Var.node (n := n) (N := c.N) c.out), by simp, ?_⟩
    have : assignmentOf (n := n) c x (Var.node (n := n) (N := c.N) c.out) = true := by
      simpa [assignmentOf, Var.node, DAGCircuit.eval_def] using hx
    simpa [Lit.eval, this]

theorem circuitSAT_of_satisfiable (c : DAGCircuit G n) :
    CNF.Formula.Satisfiable (sat (n := n) c) → CircuitSAT (n := n) c := by
  rintro ⟨σ, hσ⟩
  let x : Fin n → Bool := fun i => σ (Var.input (n := n) (N := c.N) i)
  have hcore : CNF.Formula.Satisfies (core (n := n) c) σ := by
    intro cl hcl
    exact hσ cl (by simp [sat, hcl])
  have hout :
      CNF.Clause.Satisfies [Lit.pos (Var.node (n := n) (N := c.N) c.out)] σ := by
    have : [Lit.pos (Var.node (n := n) (N := c.N) c.out)] ∈ sat (n := n) c := by
      simp [sat]
    exact hσ _ this
  have hout' : σ (Var.node (n := n) (N := c.N) c.out) = true := by
    have :
        Lit.eval σ (Lit.pos (Var.node (n := n) (N := c.N) c.out)) = true := by
      exact (CNF.Clause.satisfies_singleton (σ := σ) _).1 (by simpa using hout)
    simpa [Lit.eval] using this
  -- Extract satisfaction of the per-node constraints from satisfaction of `core`.
  have hnodeClauses :
      ∀ i : Fin c.N, CNF.Formula.Satisfies (nodeClauses (n := n) (d := c.toDAG) i) σ := by
    intro i cl hcl
    have : cl ∈ core (n := n) c := by
      refine List.mem_flatten.2 ?_
      refine ⟨nodeClauses (n := n) (d := c.toDAG) i, ?_, hcl⟩
      exact List.mem_ofFn.2 ⟨i, rfl⟩
    exact hcore _ this
  -- Prove by strong induction that node variables agree with `evalAt`.
  have hnode :
      ∀ i : Nat, ∀ hi : i < c.N,
        σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = c.toDAG.evalAt x i hi := by
    intro i
    refine Nat.strong_induction_on i ?_
    intro i ih hi
    have hsatI : CNF.Formula.Satisfies (nodeClauses (n := n) (d := c.toDAG) ⟨i, hi⟩) σ :=
      hnodeClauses ⟨i, hi⟩
    cases hnd : c.toDAG.node i hi with
    | input j =>
        have heq :
            σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = σ (Var.input (n := n) (N := c.N) j) := by
          exact satisfies_eqvClauses (n := n) (σ := σ)
            (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (w := Var.input (n := n) (N := c.N) j)
            (by simpa [nodeClauses, hnd] using hsatI)
        have hxj : σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = x j := by
          simpa [x] using heq
        simpa [DAG.evalAt_eq_node (d := c.toDAG) (x := x), hnd] using hxj
    | const b =>
        have : σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = b := by
          exact satisfies_constClauses (n := n) (σ := σ) (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩)
            (b := b) (by simpa [nodeClauses, hnd] using hsatI)
        simpa [assignmentOf, x, Var.node, DAG.evalAt_eq_node (d := c.toDAG) (x := x), hnd, this]
    | gate g f =>
        have hgate :
            σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) =
              GateEval.eval g fun j =>
                σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j))) := by
          exact satisfies_gateClauses (n := n) (σ := σ) (g := g)
            (child := fun j =>
              Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j)))
            (out := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (by simpa [nodeClauses, hnd] using hsatI)
        have hchild :
            (j : Fin _) →
              σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j))) =
                c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
          intro j
          exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)
        have hfun :
            (fun j : Fin _ =>
              σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j)))) =
              fun j : Fin _ => c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
          funext j
          exact hchild j
        have hEval := DAG.evalAt_eq_node (d := c.toDAG) (x := x) (i := i) (hi := hi)
        calc
          σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩)
              = GateEval.eval g fun j =>
                  σ (Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j))) := hgate
          _ = GateEval.eval g fun j =>
                c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
                simp [hfun]
          _ = c.toDAG.evalAt x i hi := by
                simpa [hnd] using hEval.symm
  refine ⟨x, ?_⟩
  have houtEval : c.eval x = σ (Var.node (n := n) (N := c.N) c.out) := by
    simpa [DAGCircuit.eval_def, Var.node] using (hnode c.out.1 c.out.2).symm
  calc
    c.eval x = σ (Var.node (n := n) (N := c.N) c.out) := houtEval
    _ = true := hout'

theorem equisatisfiable (c : DAGCircuit G n) :
    CNF.Formula.Satisfiable (sat (n := n) c) ↔ CircuitSAT (n := n) c := by
  constructor
  · exact circuitSAT_of_satisfiable (n := n) c
  · intro h
    exact satisfiable_of_circuitSAT (n := n) c h

end Tseitin

end Circuit

end Computability
