/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Tseitin
public import Mathlib.Computability.Circuit.Gate
import Mathlib.Data.List.OfFn

/-!
# Compact Tseitin SAT encoding for `AC0` circuits

`Mathlib.Computability.Circuit.Tseitin` provides a generic Tseitin encoding using a truth-table CNF
for each gate, which is exponential in the arity.

This file provides a compact, linear-size alternative for the standard `AC0` basis
(unbounded fan-in `AND` / `OR` and unary `NOT`).
-/

@[expose] public section

namespace Computability

namespace Circuit

open DAG

namespace Tseitin

open CNF

namespace AC0

variable {n : Nat}

/-! ## Gate clauses -/

def andClauses {N k : Nat} (child : Fin k → Var n N) (out : Var n N) :
    CNF.Formula (Var n N) :=
  (List.ofFn fun j : Fin k => [Lit.negate out, Lit.pos (child j)]) ++
    [Lit.pos out :: List.ofFn (fun j : Fin k => Lit.negate (child j))]

def orClauses {N k : Nat} (child : Fin k → Var n N) (out : Var n N) :
    CNF.Formula (Var n N) :=
  (List.ofFn fun j : Fin k => [Lit.pos out, Lit.negate (child j)]) ++
    [Lit.negate out :: List.ofFn (fun j : Fin k => Lit.pos (child j))]

def notClauses {N : Nat} (child : Fin 1 → Var n N) (out : Var n N) :
    CNF.Formula (Var n N) :=
  [ [Lit.pos out, Lit.pos (child 0)]
  , [Lit.negate out, Lit.negate (child 0)]
  ]

def gateClauses {N k : Nat} (g : AC0Gate k)
    (child : Fin k → Var n N) (out : Var n N) : CNF.Formula (Var n N) :=
  match g with
  | .and => andClauses (n := n) (N := N) child out
  | .or => orClauses (n := n) (N := N) child out
  | .not => notClauses (n := n) (N := N) child out

theorem satisfies_andClauses_iff {N k : Nat} {σ : Var n N → Bool} {child : Fin k → Var n N}
    {out : Var n N} :
    CNF.Formula.Satisfies (andClauses (n := n) (N := N) child out) σ ↔
      σ out = AC0Gate.eval (n := k) AC0Gate.and (fun j => σ (child j)) := by
  classical
  constructor
  · intro h
    cases hout : σ out with
    | true =>
        have hAll : ∀ j : Fin k, σ (child j) = true := by
          intro j
          have hcl :
              CNF.Clause.Satisfies [Lit.negate out, Lit.pos (child j)] σ := by
            have :
                [Lit.negate out, Lit.pos (child j)] ∈
                  andClauses (n := n) (N := N) child out := by
              refine List.mem_append.2 (Or.inl ?_)
              exact List.mem_ofFn.2 ⟨j, rfl⟩
            exact h _ this
          have h' :=
            (CNF.Clause.satisfies_pair (σ := σ) (l₁ := Lit.negate out) (l₂ := Lit.pos (child j))).1
              hcl
          rcases h' with hneg | hpos
          · have hfalse : Lit.eval σ (Lit.negate out) = false := by
              simp [hout]
            have : False := by
              have hneg' : Lit.eval σ (Lit.negate out) = true := hneg
              rw [hfalse] at hneg'
              cases hneg'
            exact this.elim
          · simpa using hpos
        have : decide (∀ j : Fin k, σ (child j) = true) = true := by
          simpa [decide_eq_true_eq] using hAll
        simp [AC0Gate.eval, this]
    | false =>
        have hbig :
            CNF.Clause.Satisfies
              (Lit.pos out :: List.ofFn (fun j : Fin k => Lit.negate (child j))) σ := by
          have :
              (Lit.pos out :: List.ofFn (fun j : Fin k => Lit.negate (child j))) ∈
                andClauses (n := n) (N := N) child out := by
            refine List.mem_append.2 (Or.inr ?_)
            simp
          exact h _ this
        have hex : ∃ j : Fin k, σ (child j) = false := by
          rcases hbig with ⟨l, hl, hl_eval⟩
          rcases List.mem_cons.1 hl with rfl | hlm
          · have hfalse : Lit.eval σ (Lit.pos out) = false := by
              simp [hout]
            have : False := by
              have hl_eval' : Lit.eval σ (Lit.pos out) = true := hl_eval
              rw [hfalse] at hl_eval'
              cases hl_eval'
            exact this.elim
          · rcases List.mem_ofFn.1 hlm with ⟨j, rfl⟩
            refine ⟨j, ?_⟩
            cases hx : σ (child j) <;> simp [hx] at hl_eval ⊢
        have hnot : ¬ ∀ j : Fin k, σ (child j) = true := by
          rcases hex with ⟨j, hj⟩
          intro hall
          have htrue : σ (child j) = true := hall j
          rw [hj] at htrue
          cases htrue
        have : decide (∀ j : Fin k, σ (child j) = true) = false := by
          simpa [decide_eq_false_iff_not] using hnot
        simp [AC0Gate.eval, this]
  · intro hout cl hcl
    have hout' : σ out = decide (∀ j : Fin k, σ (child j) = true) := by
      simpa [AC0Gate.eval] using hout
    cases houtBool : σ out with
    | true =>
        have hall : ∀ j : Fin k, σ (child j) = true := by
          have : decide (∀ j : Fin k, σ (child j) = true) = true := by
            simpa [houtBool] using hout'.symm
          simpa [decide_eq_true_eq] using this
        rcases List.mem_append.1 hcl with hcl | hcl
        · rcases List.mem_ofFn.1 hcl with ⟨j, rfl⟩
          refine ⟨Lit.pos (child j), by simp, ?_⟩
          simp [hall j]
        · rcases List.mem_singleton.1 hcl with rfl
          refine ⟨Lit.pos out, by simp, ?_⟩
          simp [houtBool]
    | false =>
        have hnot : ¬ ∀ j : Fin k, σ (child j) = true := by
          have : decide (∀ j : Fin k, σ (child j) = true) = false := by
            simpa [houtBool] using hout'.symm
          simpa [decide_eq_false_iff_not] using this
        have hex : ∃ j : Fin k, σ (child j) = false := by
          have : ∃ j : Fin k, ¬ σ (child j) = true := by
            simpa [not_forall] using hnot
          rcases this with ⟨j, hj⟩
          cases hx : σ (child j) with
          | false => exact ⟨j, hx⟩
          | true => cases hj (by simp [hx])
        rcases List.mem_append.1 hcl with hcl | hcl
        · rcases List.mem_ofFn.1 hcl with ⟨j, rfl⟩
          refine ⟨Lit.negate out, by simp, ?_⟩
          simp [houtBool]
        · rcases List.mem_singleton.1 hcl with rfl
          rcases hex with ⟨j, hj⟩
          refine ⟨Lit.negate (child j), ?_, ?_⟩
          · have : Lit.negate (child j) ∈ List.ofFn (fun t : Fin k => Lit.negate (child t)) :=
              List.mem_ofFn.2 ⟨j, rfl⟩
            exact List.mem_cons_of_mem _ this
          · simp [hj]

theorem satisfies_orClauses_iff {N k : Nat} {σ : Var n N → Bool} {child : Fin k → Var n N}
    {out : Var n N} :
    CNF.Formula.Satisfies (orClauses (n := n) (N := N) child out) σ ↔
      σ out = AC0Gate.eval (n := k) AC0Gate.or (fun j => σ (child j)) := by
  classical
  constructor
  · intro h
    cases hout : σ out with
    | true =>
        have hbig :
            CNF.Clause.Satisfies
              (Lit.negate out :: List.ofFn (fun j : Fin k => Lit.pos (child j))) σ := by
          have :
              (Lit.negate out :: List.ofFn (fun j : Fin k => Lit.pos (child j))) ∈
                orClauses (n := n) (N := N) child out := by
            refine List.mem_append.2 (Or.inr ?_)
            simp
          exact h _ this
        have hex : ∃ j : Fin k, σ (child j) = true := by
          rcases hbig with ⟨l, hl, hl_eval⟩
          rcases List.mem_cons.1 hl with rfl | hlm
          · have : Lit.eval σ (Lit.negate out) = false := by
              simp [hout]
            simp [this] at hl_eval
          · rcases List.mem_ofFn.1 hlm with ⟨j, rfl⟩
            have hj : σ (child j) = true := by
              simpa using hl_eval
            exact ⟨j, hj⟩
        have : decide (∃ j : Fin k, σ (child j) = true) = true := by
          simpa [decide_eq_true_eq] using hex
        simp [AC0Gate.eval, this]
    | false =>
        have hAll : ∀ j : Fin k, σ (child j) = false := by
          intro j
          have hcl :
              CNF.Clause.Satisfies [Lit.pos out, Lit.negate (child j)] σ := by
            have : [Lit.pos out, Lit.negate (child j)] ∈ orClauses (n := n) (N := N) child out := by
              refine List.mem_append.2 (Or.inl ?_)
              exact List.mem_ofFn.2 ⟨j, rfl⟩
            exact h _ this
          have h' :=
            (CNF.Clause.satisfies_pair (σ := σ) (l₁ := Lit.pos out) (l₂ := Lit.negate (child j))).1
              hcl
          rcases h' with houtLit | hneg
          · exfalso
            have : Lit.eval σ (Lit.pos out) = false := by
              simp [hout]
            simp [this] at houtLit
          · cases hx : σ (child j) <;> simp [hx] at hneg ⊢
        have hnot : ¬ ∃ j : Fin k, σ (child j) = true := by
          intro hex
          rcases hex with ⟨j, hj⟩
          have hfalse : σ (child j) = false := hAll j
          rw [hj] at hfalse
          cases hfalse
        have : decide (∃ j : Fin k, σ (child j) = true) = false := by
          simpa [decide_eq_false_iff_not] using hnot
        simp [AC0Gate.eval, this]
  · intro hout cl hcl
    have hout' : σ out = decide (∃ j : Fin k, σ (child j) = true) := by
      simpa [AC0Gate.eval] using hout
    cases houtBool : σ out with
    | true =>
        have hex : ∃ j : Fin k, σ (child j) = true := by
          have : decide (∃ j : Fin k, σ (child j) = true) = true := by
            simpa [houtBool] using hout'.symm
          simpa [decide_eq_true_eq] using this
        rcases List.mem_append.1 hcl with hcl | hcl
        · rcases List.mem_ofFn.1 hcl with ⟨j, rfl⟩
          refine ⟨Lit.pos out, by simp, ?_⟩
          simp [houtBool]
        · rcases List.mem_singleton.1 hcl with rfl
          rcases hex with ⟨j, hj⟩
          refine ⟨Lit.pos (child j), ?_, ?_⟩
          · have : Lit.pos (child j) ∈ List.ofFn (fun t : Fin k => Lit.pos (child t)) :=
              List.mem_ofFn.2 ⟨j, rfl⟩
            exact List.mem_cons_of_mem _ this
          · simp [hj]
    | false =>
        have hnot : ¬ ∃ j : Fin k, σ (child j) = true := by
          have : decide (∃ j : Fin k, σ (child j) = true) = false := by
            simpa [houtBool] using hout'.symm
          simpa [decide_eq_false_iff_not] using this
        rcases List.mem_append.1 hcl with hcl | hcl
        · rcases List.mem_ofFn.1 hcl with ⟨j, rfl⟩
          refine ⟨Lit.negate (child j), by simp, ?_⟩
          have : σ (child j) = false := by
            cases hx : σ (child j) with
            | false => rfl
            | true => exact (False.elim (hnot ⟨j, by simp [hx]⟩))
          simp [this]
        · rcases List.mem_singleton.1 hcl with rfl
          refine ⟨Lit.negate out, by simp, ?_⟩
          simp [houtBool]

theorem satisfies_notClauses_iff {N : Nat} {σ : Var n N → Bool} {child : Fin 1 → Var n N}
    {out : Var n N} :
    CNF.Formula.Satisfies (notClauses (n := n) (N := N) child out) σ ↔
      σ out = AC0Gate.eval (n := 1) AC0Gate.not (fun j => σ (child j)) := by
  constructor
  · intro h
    have h₁ : CNF.Clause.Satisfies [Lit.pos out, Lit.pos (child 0)] σ := by
      exact h _ (by simp [notClauses])
    have h₂ : CNF.Clause.Satisfies [Lit.negate out, Lit.negate (child 0)] σ := by
      exact h _ (by simp [notClauses])
    cases hout : σ out <;> cases hx : σ (child 0) <;>
      simp [AC0Gate.eval, hout, hx] at h₁ h₂ ⊢
  · intro hout cl hcl
    have hout' : σ out = !(σ (child 0)) := by
      simpa [AC0Gate.eval] using hout
    rcases List.mem_cons.1 hcl with rfl | hcl
    · -- clause `[out, child]`
      cases ho : σ out with
      | true =>
          refine ⟨Lit.pos out, by simp, ?_⟩
          simp [ho]
      | false =>
          have hchild : σ (child 0) = true := by
            cases hc : σ (child 0) with
            | false =>
                have hout'' := hout'
                rw [ho, hc] at hout''
                cases hout''
            | true =>
                rfl
          refine ⟨Lit.pos (child 0), by simp, ?_⟩
          simp [hchild]
    · rcases List.mem_singleton.1 hcl with rfl
      -- clause `[¬out, ¬child]`
      cases ho : σ out with
      | true =>
          have hchild : σ (child 0) = false := by
            cases hc : σ (child 0) with
            | false => rfl
            | true =>
                have hout'' := hout'
                rw [ho, hc] at hout''
                cases hout''
          refine ⟨Lit.negate (child 0), by simp, ?_⟩
          simp [hchild]
      | false =>
          refine ⟨Lit.negate out, by simp, ?_⟩
          simp [ho]

theorem satisfies_gateClauses_iff {N k : Nat} {σ : Var n N → Bool} {g : AC0Gate k}
    {child : Fin k → Var n N} {out : Var n N} :
    CNF.Formula.Satisfies (gateClauses (n := n) (N := N) g child out) σ ↔
      σ out = GateEval.eval (G := AC0Gate) g (fun j => σ (child j)) := by
  cases g with
  | and =>
      simpa [gateClauses] using
        (satisfies_andClauses_iff (n := n) (σ := σ) (child := child) (out := out))
  | or =>
      simpa [gateClauses] using
        (satisfies_orClauses_iff (n := n) (σ := σ) (child := child) (out := out))
  | not =>
      simpa [gateClauses] using
        (satisfies_notClauses_iff (n := n) (σ := σ) (child := child) (out := out))

/-! ## Circuit encoding -/

def nodeClauses (d : DAG AC0Gate n) (i : Fin d.N) : CNF.Formula (Var n d.N) :=
  match d.node i.1 i.2 with
  | .input j =>
      Tseitin.eqvClauses (n := n) (N := d.N) (Var.node i) (Var.input (n := n) (N := d.N) j)
  | .const b =>
      Tseitin.constClauses (n := n) (N := d.N) (Var.node (n := n) (N := d.N) i) b
  | .gate g f =>
      gateClauses (n := n) (N := d.N) g
        (fun j => Var.node (n := n) (N := d.N) (Tseitin.childToN (N := d.N) i (f j)))
        (Var.node (n := n) (N := d.N) i)

def core (c : DAGCircuit AC0Gate n) : CNF.Formula (Var n c.N) :=
  List.flatten (List.ofFn fun i : Fin c.N => nodeClauses (n := n) (d := c.toDAG) i)

def sat (c : DAGCircuit AC0Gate n) : CNF.Formula (Var n c.N) :=
  core (n := n) c ++ [ [Lit.pos (Var.node (n := n) (N := c.N) c.out)] ]

theorem assignmentOf_satisfies_nodeClauses (c : DAGCircuit AC0Gate n) (x : Fin n → Bool)
    (i : Fin c.N) :
    CNF.Formula.Satisfies (nodeClauses (n := n) (d := c.toDAG) i)
      (Tseitin.assignmentOf (n := n) c x) := by
  classical
  intro cl hcl
  cases hnd : c.toDAG.node i.1 i.2 with
  | input j =>
      have hmem :
          cl ∈
            Tseitin.eqvClauses (n := n) (N := c.N) (Var.node i)
              (Var.input (n := n) (N := c.N) j) := by
        simpa [nodeClauses, hnd] using hcl
      let σ : Var n c.N → Bool := Tseitin.assignmentOf (n := n) c x
      have hv : σ (Var.node (n := n) (N := c.N) i) = x j := by
        simp [σ, Tseitin.assignmentOf, Var.node, hnd, DAG.evalAt_eq_node (d := c.toDAG) (x := x)]
      have hw : σ (Var.input (n := n) (N := c.N) j) = x j := by
        rfl
      have hEq : σ (Var.node (n := n) (N := c.N) i) = σ (Var.input (n := n) (N := c.N) j) := by
        simp [hv, hw]
      exact (Tseitin.satisfies_eqvClauses_iff (n := n) (σ := σ) (v := Var.node i)
        (w := Var.input (n := n) (N := c.N) j)).2 hEq _ hmem
  | const b =>
      have hmem :
          cl ∈ Tseitin.constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b := by
        simpa [nodeClauses, hnd] using hcl
      let σ : Var n c.N → Bool := Tseitin.assignmentOf (n := n) c x
      have hv : σ (Var.node (n := n) (N := c.N) i) = b := by
        simp [σ, Tseitin.assignmentOf, Var.node, hnd, DAG.evalAt_eq_node (d := c.toDAG) (x := x)]
      exact
        (Tseitin.satisfies_constClauses_iff (n := n) (σ := σ) (v := Var.node i) (b := b)).2
          hv _ hmem
  | gate g f =>
      have hmem :
          cl ∈
            gateClauses (n := n) (N := c.N) g
              (fun j => Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) i (f j)))
              (Var.node (n := n) (N := c.N) i) := by
        simpa [nodeClauses, hnd] using hcl
      let σ : Var n c.N → Bool := Tseitin.assignmentOf (n := n) c x
      have hout :
          σ (Var.node (n := n) (N := c.N) i) =
            GateEval.eval (G := AC0Gate) g fun j =>
              σ (Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) i (f j))) := by
        have hEval :=
          DAG.evalAt_eq_node (d := c.toDAG) (x := x) (i := i.1) (hi := i.2)
        have hEval' :
            c.toDAG.evalAt x i.1 i.2 =
              GateEval.eval (G := AC0Gate) g fun j =>
                c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 i.2) := by
          simpa [hnd] using hEval
        simpa [σ, Tseitin.assignmentOf, Var.node, Tseitin.childToN] using hEval'
      exact (satisfies_gateClauses_iff (n := n) (σ := σ) (g := g)
        (child := fun j => Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) i (f j)))
        (out := Var.node (n := n) (N := c.N) i)).2 hout _ hmem

theorem assignmentOf_satisfies_core (c : DAGCircuit AC0Gate n) (x : Fin n → Bool) :
    CNF.Formula.Satisfies (core (n := n) c) (Tseitin.assignmentOf (n := n) c x) := by
  intro cl hcl
  rcases List.mem_flatten.1 hcl with ⟨cs, hcs, hclcs⟩
  rcases List.mem_ofFn.1 hcs with ⟨i, rfl⟩
  exact assignmentOf_satisfies_nodeClauses (n := n) c x i _ hclcs

theorem satisfiable_of_circuitSAT (c : DAGCircuit AC0Gate n) :
    Tseitin.CircuitSAT (n := n) c → CNF.Formula.Satisfiable (sat (n := n) c) := by
  rintro ⟨x, hx⟩
  refine ⟨Tseitin.assignmentOf (n := n) c x, ?_⟩
  intro cl hcl
  rcases List.mem_append.1 hcl with hcore | hout
  · exact assignmentOf_satisfies_core (n := n) c x _ hcore
  · rcases List.mem_singleton.1 hout with rfl
    refine ⟨Lit.pos (Var.node (n := n) (N := c.N) c.out), by simp, ?_⟩
    have : Tseitin.assignmentOf (n := n) c x (Var.node (n := n) (N := c.N) c.out) = true := by
      simpa [Tseitin.assignmentOf, Var.node, DAGCircuit.eval_def] using hx
    simp [this]

theorem circuitSAT_of_satisfiable (c : DAGCircuit AC0Gate n) :
    CNF.Formula.Satisfiable (sat (n := n) c) → Tseitin.CircuitSAT (n := n) c := by
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
  have hnodeClauses :
      ∀ i : Fin c.N, CNF.Formula.Satisfies (nodeClauses (n := n) (d := c.toDAG) i) σ := by
    intro i cl hcl
    have : cl ∈ core (n := n) c := by
      refine List.mem_flatten.2 ?_
      refine ⟨nodeClauses (n := n) (d := c.toDAG) i, ?_, hcl⟩
      exact List.mem_ofFn.2 ⟨i, rfl⟩
    exact hcore _ this
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
          exact (Tseitin.satisfies_eqvClauses_iff (n := n) (σ := σ)
            (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (w := Var.input (n := n) (N := c.N) j)).1
              (by simpa [nodeClauses, hnd] using hsatI)
        have hxj : σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = x j := by
          simpa [x] using heq
        simpa [DAG.evalAt_eq_node (d := c.toDAG) (x := x), hnd] using hxj
    | const b =>
        have : σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = b := by
          exact (Tseitin.satisfies_constClauses_iff (n := n) (σ := σ)
            (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (b := b)).1
              (by simpa [nodeClauses, hnd] using hsatI)
        simpa [Tseitin.assignmentOf, x, Var.node,
          DAG.evalAt_eq_node (d := c.toDAG) (x := x), hnd, this]
    | gate g f =>
        have hgate :
            σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩) =
              GateEval.eval (G := AC0Gate) g fun j =>
                σ (Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) ⟨i, hi⟩ (f j))) := by
          exact (satisfies_gateClauses_iff (n := n) (σ := σ) (g := g)
            (child := fun j =>
              Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) ⟨i, hi⟩ (f j)))
            (out := Var.node (n := n) (N := c.N) ⟨i, hi⟩)).1
              (by simpa [nodeClauses, hnd] using hsatI)
        have hchild :
            (j : Fin _) →
              σ (Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) ⟨i, hi⟩ (f j))) =
                c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
          intro j
          exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)
        have hfun :
            (fun j : Fin _ =>
              σ (Var.node (n := n) (N := c.N) (Tseitin.childToN (N := c.N) ⟨i, hi⟩ (f j)))) =
              fun j : Fin _ => c.toDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
          funext j
          exact hchild j
        have hEval := DAG.evalAt_eq_node (d := c.toDAG) (x := x) (i := i) (hi := hi)
        calc
          σ (Var.node (n := n) (N := c.N) ⟨i, hi⟩)
              = GateEval.eval (G := AC0Gate) g fun j =>
                  σ
                    (Var.node (n := n) (N := c.N)
                      (Tseitin.childToN (N := c.N) ⟨i, hi⟩ (f j))) := hgate
          _ = GateEval.eval (G := AC0Gate) g fun j =>
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

theorem equisatisfiable (c : DAGCircuit AC0Gate n) :
    CNF.Formula.Satisfiable (sat (n := n) c) ↔ Tseitin.CircuitSAT (n := n) c := by
  constructor
  · exact circuitSAT_of_satisfiable (n := n) c
  · intro h
    exact satisfiable_of_circuitSAT (n := n) c h

end AC0

end Tseitin

end Circuit

end Computability
