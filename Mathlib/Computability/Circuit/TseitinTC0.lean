/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.TseitinAC0
public import Mathlib.Computability.Circuit.CNFThreshold
public import Mathlib.Computability.Gate
import Mathlib.Data.List.OfFn

/-!
# Compact Tseitin SAT encoding for `TC0` circuits

`Mathlib.Computability.Circuit.Tseitin` provides a generic Tseitin encoding using a truth-table CNF
for each gate, which is exponential in the gate arity.

This file defines a compact alternative for the standard `TC0` basis:

* `AC0` gates (`AND` / `OR` / `NOT`) are encoded using the linear-size constraints from
  `Mathlib.Computability.Circuit.TseitinAC0`.
* Threshold gates are encoded using a polynomial-size sequential-counter encoding from
  `Mathlib.Computability.Circuit.CNFThreshold`.

The output is a CNF formula over an extended variable type that includes auxiliary variables for
threshold gates.
-/

@[expose] public section

namespace Computability

open Gate

namespace Circuit

open CircuitDAG

namespace Tseitin

open CNF

namespace TC0

variable {n : Nat}

/-! ## Variables -/

/-- Auxiliary variables for the `TC0` encoding: tagged by a node index plus gate parameters. -/
abbrev Aux (N : Nat) : Type :=
  Fin N × Σ k : Nat, Σ t : Nat, CNFEnc.ThrAux k t

/-- Variables for the `TC0` Tseitin encoding: base Tseitin variables plus threshold auxiliaries. -/
abbrev VarTC (n N : Nat) : Type :=
  Sum (Var n N) (Aux N)

namespace VarTC

def base {N : Nat} (v : Var n N) : VarTC (n := n) N :=
  Sum.inl v

def thrAux {N : Nat} (i : Fin N) (k t : Nat) (u : CNFEnc.ThrAux k t) : VarTC (n := n) N :=
  Sum.inr ⟨i, ⟨k, ⟨t, u⟩⟩⟩

end VarTC

/-! ## Node clauses -/

def liftBase {N : Nat} : CNF.Formula (Var n N) → CNF.Formula (VarTC (n := n) N) :=
  CNF.Formula.mapVar (VarTC.base (n := n) (N := N))

def liftThr {N k t : Nat} (i : Fin N) :
    CNFEnc.ThrVar (Var n N) k t → VarTC (n := n) N
  | Sum.inl v => VarTC.base (n := n) (N := N) v
  | Sum.inr u => VarTC.thrAux (n := n) (N := N) i k t u

def nodeClauses (c : Circuit TC0Gate n) (i : Fin c.N) :
    CNF.Formula (VarTC (n := n) c.N) :=
  match c.node i.1 i.2 with
  | .input j =>
      liftBase (n := n) (N := c.N) <|
        eqvClauses (n := n) (N := c.N)
          (Var.node (n := n) (N := c.N) i)
          (Var.input (n := n) (N := c.N) j)
  | .const b =>
      liftBase (n := n) (N := c.N) <|
        constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b
  | .gate (k := k) g f =>
      match g with
      | .ac0 g0 =>
          let child : Fin k → Var n c.N :=
            fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))
          liftBase (n := n) (N := c.N) <|
            Tseitin.AC0.gateClauses (n := n) (N := c.N) g0 child (Var.node (n := n) (N := c.N) i)
      | .thr t =>
          let child : Fin k → Var n c.N :=
            fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))
          CNF.Formula.mapVar (liftThr (n := n) (N := c.N) (k := k) (t := t) i) <|
            CNFEnc.thrClauses (V := Var n c.N) k t child (Var.node (n := n) (N := c.N) i)

/-! ## Full encodings -/

def core (c : Circuit TC0Gate n) : CNF.Formula (VarTC (n := n) c.N) :=
  List.flatten (List.ofFn fun i : Fin c.N => nodeClauses (n := n) c i)

def sat (c : Circuit TC0Gate n) : CNF.Formula (VarTC (n := n) c.N) :=
  core (n := n) c ++
    [ [Lit.pos (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out))] ]

/-! ## Correctness -/

/--
A satisfying assignment for `TC0.sat` induced by an input assignment, with canonical threshold
auxiliaries.
-/
def assignmentOf (c : Circuit TC0Gate n) (x : Fin n → Bool) :
    VarTC (n := n) c.N → Bool
  | Sum.inl v => Tseitin.assignmentOf (n := n) c x v
  | Sum.inr ⟨i, ⟨k, ⟨t, u⟩⟩⟩ =>
      match c.node i.1 i.2 with
      | .gate (k := k') (.thr t') f =>
          if hk : k = k' then
            match hk with
            | rfl =>
                if ht : t = t' then
                  match ht with
                  | rfl =>
                      let child : Fin k → Var n c.N :=
                        fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))
                      CNFEnc.extend (V := Var n c.N) (k := k) (t := t)
                        (Tseitin.assignmentOf (n := n) c x) child (Sum.inr u)
                else
                  false
          else
            false
      | _ => false

theorem assignmentOf_satisfies_nodeClauses (c : Circuit TC0Gate n) (x : Fin n → Bool)
    (i : Fin c.N) :
    CNF.Formula.Satisfies (nodeClauses (n := n) c i) (assignmentOf (n := n) c x) := by
  classical
  set σ : VarTC (n := n) c.N → Bool := assignmentOf (n := n) c x with hσ
  set σBase : Var n c.N → Bool := Tseitin.assignmentOf (n := n) c x with hσBase
  have hσBase' : (fun v : Var n c.N => σ (VarTC.base (n := n) (N := c.N) v)) = σBase := by
    funext v
    simp [σ, σBase, assignmentOf, VarTC.base]
  cases hnd : c.node i.1 i.2 with
  | input j =>
      have hEq : σBase (Var.node (n := n) (N := c.N) i) =
          σBase (Var.input (n := n) (N := c.N) j) := by
        have hEval :=
          CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i.1) (hi := i.2)
        have : c.toCircuitDAG.evalAt x i.1 i.2 = x j := by
          simpa [hnd] using hEval
        simpa [σBase, hσBase, Tseitin.assignmentOf, Var.node, Var.input] using this
      have hbase :
          CNF.Formula.Satisfies
            (eqvClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i)
              (Var.input (n := n) (N := c.N) j))
            σBase :=
        (satisfies_eqvClauses_iff (n := n) (σ := σBase)
          (v := Var.node (n := n) (N := c.N) i) (w := Var.input (n := n) (N := c.N) j)).2 hEq
      have hlift :
          CNF.Formula.Satisfies
            (liftBase (n := n) (N := c.N) <|
              eqvClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i)
                (Var.input (n := n) (N := c.N) j))
            σ := by
        have hbase' :
            CNF.Formula.Satisfies
              (eqvClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i)
                (Var.input (n := n) (N := c.N) j))
              (fun v : Var n c.N => σ (VarTC.base (n := n) (N := c.N) v)) := by
          simpa [hσBase'] using hbase
        exact (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).2 hbase'
      simpa [nodeClauses, hnd] using hlift
  | const b =>
      have hEq : σBase (Var.node (n := n) (N := c.N) i) = b := by
        have hEval :=
          CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i.1) (hi := i.2)
        have : c.toCircuitDAG.evalAt x i.1 i.2 = b := by
          simpa [hnd] using hEval
        simpa [σBase, hσBase, Tseitin.assignmentOf, Var.node] using this
      have hbase :
          CNF.Formula.Satisfies
            (constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b)
            σBase :=
        (satisfies_constClauses_iff (n := n) (σ := σBase)
          (v := Var.node (n := n) (N := c.N) i) (b := b)).2 hEq
      have hlift :
          CNF.Formula.Satisfies
            (liftBase (n := n) (N := c.N) <|
              constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b)
            σ := by
        have hbase' :
            CNF.Formula.Satisfies
              (constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) i) b)
              (fun v : Var n c.N => σ (VarTC.base (n := n) (N := c.N) v)) := by
          simpa [hσBase'] using hbase
        exact (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).2 hbase'
      simpa [nodeClauses, hnd] using hlift
  | gate g f =>
      rename_i k
      cases g with
      | ac0 g0 =>
          let child : Fin _ → Var n c.N :=
            fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))
          have hEq : σBase (Var.node (n := n) (N := c.N) i) =
              GateEval.eval (G := AC0Gate) g0 (fun j => σBase (child j)) := by
            have hEval :=
              CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i.1) (hi := i.2)
            have :
                c.toCircuitDAG.evalAt x i.1 i.2 =
                  GateEval.eval (G := TC0Gate) (TC0Gate.ac0 (n := _) g0)
                    (fun j => c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 i.2)) := by
              simpa [hnd] using hEval
            simpa [σBase, hσBase, Tseitin.assignmentOf, Var.node, child, childToN,
              GateEval_eval_TC0Gate, TC0Gate_eval_ac0] using this
          have hbase :
              CNF.Formula.Satisfies
                (Tseitin.AC0.gateClauses (n := n) (N := c.N) g0 child
                  (Var.node (n := n) (N := c.N) i))
                σBase :=
            (Tseitin.AC0.satisfies_gateClauses_iff (n := n) (σ := σBase) (g := g0)
              (child := child) (out := Var.node (n := n) (N := c.N) i)).2 hEq
          have hlift :
              CNF.Formula.Satisfies
                (liftBase (n := n) (N := c.N) <|
                  Tseitin.AC0.gateClauses (n := n) (N := c.N) g0 child
                    (Var.node (n := n) (N := c.N) i))
                σ := by
            have hbase' :
                CNF.Formula.Satisfies
                  (Tseitin.AC0.gateClauses (n := n) (N := c.N) g0 child
                    (Var.node (n := n) (N := c.N) i))
                  (fun v : Var n c.N => σ (VarTC.base (n := n) (N := c.N) v)) := by
              simpa [hσBase'] using hbase
            exact
              (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).2 hbase'
          simpa [nodeClauses, hnd, child] using hlift
      | thr t =>
          let child : Fin k → Var n c.N :=
            fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) i (f j))
          have hEq : σBase (Var.node (n := n) (N := c.N) i) =
              decide (t ≤ countTrue (fun j => σBase (child j))) := by
            have hEval :=
              CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i.1) (hi := i.2)
            have :
                c.toCircuitDAG.evalAt x i.1 i.2 =
                  GateEval.eval (G := TC0Gate) (TC0Gate.thr (n := _) t)
                    (fun j => c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 i.2)) := by
              simpa [hnd] using hEval
            simpa [σBase, hσBase, Tseitin.assignmentOf, Var.node, child, childToN,
              GateEval_eval_TC0Gate, TC0Gate_eval_thr] using this
          have hthr :
              CNF.Formula.Satisfies
                (CNFEnc.thrClauses (V := Var n c.N) k t child (Var.node (n := n) (N := c.N) i))
                (CNFEnc.extend (V := Var n c.N) (k := k) (t := t) σBase child) := by
            exact
              CNFEnc.satisfies_thrClauses_complete (V := Var n c.N) (k := k) (t := t) child
                (Var.node (n := n) (N := c.N) i)
                σBase hEq
          have hliftThr :
              (fun v : CNFEnc.ThrVar (Var n c.N) k t =>
                  σ (liftThr (n := n) (N := c.N) (k := k) (t := t) i v)) =
                CNFEnc.extend (V := Var n c.N) (k := k) (t := t) σBase child := by
            funext v
            cases v with
            | inl v =>
                simp [liftThr, σ, σBase, assignmentOf, CNFEnc.extend, VarTC.base]
            | inr u =>
                simp [liftThr, σ, σBase, assignmentOf, CNFEnc.extend, VarTC.thrAux, hnd, child]
          have hlift :
              CNF.Formula.Satisfies
                (CNF.Formula.mapVar (liftThr (n := n) (N := c.N) (k := k) (t := t) i)
                  (CNFEnc.thrClauses (V := Var n c.N) k t child
                    (Var.node (n := n) (N := c.N) i)))
                σ := by
            have hthr' :
                CNF.Formula.Satisfies
                  (CNFEnc.thrClauses (V := Var n c.N) k t child (Var.node (n := n) (N := c.N) i))
                  (fun v => σ (liftThr (n := n) (N := c.N) (k := k) (t := t) i v)) := by
              simpa [hliftThr] using hthr
            exact
              (CNF.Formula.satisfies_mapVar_iff
                    (g := liftThr (n := n) (N := c.N) (k := k) (t := t) i)
                    _ σ).2 hthr'
          simpa [nodeClauses, hnd, child] using hlift

theorem assignmentOf_satisfies_core (c : Circuit TC0Gate n) (x : Fin n → Bool) :
    CNF.Formula.Satisfies (core (n := n) c) (assignmentOf (n := n) c x) := by
  intro cl hcl
  rcases List.mem_flatten.1 hcl with ⟨cs, hcs, hclcs⟩
  rcases List.mem_ofFn.1 hcs with ⟨i, rfl⟩
  exact assignmentOf_satisfies_nodeClauses (n := n) c x i _ hclcs

theorem satisfiable_of_circuitSAT (c : Circuit TC0Gate n) :
    Tseitin.CircuitSAT (n := n) c → CNF.Formula.Satisfiable (sat (n := n) c) := by
  rintro ⟨x, hx⟩
  refine ⟨assignmentOf (n := n) c x, ?_⟩
  intro cl hcl
  rcases List.mem_append.1 hcl with hcore | hout
  · exact assignmentOf_satisfies_core (n := n) c x _ hcore
  · rcases List.mem_singleton.1 hout with rfl
    refine
      ⟨Lit.pos (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out)),
        by simp, ?_⟩
    have :
        assignmentOf (n := n) c x
            (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out)) =
          true := by
      simpa [assignmentOf, VarTC.base, Tseitin.assignmentOf, Var.node, Circuit.eval_def] using hx
    simpa [Lit.eval, this]

theorem circuitSAT_of_satisfiable (c : Circuit TC0Gate n) :
    CNF.Formula.Satisfiable (sat (n := n) c) → Tseitin.CircuitSAT (n := n) c := by
  rintro ⟨σ, hσ⟩
  let σBase : Var n c.N → Bool := fun v => σ (VarTC.base (n := n) (N := c.N) v)
  let x : Fin n → Bool := fun i => σBase (Var.input (n := n) (N := c.N) i)
  have hcore : CNF.Formula.Satisfies (core (n := n) c) σ := by
    intro cl hcl
    exact hσ cl (by simp [sat, hcl])
  have hout :
      CNF.Clause.Satisfies
        [Lit.pos (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out))] σ := by
    have :
        [Lit.pos
            (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out))] ∈
          sat (n := n) c := by
      simp [sat]
    exact hσ _ this
  have hout' : σBase (Var.node (n := n) (N := c.N) c.out) = true := by
    have :
        Lit.eval σ
            (Lit.pos
              (VarTC.base (n := n) (N := c.N) (Var.node (n := n) (N := c.N) c.out))) =
          true := by
      exact (CNF.Clause.satisfies_singleton (σ := σ) _).1 (by simpa using hout)
    simpa [σBase, Lit.eval] using this
  have hnodeClauses :
      ∀ i : Fin c.N, CNF.Formula.Satisfies (nodeClauses (n := n) c i) σ := by
    intro i cl hcl
    have : cl ∈ core (n := n) c := by
      refine List.mem_flatten.2 ?_
      refine ⟨nodeClauses (n := n) c i, ?_, hcl⟩
      exact List.mem_ofFn.2 ⟨i, rfl⟩
    exact hcore _ this
  have hnode :
      ∀ i : Nat, ∀ hi : i < c.N,
        σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = c.toCircuitDAG.evalAt x i hi := by
    intro i
    refine Nat.strong_induction_on i ?_
    intro i ih hi
    have hsatI : CNF.Formula.Satisfies (nodeClauses (n := n) c ⟨i, hi⟩) σ :=
      hnodeClauses ⟨i, hi⟩
    cases hnd : c.node i hi with
    | input j =>
        have hbase :
            CNF.Formula.Satisfies
              (eqvClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) ⟨i, hi⟩)
                (Var.input (n := n) (N := c.N) j))
              σBase := by
          have :=
            (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).1
              (by simpa [nodeClauses, hnd, liftBase] using hsatI)
          simpa [σBase] using this
        have heq :
            σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) =
              σBase (Var.input (n := n) (N := c.N) j) := by
          exact satisfies_eqvClauses (n := n) (σ := σBase)
            (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (w := Var.input (n := n) (N := c.N) j) hbase
        have hxj : σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = x j := by
          simpa [x] using heq
        simpa [CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x), hnd] using hxj
    | const b =>
        have hbase :
            CNF.Formula.Satisfies
              (constClauses (n := n) (N := c.N) (Var.node (n := n) (N := c.N) ⟨i, hi⟩) b)
              σBase := by
          have :=
            (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).1
              (by simpa [nodeClauses, hnd, liftBase] using hsatI)
          simpa [σBase] using this
        have hb : σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) = b := by
          exact
            satisfies_constClauses (n := n) (σ := σBase)
              (v := Var.node (n := n) (N := c.N) ⟨i, hi⟩) (b := b) hbase
        simp [CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x), hnd, hb]
      | gate g f =>
          rename_i k
          cases g with
          | ac0 g0 =>
            let child : Fin k → Var n c.N :=
              fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j))
            have hbase :
                CNF.Formula.Satisfies
                  (Tseitin.AC0.gateClauses (n := n) (N := c.N) g0 child
                    (Var.node (n := n) (N := c.N) ⟨i, hi⟩))
                  σBase := by
              have :=
                (CNF.Formula.satisfies_mapVar_iff (g := VarTC.base (n := n) (N := c.N)) _ σ).1
                  (by simpa [nodeClauses, hnd, liftBase, child] using hsatI)
              simpa [σBase] using this
            have hgate :
                σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) =
                  GateEval.eval (G := AC0Gate) g0 (fun j => σBase (child j)) :=
              (Tseitin.AC0.satisfies_gateClauses_iff (n := n) (σ := σBase) (g := g0)
                (child := child) (out := Var.node (n := n) (N := c.N) ⟨i, hi⟩)).1 hbase
            have hchild :
                (j : Fin k) →
                  σBase (child j) = c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
              intro j
              exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)
            have hfun :
                (fun j : Fin k => σBase (child j)) =
                  fun j : Fin k => c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
              funext j
              exact hchild j
            have hEval :=
              CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i) (hi := hi)
            calc
              σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩)
                  = GateEval.eval (G := AC0Gate) g0 fun j => σBase (child j) := hgate
              _ =
                  GateEval.eval (G := AC0Gate) g0 fun j =>
                    c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
                      simp [hfun]
              _ = c.toCircuitDAG.evalAt x i hi := by
                    simpa [hnd, GateEval_eval_TC0Gate, TC0Gate_eval_ac0] using hEval.symm
          | thr t =>
              let child : Fin k → Var n c.N :=
                fun j => Var.node (n := n) (N := c.N) (childToN (N := c.N) ⟨i, hi⟩ (f j))
              let σThr : CNFEnc.ThrVar (Var n c.N) k t → Bool :=
                fun v => σ (liftThr (n := n) (N := c.N) (k := k) (t := t) ⟨i, hi⟩ v)
              have hthr :
                  CNF.Formula.Satisfies
                    (CNFEnc.thrClauses (V := Var n c.N) k t child
                      (Var.node (n := n) (N := c.N) ⟨i, hi⟩))
                    σThr := by
                have :=
                  (CNF.Formula.satisfies_mapVar_iff
                        (g := liftThr (n := n) (N := c.N) (k := k) (t := t) ⟨i, hi⟩)
                        _ σ).1
                    (by simpa [nodeClauses, hnd, child] using hsatI)
                simpa [σThr] using this
              have hgate :
                  σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) =
                    decide (t ≤ countTrue (fun j => σBase (child j))) := by
                have hsound :=
                  CNFEnc.satisfies_thrClauses_sound (V := Var n c.N) k t child
                    (Var.node (n := n) (N := c.N) ⟨i, hi⟩) σThr hthr
                have houtVar :
                    σThr
                        (CNFEnc.inVar (V := Var n c.N) (k := k) (t := t)
                          (Var.node (n := n) (N := c.N) ⟨i, hi⟩)) =
                      σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩) := by
                  simp [σThr, σBase, liftThr, CNFEnc.inVar, VarTC.base]
                have hchildVar :
                    (fun j : Fin k =>
                        σThr (CNFEnc.inVar (V := Var n c.N) (k := k) (t := t) (child j))) =
                      fun j : Fin k => σBase (child j) := by
                  funext j
                  simp [σThr, σBase, liftThr, CNFEnc.inVar, VarTC.base]
                simpa [houtVar, hchildVar] using hsound
              have hchild :
                  (j : Fin k) →
                    σBase (child j) = c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
                intro j
                exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)
              have hfun :
                  (fun j : Fin k => σBase (child j)) =
                    fun j : Fin k => c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
                funext j
                exact hchild j
              have hEval :=
              CircuitDAG.evalAt_eq_node (d := c.toCircuitDAG) (x := x) (i := i) (hi := hi)
              calc
                σBase (Var.node (n := n) (N := c.N) ⟨i, hi⟩)
                    = decide (t ≤ countTrue (fun j => σBase (child j))) := hgate
                _ =
                    decide (t ≤
                      countTrue fun j =>
                        c.toCircuitDAG.evalAt x (f j).1 (lt_trans (f j).2 hi)) := by
                      simp [hfun]
                _ = c.toCircuitDAG.evalAt x i hi := by
                      simpa [hnd, GateEval_eval_TC0Gate, TC0Gate_eval_thr] using hEval.symm
  refine ⟨x, ?_⟩
  have houtEval : c.eval x = σBase (Var.node (n := n) (N := c.N) c.out) := by
    simpa [Circuit.eval_def, Var.node, σBase] using (hnode c.out.1 c.out.2).symm
  calc
    c.eval x = σBase (Var.node (n := n) (N := c.N) c.out) := houtEval
    _ = true := hout'

theorem equisatisfiable (c : Circuit TC0Gate n) :
    CNF.Formula.Satisfiable (sat (n := n) c) ↔ Tseitin.CircuitSAT (n := n) c := by
  constructor
  · exact circuitSAT_of_satisfiable (n := n) c
  · intro h
    exact satisfiable_of_circuitSAT (n := n) c h

end TC0

end Tseitin

end Circuit

end Computability
