/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.Gate
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# DAG circuits (explicit sharing)

This file defines a *topologically indexed* DAG representation of Boolean circuits.

The key idea is to index nodes by natural numbers and require that a node at index `i` may only
refer to predecessors `< i`. This gives acyclicity and enables evaluation by simple recursion over
the prefix length.
-/

@[expose] public section

namespace Computability

namespace Circuit

variable {G : Nat → Type} {n : Nat}

/-- A node at index `i` is either an input wire, a constant, or a gate whose children are indexed by
`Fin i` (so they are strictly earlier). -/
inductive DAGNode (G : Nat → Type) (n : Nat) (i : Nat) : Type where
  | input : Fin n → DAGNode G n i
  | const : Bool → DAGNode G n i
  | gate : {k : Nat} → G k → (Fin k → Fin i) → DAGNode G n i

namespace DAGNode

variable {i : Nat}

@[simp] theorem gate_mk {k : Nat} (g : G k) (f : Fin k → Fin i) :
    DAGNode.gate (G := G) (n := n) (i := i) g f = .gate g f :=
  rfl

end DAGNode

/-- A DAG is given by a number of nodes `N` and an assignment of a node-description to each
index `i < N`. -/
structure DAG (G : Nat → Type) (n : Nat) : Type where
  /-- Number of nodes. -/
  N : Nat
  /-- Node-description at each index `i < N`. -/
  node : ∀ i : Nat, i < N → DAGNode G n i

namespace DAG

/-- The empty DAG (with no nodes). -/
def empty (G : Nat → Type) (n : Nat) : DAG G n :=
  ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩

instance : Inhabited (DAG G n) :=
  ⟨empty G n⟩

/-- Append a new node at the end (at index `d.N`). -/
def snoc (d : DAG G n) (nd : DAGNode G n d.N) : DAG G n :=
  ⟨d.N + 1, fun i hi =>
    by
      by_cases h : i < d.N
      · exact d.node i h
      · have : i = d.N := Nat.eq_of_lt_succ_of_not_lt hi h
        subst this
        exact nd⟩

@[simp] theorem snoc_N (d : DAG G n) (nd : DAGNode G n d.N) : (snoc d nd).N = d.N + 1 :=
  rfl

@[simp] theorem snoc_node_lt (d : DAG G n) (nd : DAGNode G n d.N) {i : Nat} (hi : i < d.N) :
    (snoc d nd).node i (lt_trans hi (Nat.lt_succ_self _)) = d.node i hi := by
  simp [snoc, hi]

@[simp] theorem snoc_node_last (d : DAG G n) (nd : DAGNode G n d.N) :
    (snoc d nd).node d.N (Nat.lt_succ_self _) = nd := by
  simp [snoc]

/-- `d₀` is a prefix of `d₁` if `d₁` has at least as many nodes and agrees with `d₀` on all earlier
nodes. -/
structure Prefix (d₀ d₁ : DAG G n) : Prop where
  le : d₀.N ≤ d₁.N
  node_eq : ∀ i (hi : i < d₀.N), d₁.node i (lt_of_lt_of_le hi le) = d₀.node i hi

namespace Prefix

theorem refl (d : DAG G n) : Prefix d d :=
  ⟨le_rfl, by intro i hi; rfl⟩

theorem trans {d₀ d₁ d₂ : DAG G n} (h₀₁ : Prefix d₀ d₁) (h₁₂ : Prefix d₁ d₂) : Prefix d₀ d₂ := by
  refine ⟨le_trans h₀₁.le h₁₂.le, ?_⟩
  intro i hi
  simpa [h₀₁.node_eq i hi] using
    (h₁₂.node_eq i (lt_of_lt_of_le hi h₀₁.le))

theorem snoc (d : DAG G n) (nd : DAGNode G n d.N) : Prefix d (snoc d nd) := by
  refine ⟨Nat.le_succ _, ?_⟩
  intro i hi
  simpa using (snoc_node_lt (d := d) (nd := nd) (hi := hi))

end Prefix

/-- Rename inputs of a DAG by applying `ρ` to input references. -/
def mapInputs {m : Nat} (d : DAG G n) (ρ : Fin n → Fin m) : DAG G m :=
  { N := d.N
    node := fun i hi =>
      match d.node i hi with
      | .input j => .input (ρ j)
      | .const b => .const b
      | .gate g f => .gate g f }

/-- Relabel gates of a DAG using an arity-preserving map. -/
def mapGate {H : Nat → Type} (φ : GateHom G H) (d : DAG G n) : DAG H n :=
  { N := d.N
    node := fun i hi =>
      match d.node i hi with
      | .input j => .input j
      | .const b => .const b
      | .gate g f => .gate (φ.map g) f }

@[simp] theorem mapInputs_N {m : Nat} (d : DAG G n) (ρ : Fin n → Fin m) :
    (d.mapInputs ρ).N = d.N :=
  rfl

@[simp] theorem mapGate_N {H : Nat → Type} (φ : GateHom G H) (d : DAG G n) :
    (d.mapGate φ).N = d.N :=
  rfl

section Eval

variable [GateEval G]

/-- Evaluate the first `m` nodes of a DAG, producing a vector of Boolean values of length `m`. -/
def evalVec (d : DAG G n) (x : Fin n → Bool) : (m : Nat) → (hm : m ≤ d.N) → Fin m → Bool
  | 0, _ => Fin.elim0
  | m + 1, hm =>
      let vals := evalVec d x m (le_trans (Nat.le_succ m) hm)
      let nd := d.node m (lt_of_lt_of_le (Nat.lt_succ_self m) hm)
      let v : Bool :=
        match nd with
        | .input i => x i
        | .const b => b
        | .gate g f => GateEval.eval g fun j => vals (f j)
      Fin.snoc vals v

@[simp] theorem evalVec_zero (d : DAG G n) (x : Fin n → Bool) (hm : 0 ≤ d.N) :
    d.evalVec x 0 hm = Fin.elim0 := by
  rfl

/-- Proof-irrelevance for the `m ≤ N` argument of `evalVec`. -/
theorem evalVec_congr_hm (d : DAG G n) (x : Fin n → Bool) (m : Nat) {hm₁ hm₂ : m ≤ d.N} :
    d.evalVec x m hm₁ = d.evalVec x m hm₂ := by
  cases Subsingleton.elim hm₁ hm₂
  rfl

/-- Increasing the prefix length of `evalVec` does not change earlier entries. -/
theorem evalVec_castLE (d : DAG G n) (x : Fin n → Bool) (m : Nat) (hm : m ≤ d.N) :
    ∀ m' (hm' : m' ≤ d.N) (hmm' : m ≤ m') (i : Fin m),
      d.evalVec x m' hm' (Fin.castLE hmm' i) = d.evalVec x m hm i := by
  intro m' hm' hmm' i
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmm'
  have aux :
      ∀ t (hm_t : m + t ≤ d.N),
        d.evalVec x (m + t) hm_t (Fin.castAdd t i) = d.evalVec x m hm i := by
    intro t hm_t
    induction t with
    | zero =>
        simp [evalVec_congr_hm (d := d) (x := x) (m := m) (hm₁ := hm_t) (hm₂ := hm)]
    | succ t ih =>
        have hm_succ : m + t + 1 ≤ d.N := by
          simpa [Nat.add_assoc] using hm_t
        have hm_prev : m + t ≤ d.N :=
          le_trans (Nat.le_succ (m + t)) hm_succ
        have hcastSucc :
            (Fin.castAdd (t + 1) i : Fin (m + t + 1)) =
              Fin.castSucc (Fin.castAdd t i) := by
          simpa using (Fin.castSucc_castAdd (m := t) (i := i)).symm
        calc
          d.evalVec x (m + t + 1) hm_succ (Fin.castAdd (t + 1) i)
              = d.evalVec x (m + t + 1) hm_succ (Fin.castSucc (Fin.castAdd t i)) := by
                simp [hcastSucc]
          _ = d.evalVec x (m + t) hm_prev (Fin.castAdd t i) := by
                simp [evalVec]
          _ = d.evalVec x m hm i := ih hm_prev
  have hcast : (Fin.castLE hmm' i : Fin (m + t)) = Fin.castAdd t i := by
    ext
    rfl
  simpa [hcast] using aux t hm'

/-- Evaluate a node at index `i`. -/
def evalAt (d : DAG G n) (x : Fin n → Bool) (i : Nat) (hi : i < d.N) : Bool :=
  d.evalVec x d.N le_rfl ⟨i, hi⟩

/-- Unfold `evalAt` at a node by looking at the node label. -/
theorem evalAt_eq_node (d : DAG G n) (x : Fin n → Bool) {i : Nat} (hi : i < d.N) :
    d.evalAt x i hi =
      match d.node i hi with
      | .input j => x j
      | .const b => b
      | .gate g f =>
          GateEval.eval g fun j =>
            d.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
  -- Reduce to evaluation at prefix length `i+1`.
  have hm : i + 1 ≤ d.N := Nat.succ_le_of_lt hi
  have hcast : (Fin.castLE hm (Fin.last i) : Fin d.N) = ⟨i, hi⟩ := by
    ext
    rfl
  have heq :
      d.evalVec x d.N le_rfl ⟨i, hi⟩ = d.evalVec x (i + 1) hm (Fin.last i) := by
    calc
      d.evalVec x d.N le_rfl ⟨i, hi⟩
          = d.evalVec x d.N le_rfl (Fin.castLE hm (Fin.last i)) := by
              simp [hcast]
      _ = d.evalVec x (i + 1) hm (Fin.last i) := by
          simpa using (d.evalVec_castLE (x := x) (m := i + 1) (hm := hm) d.N le_rfl hm (Fin.last i))
  -- Unfold one step of `evalVec` at length `i+1`. The `node` proof is propositionally irrelevant.
  have hi0 : i < d.N := lt_of_lt_of_le (Nat.lt_succ_self i) hm
  have hi0_eq : hi0 = hi := Subsingleton.elim _ _
  cases hi0_eq
  -- Replace child values `vals (f j)` by `evalAt` of the corresponding earlier node.
  cases hnd : d.node i hi with
  | input j =>
      simpa [evalAt, evalVec, hnd] using heq
  | const b =>
      simpa [evalAt, evalVec, hnd] using heq
  | gate g f =>
      have hchild :
          (j : Fin _) → d.evalVec x i (le_trans (Nat.le_succ i) hm) (f j) =
            d.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
        intro j
        have hm0 : i ≤ d.N := le_trans (Nat.le_succ i) hm
        have hcast0 :
            (Fin.castLE hm0 (f j) : Fin d.N) = ⟨(f j).1, lt_trans (f j).2 hi⟩ := by
          ext
          rfl
        have :=
          d.evalVec_castLE (x := x) (m := i) (hm := hm0) d.N le_rfl hm0 (f j)
        -- `evalAt` is evaluation at full length `N`, so cast down to length `i`.
        simpa [evalAt, hcast0] using this.symm
      simpa [evalAt, evalVec, hnd, hchild] using heq

theorem evalAt_mapInputs {m : Nat} (d : DAG G n) (ρ : Fin n → Fin m) (x : Fin m → Bool)
    (i : Nat) (hi : i < d.N) :
    (d.mapInputs ρ).evalAt x i hi = d.evalAt (fun j => x (ρ j)) i hi := by
  revert hi
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  have hi' : i < (d.mapInputs ρ).N := by
    simpa using hi
  -- unfold `evalAt` on both sides by the node label of `d` at `i`
  cases hnd : d.node i hi with
  | input j =>
      rw [evalAt_eq_node (d := d.mapInputs ρ) (x := x) (hi := hi')]
      rw [evalAt_eq_node (d := d) (x := fun t => x (ρ t)) (hi := hi)]
      simp [DAG.mapInputs, hnd]
  | const b =>
      rw [evalAt_eq_node (d := d.mapInputs ρ) (x := x) (hi := hi')]
      rw [evalAt_eq_node (d := d) (x := fun t => x (ρ t)) (hi := hi)]
      simp [DAG.mapInputs, hnd]
  | gate g f =>
      rw [evalAt_eq_node (d := d.mapInputs ρ) (x := x) (hi := hi')]
      rw [evalAt_eq_node (d := d) (x := fun t => x (ρ t)) (hi := hi)]
      have hnode : (d.mapInputs ρ).node i hi' = DAGNode.gate g f := by
        simp [DAG.mapInputs, hnd]
      have hchild :
          (j : Fin _) →
            (d.mapInputs ρ).evalAt x (f j).1 (lt_trans (f j).2 hi') =
              d.evalAt (fun t => x (ρ t)) (f j).1 (lt_trans (f j).2 hi) := by
        intro j
        exact (ih (f j).1 (f j).2) (lt_trans (f j).2 hi)
      have hfun :
          (fun j => (d.mapInputs ρ).evalAt x (f j).1 (lt_trans (f j).2 hi')) =
            fun j => d.evalAt (fun t => x (ρ t)) (f j).1 (lt_trans (f j).2 hi) := by
        funext j
        exact hchild j
      -- reduce the node labels, then rewrite the child-evaluation function
      simp [hnode, hnd, hfun]

/-- If `d₀` is a prefix of `d₁`, then evaluation on any prefix length `m ≤ d₀.N` agrees. -/
theorem evalVec_eq_of_prefix {d₀ d₁ : DAG G n} (h : Prefix (G := G) (n := n) d₀ d₁)
    (x : Fin n → Bool) :
    ∀ m (hm : m ≤ d₀.N), d₁.evalVec x m (le_trans hm h.le) = d₀.evalVec x m hm := by
  intro m hm
  induction m with
  | zero =>
      -- both sides are `Fin.elim0`
      rfl
  | succ m ih =>
      have hm0 : m ≤ d₀.N := le_trans (Nat.le_succ m) hm
      have hm1 : m ≤ d₁.N := le_trans hm0 h.le
      have hm1s : m + 1 ≤ d₁.N := le_trans hm h.le
      have hrec : d₁.evalVec x m hm1 = d₀.evalVec x m hm0 :=
        ih (hm := hm0)
      -- The recursive call inside `evalVec` uses `le_trans (Nat.le_succ m) hm1s`, which is
      -- propositionally equal to `hm1`.
      have hrec1 :
          d₁.evalVec x m (le_trans (Nat.le_succ m) hm1s) = d₁.evalVec x m hm1 :=
        evalVec_congr_hm (d := d₁) (x := x) (m := m)
          (hm₁ := le_trans (Nat.le_succ m) hm1s) (hm₂ := hm1)
      funext i
      induction i using Fin.lastCases with
      | cast j =>
          -- `Fin.snoc` agrees with the prefix on `castSucc`
          have hcast₁ :
              (d₁.evalVec x (m + 1) hm1s) (Fin.castSucc j) = (d₁.evalVec x m hm1) j := by
            simp [evalVec, hrec1]
          have hcast₀ :
              (d₀.evalVec x (m + 1) hm) (Fin.castSucc j) = (d₀.evalVec x m hm0) j := by
            simp [evalVec]
          -- reduce to the induction hypothesis at length `m`
          simpa [hcast₀, hcast₁] using congrArg (fun f => f j) hrec
      | last =>
          have hn0 : m < d₀.N := lt_of_lt_of_le (Nat.lt_succ_self m) hm
          have hn1' : m < d₁.N := lt_of_lt_of_le hn0 h.le
          have hn1_def : m < d₁.N := lt_of_lt_of_le (Nat.lt_succ_self m) hm1s
          have hproof : hn1_def = hn1' := Subsingleton.elim _ _
          have hnode : d₁.node m hn1_def = d₀.node m hn0 := by
            subst hproof
            simpa using h.node_eq m hn0
          -- `Fin.snoc` at `last` yields the freshly computed value.
          simp [evalVec, hrec1, hnode, hrec]

/-- If `d₀` is a prefix of `d₁`, then evaluation of earlier nodes agrees. -/
theorem evalAt_eq_of_prefix {d₀ d₁ : DAG G n} (h : Prefix (G := G) (n := n) d₀ d₁)
    (x : Fin n → Bool) {i : Nat} (hi : i < d₀.N) :
    d₁.evalAt x i (lt_of_lt_of_le hi h.le) = d₀.evalAt x i hi := by
  set j : Fin d₀.N := ⟨i, hi⟩
  have hj : (Fin.castLE h.le j : Fin d₁.N) = ⟨i, lt_of_lt_of_le hi h.le⟩ := by
    ext
    rfl
  unfold evalAt
  -- first, reduce evaluation in `d₁` at length `d₁.N` to evaluation at length `d₀.N`
  have hlen :
      d₁.evalVec x d₁.N le_rfl (Fin.castLE h.le j) = d₁.evalVec x d₀.N h.le j := by
    simpa using (evalVec_castLE (d := d₁) (x := x) (m := d₀.N) (hm := h.le)
      d₁.N le_rfl h.le j)
  -- then use prefix-equality of `evalVec` at length `d₀.N`
  have hvec : d₁.evalVec x d₀.N h.le j = d₀.evalVec x d₀.N le_rfl j := by
    have hvec' := evalVec_eq_of_prefix (d₀ := d₀) (d₁ := d₁) (h := h) (x := x) d₀.N le_rfl
    simpa using congrArg (fun f => f j) hvec'
  simpa [hj] using hlen.trans hvec

/-- Appending a node does not change the values of earlier nodes. -/
theorem evalAt_snoc_of_lt (d : DAG G n) (nd : DAGNode G n d.N) (x : Fin n → Bool) {i : Nat}
    (hi : i < d.N) :
    (snoc d nd).evalAt x i (lt_trans hi (Nat.lt_succ_self _)) = d.evalAt x i hi := by
  have hsnoc : Prefix (G := G) (n := n) d (snoc d nd) := Prefix.snoc (d := d) (nd := nd)
  simpa using
    (evalAt_eq_of_prefix (d₀ := d) (d₁ := snoc d nd) (h := hsnoc) (x := x) (i := i) (hi := hi))

/-- The value of the newly appended node. -/
theorem evalAt_snoc_last (d : DAG G n) (nd : DAGNode G n d.N) (x : Fin n → Bool) :
    (snoc d nd).evalAt x d.N (Nat.lt_succ_self _) =
      match nd with
      | .input i => x i
      | .const b => b
      | .gate g f => GateEval.eval g fun j => d.evalAt x (f j).1 (f j).2 := by
  have hlast : (⟨d.N, Nat.lt_succ_self _⟩ : Fin (d.N + 1)) = Fin.last d.N := rfl
  cases nd with
  | input i =>
      unfold evalAt
      simpa [hlast] using (by simp [evalVec, DAG.snoc_node_last])
  | const b =>
      unfold evalAt
      simpa [hlast] using (by simp [evalVec, DAG.snoc_node_last])
  | gate g f =>
      have hprefix : Prefix (G := G) (n := n) d (snoc d (DAGNode.gate g f)) :=
        Prefix.snoc (d := d) (nd := DAGNode.gate g f)
      have hvals :
          (snoc d (DAGNode.gate g f)).evalVec x d.N (Nat.le_succ d.N) =
            d.evalVec x d.N le_rfl := by
        have hvec :=
          evalVec_eq_of_prefix (d₀ := d) (d₁ := snoc d (DAGNode.gate g f)) (h := hprefix) (x := x)
            d.N le_rfl
        simpa using hvec
      unfold evalAt
      -- `Fin.snoc` at `last` yields the value computed for the new node.
      simpa [hlast, evalAt] using (by simp [evalVec, DAG.snoc_node_last, hvals])

end Eval

end DAG

/-- A DAG circuit is a DAG together with a designated output node. -/
structure DAGCircuit (G : Nat → Type) (n : Nat) : Type extends DAG G n where
  /-- Output node. -/
  out : Fin N

namespace DAGCircuit

variable [GateEval G]

/-- Evaluate a DAG circuit. -/
def eval (c : DAGCircuit G n) (x : Fin n → Bool) : Bool :=
  c.toDAG.evalAt x c.out.1 c.out.2

@[simp] theorem eval_def (c : DAGCircuit G n) (x : Fin n → Bool) :
    c.eval x = c.toDAG.evalAt x c.out.1 c.out.2 :=
  rfl

/-- The size of a DAG circuit is the number of nodes. -/
def size (c : DAGCircuit G n) : Nat :=
  c.N

/-- Rename inputs of a DAG circuit by applying `ρ` to input references. -/
def mapInputs {m : Nat} (c : DAGCircuit G n) (ρ : Fin n → Fin m) : DAGCircuit G m :=
  { N := c.N
    node := (c.toDAG.mapInputs ρ).node
    out := c.out }

omit [GateEval G] in
@[simp] theorem mapInputs_size {m : Nat} (c : DAGCircuit G n) (ρ : Fin n → Fin m) :
    (c.mapInputs ρ).size = c.size :=
  rfl

theorem eval_mapInputs {m : Nat} (c : DAGCircuit G n) (ρ : Fin n → Fin m) (x : Fin m → Bool) :
    (c.mapInputs ρ).eval x = c.eval (fun i => x (ρ i)) := by
  simpa [DAGCircuit.mapInputs, DAGCircuit.eval] using
    (DAG.evalAt_mapInputs (d := c.toDAG) (ρ := ρ) (x := x) (i := c.out.1) (hi := c.out.2))

end DAGCircuit

end Circuit

end Computability
