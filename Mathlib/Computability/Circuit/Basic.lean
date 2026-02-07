/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Boolean circuits (DAGs with explicit sharing)

This file defines Boolean circuits as *topologically indexed* DAGs.

In circuit complexity, a **circuit** is a DAG where gates can have arbitrary fan-out (sharing).
This contrasts with **formulas** (see `Formula` in `Formula/Basic.lean`) which are trees with
fan-out 1.

The key idea is to index nodes by natural numbers and require that a node at index `i` may only
refer to predecessors `< i`. This gives acyclicity and enables evaluation by simple recursion over
the prefix length. This representation is equivalent to a straight-line program.

## Main definitions

* `CircuitNode G n i`: a node at index `i` (input, constant, or gate referencing earlier nodes)
* `CircuitDAG G n`: the underlying DAG structure (nodes indexed 0 to N-1)
* `Circuit G n`: a DAG circuit with a designated output node

## Tags

circuit, Boolean, DAG, sharing, straight-line program, circuit complexity
-/

@[expose] public section

namespace Computability

open Gate

variable {G : Nat → Type} {n : Nat}

/-- A node at index `i` is either an input wire, a constant, or a gate whose children are indexed by
`Fin i` (so they are strictly earlier). -/
inductive CircuitNode (G : Nat → Type) (n : Nat) (i : Nat) : Type where
  | input : Fin n → CircuitNode G n i
  | const : Bool → CircuitNode G n i
  | gate : {k : Nat} → G k → (Fin k → Fin i) → CircuitNode G n i

namespace CircuitNode

variable {i : Nat}

section DecidableEq

variable [∀ k, DecidableEq (G k)]

/-- Decidable equality for circuit nodes, given decidable equality on gate labels. -/
protected def decEq : (nd₁ nd₂ : CircuitNode G n i) → Decidable (nd₁ = nd₂)
  | .input j₁, .input j₂ =>
      if h : j₁ = j₂ then isTrue (h ▸ rfl) else isFalse fun h' => by cases h'; exact h rfl
  | .const b₁, .const b₂ =>
      if h : b₁ = b₂ then isTrue (h ▸ rfl) else isFalse fun h' => by cases h'; exact h rfl
  | .gate (k := k₁) g₁ f₁, .gate (k := k₂) g₂ f₂ =>
      if hk : k₁ = k₂ then
        let g₂' : G k₁ := hk ▸ g₂
        let f₂' : Fin k₁ → Fin i := fun j => f₂ (hk ▸ j)
        if hg : g₁ = g₂' then
          if hf : ∀ j, f₁ j = f₂' j then
            isTrue (by subst hk hg; congr; funext j; exact hf j)
          else isFalse fun h => by cases h; exact hf fun _ => rfl
        else isFalse fun h => by cases h; exact hg rfl
      else isFalse fun h => by cases h; exact hk rfl
  | .input _, .const _ | .input _, .gate _ _ | .const _, .input _
  | .const _, .gate _ _ | .gate _ _, .input _ | .gate _ _, .const _ => isFalse nofun

instance [∀ k, DecidableEq (G k)] : DecidableEq (CircuitNode G n i) := CircuitNode.decEq

end DecidableEq

end CircuitNode

/-- A circuit DAG is given by a number of nodes `N` and an assignment of a node-description to each
index `i < N`. -/
structure CircuitDAG (G : Nat → Type) (n : Nat) : Type where
  /-- Number of nodes. -/
  N : Nat
  /-- Node-description at each index `i < N`. -/
  node : ∀ i : Nat, i < N → CircuitNode G n i

namespace CircuitDAG

/-- The empty DAG (with no nodes). -/
def empty (G : Nat → Type) (n : Nat) : CircuitDAG G n :=
  ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩

instance : Inhabited (CircuitDAG G n) :=
  ⟨empty G n⟩

/-- Append a new node at the end (at index `d.N`). -/
def snoc (d : CircuitDAG G n) (nd : CircuitNode G n d.N) : CircuitDAG G n :=
  ⟨d.N + 1, fun i hi =>
    if h : i < d.N then d.node i h else Nat.eq_of_lt_succ_of_not_lt hi h ▸ nd⟩

@[simp] theorem snoc_N (d : CircuitDAG G n) (nd : CircuitNode G n d.N) : (snoc d nd).N = d.N + 1 :=
  rfl

@[simp] theorem snoc_node_lt (d : CircuitDAG G n) (nd : CircuitNode G n d.N) {i : Nat}
    (hi : i < d.N) : (snoc d nd).node i (lt_trans hi (Nat.lt_succ_self _)) = d.node i hi := by
  simp [snoc, hi]

@[simp] theorem snoc_node_last (d : CircuitDAG G n) (nd : CircuitNode G n d.N) :
    (snoc d nd).node d.N (Nat.lt_succ_self _) = nd := by
  simp [snoc]

/-- `d₀` is a prefix of `d₁` if `d₁` has at least as many nodes and agrees with `d₀` on all earlier
nodes. -/
structure Prefix (d₀ d₁ : CircuitDAG G n) : Prop where
  le : d₀.N ≤ d₁.N
  node_eq : ∀ i (hi : i < d₀.N), d₁.node i (lt_of_lt_of_le hi le) = d₀.node i hi

namespace Prefix

theorem refl (d : CircuitDAG G n) : Prefix d d :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem trans {d₀ d₁ d₂ : CircuitDAG G n} (h₀₁ : Prefix d₀ d₁) (h₁₂ : Prefix d₁ d₂) :
    Prefix d₀ d₂ :=
  ⟨le_trans h₀₁.le h₁₂.le,
    fun i hi => by simpa [h₀₁.node_eq i hi] using h₁₂.node_eq i (lt_of_lt_of_le hi h₀₁.le)⟩

theorem snoc (d : CircuitDAG G n) (nd : CircuitNode G n d.N) : Prefix d (CircuitDAG.snoc d nd) :=
  ⟨Nat.le_succ _, fun i hi => by simpa using snoc_node_lt (d := d) (nd := nd) (hi := hi)⟩

end Prefix

/-- Rename inputs of a circuit DAG by applying `ρ` to input references. -/
def mapInputs {m : Nat} (ρ : Fin n → Fin m) (d : CircuitDAG G n) : CircuitDAG G m :=
  { N := d.N
    node := fun i hi =>
      match d.node i hi with
      | .input j => .input (ρ j)
      | .const b => .const b
      | .gate g f => .gate g f }

/-- Relabel gates of a circuit DAG using an arity-preserving map. -/
def mapGate {H : Nat → Type} (φ : GateHom G H) (d : CircuitDAG G n) : CircuitDAG H n :=
  { N := d.N
    node := fun i hi =>
      match d.node i hi with
      | .input j => .input j
      | .const b => .const b
      | .gate g f => .gate (φ.map g) f }

@[simp] theorem mapInputs_N {m : Nat} (ρ : Fin n → Fin m) (d : CircuitDAG G n) :
    (mapInputs ρ d).N = d.N :=
  rfl

@[simp] theorem mapGate_N {H : Nat → Type} (φ : GateHom G H) (d : CircuitDAG G n) :
    (d.mapGate φ).N = d.N :=
  rfl

@[simp] theorem mapInputs_id (d : CircuitDAG G n) :
    mapInputs id d = d := by
  simp only [mapInputs, id_eq]
  congr 1
  funext i hi
  cases d.node i hi <;> rfl

theorem mapInputs_comp {m ℓ : Nat} (ρ₁ : Fin n → Fin m) (ρ₂ : Fin m → Fin ℓ)
    (d : CircuitDAG G n) :
    mapInputs ρ₂ (mapInputs ρ₁ d) = mapInputs (fun i => ρ₂ (ρ₁ i)) d := by
  simp only [mapInputs]
  congr 1
  funext i hi
  cases d.node i hi <;> rfl

@[simp] theorem mapGate_id (d : CircuitDAG G n) :
    d.mapGate (GateHom.id G) = d := by
  simp only [mapGate]
  congr 1
  funext i hi
  cases d.node i hi <;> rfl

theorem mapGate_comp {H K : Nat → Type} (ψ : GateHom H K) (φ : GateHom G H) (d : CircuitDAG G n) :
    (d.mapGate φ).mapGate ψ = d.mapGate (GateHom.comp ψ φ) := by
  simp only [mapGate]
  congr 1
  funext i hi
  cases d.node i hi <;> rfl

section Eval

variable [GateEval G]

/-- Evaluate the first `m` nodes of a circuit DAG, producing a vector of Boolean values
of length `m`. -/
def evalVec (d : CircuitDAG G n) (x : Fin n → Bool) : (m : Nat) → (hm : m ≤ d.N) → Fin m → Bool
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

@[simp] theorem evalVec_zero (d : CircuitDAG G n) (x : Fin n → Bool) (hm : 0 ≤ d.N) :
    d.evalVec x 0 hm = Fin.elim0 :=
  rfl

/-- Proof-irrelevance for the `m ≤ N` argument of `evalVec`. -/
theorem evalVec_congr_hm (d : CircuitDAG G n) (x : Fin n → Bool) (m : Nat) {hm₁ hm₂ : m ≤ d.N} :
    d.evalVec x m hm₁ = d.evalVec x m hm₂ := by
  cases Subsingleton.elim hm₁ hm₂
  rfl

/-- Increasing the prefix length of `evalVec` does not change earlier entries. -/
theorem evalVec_castLE (d : CircuitDAG G n) (x : Fin n → Bool) (m : Nat) (hm : m ≤ d.N) :
    ∀ m' (hm' : m' ≤ d.N) (hmm' : m ≤ m') (i : Fin m),
      d.evalVec x m' hm' (Fin.castLE hmm' i) = d.evalVec x m hm i := by
  intro m' hm' hmm' i; induction m' with
  | zero => exact (Nat.le_zero.mp hmm' ▸ i).elim0
  | succ m' ih =>
      rcases Nat.lt_or_eq_of_le hmm' with hlt | rfl
      · have : Fin.castLE hmm' i = (Fin.castLE (Nat.lt_succ_iff.mp hlt) i).castSucc := by ext; simp
        simp only [evalVec, this, Fin.snoc_castSucc, ih (Nat.le_of_succ_le hm')]
      · simp

/-- Evaluate a node at index `i`. -/
def evalAt (d : CircuitDAG G n) (x : Fin n → Bool) (i : Nat) (hi : i < d.N) : Bool :=
  d.evalVec x d.N le_rfl ⟨i, hi⟩

/-- Unfold `evalAt` at a node by looking at the node label. -/
theorem evalAt_eq_node (d : CircuitDAG G n) (x : Fin n → Bool) {i : Nat} (hi : i < d.N) :
    d.evalAt x i hi =
      match d.node i hi with
      | .input j => x j
      | .const b => b
      | .gate g f =>
          GateEval.eval g fun j =>
            d.evalAt x (f j).1 (lt_trans (f j).2 hi) := by
  have hm : i + 1 ≤ d.N := Nat.succ_le_of_lt hi
  have hm' : i ≤ d.N := Nat.le_of_succ_le hm
  have heq : d.evalVec x d.N le_rfl ⟨i, hi⟩ = d.evalVec x (i + 1) hm (Fin.last i) := by
    simpa using d.evalVec_castLE x (i + 1) hm d.N le_rfl hm (Fin.last i)
  have hchild : ∀ j : Fin i, d.evalVec x i hm' j = d.evalAt x j (lt_trans j.isLt hi) := fun j =>
    by simpa using (d.evalVec_castLE x i hm' d.N le_rfl hm' j).symm
  cases hnd : d.node i hi <;> simpa [evalAt, evalVec, hnd, hchild] using heq

theorem evalAt_mapInputs {m : Nat} (ρ : Fin n → Fin m) (d : CircuitDAG G n) (x : Fin m → Bool)
    (i : Nat) (hi : i < d.N) :
    (mapInputs ρ d).evalAt x i hi = d.evalAt (fun j => x (ρ j)) i hi := by
  revert hi; refine Nat.strong_induction_on i ?_; intro i ih hi
  rw [evalAt_eq_node, evalAt_eq_node]
  cases hnd : d.node i hi with
  | input j => simp [CircuitDAG.mapInputs, hnd]
  | const b => simp [CircuitDAG.mapInputs, hnd]
  | gate g f =>
      simp only [CircuitDAG.mapInputs, hnd]
      congr 1; funext j; exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)

/-- If `d₀` is a prefix of `d₁`, then evaluation on any prefix length `m ≤ d₀.N` agrees. -/
theorem evalVec_eq_of_prefix {d₀ d₁ : CircuitDAG G n} (h : Prefix (G := G) (n := n) d₀ d₁)
    (x : Fin n → Bool) :
    ∀ m (hm : m ≤ d₀.N), d₁.evalVec x m (le_trans hm h.le) = d₀.evalVec x m hm := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih =>
      have hm0 : m ≤ d₀.N := Nat.le_of_succ_le hm
      have hn0 : m < d₀.N := Nat.lt_of_succ_le hm
      have hnode : d₁.node m (lt_of_lt_of_le hn0 h.le) = d₀.node m hn0 := by
        simpa using h.node_eq m hn0
      funext i; induction i using Fin.lastCases with
      | cast j => simp only [evalVec, Fin.snoc_castSucc]; exact congrFun (ih hm0) j
      | last => simp [evalVec, ih hm0, hnode]

/-- If `d₀` is a prefix of `d₁`, then evaluation of earlier nodes agrees. -/
theorem evalAt_eq_of_prefix {d₀ d₁ : CircuitDAG G n} (h : Prefix (G := G) (n := n) d₀ d₁)
    (x : Fin n → Bool) {i : Nat} (hi : i < d₀.N) :
    d₁.evalAt x i (lt_of_lt_of_le hi h.le) = d₀.evalAt x i hi := by
  simp only [evalAt]
  calc d₁.evalVec x d₁.N le_rfl ⟨i, _⟩
      = d₁.evalVec x d₀.N h.le ⟨i, hi⟩ := by
          simpa using d₁.evalVec_castLE x d₀.N h.le d₁.N le_rfl h.le ⟨i, hi⟩
    _ = d₀.evalVec x d₀.N le_rfl ⟨i, hi⟩ := congrFun (evalVec_eq_of_prefix h x d₀.N le_rfl) _

/-- Appending a node does not change the values of earlier nodes. -/
theorem evalAt_snoc_of_lt (d : CircuitDAG G n) (nd : CircuitNode G n d.N) (x : Fin n → Bool)
    {i : Nat} (hi : i < d.N) :
    (snoc d nd).evalAt x i (lt_trans hi (Nat.lt_succ_self _)) = d.evalAt x i hi := by
  simpa using evalAt_eq_of_prefix (Prefix.snoc d nd) x hi

/-- The value of the newly appended node. -/
theorem evalAt_snoc_last (d : CircuitDAG G n) (nd : CircuitNode G n d.N) (x : Fin n → Bool) :
    (snoc d nd).evalAt x d.N (Nat.lt_succ_self _) =
      match nd with
      | .input i => x i
      | .const b => b
      | .gate g f => GateEval.eval g fun j => d.evalAt x (f j).1 (f j).2 := by
  have hlast : (⟨d.N, Nat.lt_succ_self _⟩ : Fin (d.N + 1)) = Fin.last d.N := rfl
  have hvals : ∀ nd', (snoc d nd').evalVec x d.N (Nat.le_succ d.N) = d.evalVec x d.N le_rfl := by
    intro nd'; simpa using evalVec_eq_of_prefix (Prefix.snoc (nd := nd')) x d.N le_rfl
  unfold evalAt
  cases nd <;> simpa [hlast, evalAt] using (by simp [evalVec, CircuitDAG.snoc_node_last, hvals])

end Eval

end CircuitDAG

/-- A Boolean circuit is a DAG together with a designated output node.

In circuit complexity, circuits allow sharing (fan-out > 1), unlike formulas which are trees.
The size of a circuit is the number of nodes (gates + inputs + constants). -/
structure Circuit (G : Nat → Type) (n : Nat) : Type extends CircuitDAG G n where
  /-- Output node. -/
  out : Fin N

namespace Circuit

variable [GateEval G]

/-- Evaluate a circuit on an input assignment. -/
def eval (c : Circuit G n) (x : Fin n → Bool) : Bool :=
  c.toCircuitDAG.evalAt x c.out.1 c.out.2

@[simp] theorem eval_def (c : Circuit G n) (x : Fin n → Bool) :
    c.eval x = c.toCircuitDAG.evalAt x c.out.1 c.out.2 :=
  rfl

/-- The size of a circuit is the number of nodes. -/
def size (c : Circuit G n) : Nat :=
  c.N

omit [GateEval G] in
@[simp] theorem size_eq_N (c : Circuit G n) : c.size = c.N :=
  rfl

/-- Rename inputs of a circuit by applying `ρ` to input references. -/
def mapInputs {m : Nat} (ρ : Fin n → Fin m) (c : Circuit G n) : Circuit G m :=
  { N := c.N
    node := (CircuitDAG.mapInputs ρ c.toCircuitDAG).node
    out := c.out }

omit [GateEval G] in
@[simp] theorem mapInputs_size {m : Nat} (ρ : Fin n → Fin m) (c : Circuit G n) :
    (mapInputs ρ c).size = c.size :=
  rfl

omit [GateEval G] in
@[simp] theorem mapInputs_N {m : Nat} (ρ : Fin n → Fin m) (c : Circuit G n) :
    (mapInputs ρ c).N = c.N :=
  rfl

omit [GateEval G] in
@[simp] theorem mapInputs_out {m : Nat} (ρ : Fin n → Fin m) (c : Circuit G n) :
    (mapInputs ρ c).out = c.out :=
  rfl

theorem eval_mapInputs {m : Nat} (ρ : Fin n → Fin m) (c : Circuit G n) (x : Fin m → Bool) :
    (mapInputs ρ c).eval x = c.eval (fun i => x (ρ i)) := by
  simpa [Circuit.mapInputs, Circuit.eval] using CircuitDAG.evalAt_mapInputs
    (ρ := ρ) (d := c.toCircuitDAG) (x := x) (i := c.out.1) (hi := c.out.2)

omit [GateEval G] in
@[simp] theorem mapInputs_id (c : Circuit G n) :
    mapInputs id c = c := by
  obtain ⟨dag, out⟩ := c
  simp only [mapInputs, CircuitDAG.mapInputs]; congr 2; funext i hi; cases dag.node i hi <;> rfl

omit [GateEval G] in
theorem mapInputs_comp {m ℓ : Nat} (ρ₁ : Fin n → Fin m) (ρ₂ : Fin m → Fin ℓ) (c : Circuit G n) :
    mapInputs ρ₂ (mapInputs ρ₁ c) = mapInputs (fun i => ρ₂ (ρ₁ i)) c := by
  obtain ⟨dag, out⟩ := c
  simp only [mapInputs, CircuitDAG.mapInputs]; congr 2; funext i hi; cases dag.node i hi <;> rfl

end Circuit

section MapGate

variable {G H : Nat → Type} {n : Nat}

/-- Relabel gates of a circuit using an arity-preserving map. -/
def Circuit.mapGate (φ : GateHom G H) (c : Circuit G n) : Circuit H n :=
  { N := c.N
    node := (c.toCircuitDAG.mapGate φ).node
    out := c.out }

@[simp] theorem Circuit.mapGate_size (φ : GateHom G H) (c : Circuit G n) :
    (c.mapGate φ).size = c.size :=
  rfl

@[simp] theorem Circuit.mapGate_N (φ : GateHom G H) (c : Circuit G n) :
    (c.mapGate φ).N = c.N :=
  rfl

@[simp] theorem Circuit.mapGate_out (φ : GateHom G H) (c : Circuit G n) :
    (c.mapGate φ).out = c.out :=
  rfl

@[simp] theorem Circuit.mapGate_id (c : Circuit G n) :
    c.mapGate (GateHom.id G) = c := by
  obtain ⟨dag, out⟩ := c
  simp only [Circuit.mapGate, CircuitDAG.mapGate]; congr 2; funext i hi; cases dag.node i hi <;> rfl

theorem Circuit.mapGate_comp {K : Nat → Type} (ψ : GateHom H K) (φ : GateHom G H)
    (c : Circuit G n) :
    (c.mapGate φ).mapGate ψ = c.mapGate (GateHom.comp ψ φ) := by
  obtain ⟨dag, out⟩ := c
  simp only [Circuit.mapGate, CircuitDAG.mapGate]; congr 2; funext i hi; cases dag.node i hi <;> rfl

theorem CircuitDAG.evalAt_mapGate [GateEval G] [GateEval H] (φ : GateHom G H)
    (hφ : ∀ {k : Nat} (g : G k) (x : Fin k → Bool),
      GateEval.eval (G := H) (φ.map g) x = GateEval.eval (G := G) g x)
    (d : CircuitDAG G n) (x : Fin n → Bool) (i : Nat) (hi : i < d.N) :
    (d.mapGate φ).evalAt x i hi = d.evalAt x i hi := by
  revert hi; refine Nat.strong_induction_on i ?_; intro i ih hi
  rw [evalAt_eq_node, evalAt_eq_node]
  cases hnd : d.node i hi with
  | input j => simp [CircuitDAG.mapGate, hnd]
  | const b => simp [CircuitDAG.mapGate, hnd]
  | gate g f =>
      simp only [CircuitDAG.mapGate, hnd, hφ]
      congr 1; funext j; exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)

theorem Circuit.eval_mapGate [GateEval G] [GateEval H] (φ : GateHom G H)
    (hφ : ∀ {k : Nat} (g : G k) (x : Fin k → Bool),
      GateEval.eval (G := H) (φ.map g) x = GateEval.eval (G := G) g x)
    (c : Circuit G n) (x : Fin n → Bool) :
    (c.mapGate φ).eval x = c.eval x := by
  simp only [Circuit.eval, Circuit.mapGate]
  exact CircuitDAG.evalAt_mapGate φ hφ c.toCircuitDAG x c.out.1 c.out.2

end MapGate

end Computability
