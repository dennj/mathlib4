/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.DAG
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Complexity measures for DAG circuits

This file defines a depth measure for DAG circuits (explicit sharing).

The key idea is the same as for evaluation: because nodes are topologically indexed, we can compute
depths by simple recursion over the prefix length.
-/

@[expose] public section

namespace Computability

namespace Circuit

open DAG

variable {G : Nat → Type} {n : Nat}

namespace DAG

/-- Compute the depth of the first `m` nodes of a DAG, producing a vector of naturals of length `m`.

Inputs and constants have depth `0`. A gate has depth `1 + max(depth(children))` (with `0` for a
nullary gate). -/
def depthVec (d : DAG G n) : (m : Nat) → (hm : m ≤ d.N) → Fin m → Nat
  | 0, _ => Fin.elim0
  | m + 1, hm =>
      let ds := depthVec d m (le_trans (Nat.le_succ m) hm)
      let nd := d.node m (lt_of_lt_of_le (Nat.lt_succ_self m) hm)
      let v : Nat :=
        match nd with
        | .input _ => 0
        | .const _ => 0
        | .gate (k := k) _ f =>
            (Finset.sup (Finset.univ : Finset (Fin k)) fun i : Fin k => ds (f i)) + 1
      Fin.snoc ds v

/-! ## Basic lemmas -/

/-- Proof-irrelevance for the `m ≤ N` argument of `depthVec`. -/
theorem depthVec_congr_hm (d : DAG G n) (m : Nat) {hm₁ hm₂ : m ≤ d.N} :
    d.depthVec m hm₁ = d.depthVec m hm₂ := by
  cases Subsingleton.elim hm₁ hm₂
  rfl

/-- Increasing the prefix length of `depthVec` does not change earlier entries. -/
theorem depthVec_castLE (d : DAG G n) (m : Nat) (hm : m ≤ d.N) :
    ∀ m' (hm' : m' ≤ d.N) (hmm' : m ≤ m') (i : Fin m),
      d.depthVec m' hm' (Fin.castLE hmm' i) = d.depthVec m hm i := by
  intro m' hm' hmm' i
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmm'
  have aux :
      ∀ t (hm_t : m + t ≤ d.N),
        d.depthVec (m + t) hm_t (Fin.castAdd t i) = d.depthVec m hm i := by
    intro t hm_t
    induction t with
    | zero =>
        simp [depthVec_congr_hm (d := d) (m := m) (hm₁ := hm_t) (hm₂ := hm)]
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
          d.depthVec (m + t + 1) hm_succ (Fin.castAdd (t + 1) i)
              = d.depthVec (m + t + 1) hm_succ (Fin.castSucc (Fin.castAdd t i)) := by
                  simp [hcastSucc]
          _ = d.depthVec (m + t) hm_prev (Fin.castAdd t i) := by
                simp [depthVec]
          _ = d.depthVec m hm i := ih hm_prev
  have hcast : (Fin.castLE hmm' i : Fin (m + t)) = Fin.castAdd t i := by
    ext
    rfl
  simpa [hcast] using aux t hm'

/-- Depth of a node at index `i`. -/
def depthAt (d : DAG G n) (i : Nat) (hi : i < d.N) : Nat :=
  d.depthVec d.N le_rfl ⟨i, hi⟩

@[simp] theorem depthAt_def (d : DAG G n) (i : Nat) (hi : i < d.N) :
    d.depthAt i hi = d.depthVec d.N le_rfl ⟨i, hi⟩ :=
  rfl

/-- Unfold `depthAt` at a node by looking at the node label. -/
theorem depthAt_eq_node (d : DAG G n) {i : Nat} (hi : i < d.N) :
    d.depthAt i hi =
      match d.node i hi with
      | .input _ => 0
      | .const _ => 0
      | .gate (k := k) _ f =>
          (Finset.sup (Finset.univ : Finset (Fin k)) fun j : Fin k =>
                d.depthAt (f j).1 (lt_trans (f j).2 hi)) +
            1 := by
  -- Reduce to evaluation at prefix length `i+1`.
  have hm : i + 1 ≤ d.N := Nat.succ_le_of_lt hi
  have hcast : (Fin.castLE hm (Fin.last i) : Fin d.N) = ⟨i, hi⟩ := by
    ext
    rfl
  have heq :
      d.depthVec d.N le_rfl ⟨i, hi⟩ = d.depthVec (i + 1) hm (Fin.last i) := by
    calc
      d.depthVec d.N le_rfl ⟨i, hi⟩
          = d.depthVec d.N le_rfl (Fin.castLE hm (Fin.last i)) := by
              simp [hcast]
      _ = d.depthVec (i + 1) hm (Fin.last i) := by
          simpa using
            (d.depthVec_castLE (m := i + 1) (hm := hm) d.N le_rfl hm (Fin.last i))
  -- Unfold one step of `depthVec` at length `i+1`. The `node` proof is propositionally irrelevant.
  have hi0 : i < d.N := lt_of_lt_of_le (Nat.lt_succ_self i) hm
  have hi0_eq : hi0 = hi := Subsingleton.elim _ _
  cases hi0_eq
  cases hnd : d.node i hi with
  | input j =>
      simpa [depthAt, depthVec, hnd] using heq
  | const b =>
      simpa [depthAt, depthVec, hnd] using heq
  | gate g f =>
      have hchild :
          (j : Fin _) →
            d.depthVec i (le_trans (Nat.le_succ i) hm) (f j) =
              d.depthAt (f j).1 (lt_trans (f j).2 hi) := by
        intro j
        have hm0 : i ≤ d.N := le_trans (Nat.le_succ i) hm
        have hcast0 :
            (Fin.castLE hm0 (f j) : Fin d.N) = ⟨(f j).1, lt_trans (f j).2 hi⟩ := by
          ext
          rfl
        have :=
          d.depthVec_castLE (m := i) (hm := hm0) d.N le_rfl hm0 (f j)
        simpa [depthAt, hcast0] using this.symm
      simpa [depthAt, depthVec, hnd, hchild] using heq

/-- Depth is stable under prefix extension. -/
theorem depthAt_eq_of_prefix {d₀ d₁ : DAG G n} (h : Prefix (G := G) (n := n) d₀ d₁)
    (i : Nat) (hi : i < d₀.N) :
    d₁.depthAt i (lt_of_lt_of_le hi h.le) = d₀.depthAt i hi := by
  classical
  revert hi
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  have hi1 : i < d₁.N := lt_of_lt_of_le hi h.le
  have hnode : d₁.node i hi1 = d₀.node i hi := by
    simpa using h.node_eq i hi
  -- Unfold `depthAt` on both sides and use the induction hypothesis for children.
  cases hnd : d₀.node i hi with
  | input j =>
      -- `d₀.node i hi = input j`
      -- and `d₁.node i hi1 = input j` by prefix agreement.
      rw [depthAt_eq_node (d := d₀) (hi := hi)]
      rw [depthAt_eq_node (d := d₁) (hi := hi1)]
      simp [hnode, hnd]
  | const b =>
      rw [depthAt_eq_node (d := d₀) (hi := hi)]
      rw [depthAt_eq_node (d := d₁) (hi := hi1)]
      simp [hnode, hnd]
  | gate g f =>
      rw [depthAt_eq_node (d := d₀) (hi := hi)]
      rw [depthAt_eq_node (d := d₁) (hi := hi1)]
      have hchild :
          ∀ j : Fin _,
            d₁.depthAt (f j).1 (lt_trans (f j).2 hi1) = d₀.depthAt (f j).1 (lt_trans (f j).2 hi) :=
        by
          intro j
          exact ih (f j).1 (f j).2 (lt_trans (f j).2 hi)
      have hsup :
          (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ =>
                d₁.depthAt (f j).1 (lt_trans (f j).2 hi1)) =
            (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ =>
                d₀.depthAt (f j).1 (lt_trans (f j).2 hi)) := by
        -- rewrite pointwise under the `sup`
        refine Finset.sup_congr rfl ?_
        intro j hj
        exact hchild j
      simp [hnode, hnd, hsup, -depthAt_def]

theorem depthAt_snoc_of_lt (d : DAG G n) (nd : DAGNode G n d.N) (i : Nat) (hi : i < d.N) :
    (d.snoc nd).depthAt i (lt_trans hi (Nat.lt_succ_self _)) = d.depthAt i hi := by
  simpa using
    (depthAt_eq_of_prefix (d₀ := d) (d₁ := d.snoc nd) (h := Prefix.snoc (d := d) (nd := nd))
      (i := i) (hi := hi))

theorem depthAt_snoc_last (d : DAG G n) (nd : DAGNode G n d.N) :
    (d.snoc nd).depthAt d.N (Nat.lt_succ_self _) =
      match nd with
      | .input _ => 0
      | .const _ => 0
      | .gate (k := k) _ f =>
          (Finset.sup (Finset.univ : Finset (Fin k)) fun j : Fin k => d.depthAt (f j).1 (f j).2) +
            1 := by
  classical
  have hnode : (d.snoc nd).node d.N (Nat.lt_succ_self _) = nd := by
    simp [snoc_node_last]
  rw [depthAt_eq_node (d := d.snoc nd) (hi := Nat.lt_succ_self _)]
  -- reduce using `snoc_node_last` and transport earlier depths back to `d`
  cases nd with
  | input i =>
      simp [hnode]
  | const b =>
      simp [hnode]
  | gate g f =>
      -- For each child, the node is in the prefix `d`, so depth is unchanged by snoc.
      have hchild :
          (j : Fin _) →
            (d.snoc (DAGNode.gate g f)).depthAt (f j).1 (lt_trans (f j).2 (Nat.lt_succ_self _)) =
              d.depthAt (f j).1 (f j).2 := by
        intro j
        simpa using
          (depthAt_snoc_of_lt (d := d) (nd := DAGNode.gate g f) (i := (f j).1) (hi := (f j).2))
      have hsup :
          (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ =>
                (d.snoc (DAGNode.gate g f)).depthAt (f j).1
                  (lt_trans (f j).2 (Nat.lt_succ_self _))) =
            (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ =>
                d.depthAt (f j).1 (f j).2) := by
        refine Finset.sup_congr rfl ?_
        intro j hj
        exact hchild j
      simp [hnode, hsup, -depthAt_def]

end DAG

namespace DAGCircuit

/-- The depth of a DAG circuit is the depth of its designated output node. -/
def depth (c : DAGCircuit G n) : Nat :=
  c.toDAG.depthAt c.out.1 c.out.2

@[simp] theorem depth_def (c : DAGCircuit G n) :
    c.depth = c.toDAG.depthAt c.out.1 c.out.2 :=
  rfl

end DAGCircuit

end Circuit

end Computability
