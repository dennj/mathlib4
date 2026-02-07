/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Formula.Basic
public import Mathlib.Computability.Formula.Complexity
public import Mathlib.Computability.Circuit.Basic
public import Mathlib.Computability.Circuit.Complexity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Formulas to circuits

This file provides a translation from tree formulas (`Formula G n`) to topologically indexed DAG
circuits (`Circuit G n`), together with evaluation correctness.

The translation is intentionally simple: it flattens the tree into a DAG by allocating a fresh node
for every subcircuit (so it does **not** attempt to identify common subcircuits). This is enough to
connect the formula syntax to the circuit representation and can later be refined by adding sharing.
-/

@[expose] public section

namespace Computability

open Gate

namespace Formula

open CircuitDAG

open scoped BigOperators

variable {G : Nat → Type} {n : Nat}

namespace ToCircuit

/-- Result of building a formula into a DAG starting from an existing prefix DAG `d`. -/
structure BuildResult (d : CircuitDAG G n) where
  dag : CircuitDAG G n
  pref : CircuitDAG.Prefix d dag
  out : Fin dag.N

/-- Result of building the children of a gate into a DAG
starting from an existing prefix DAG `d`. -/
structure ChildrenResult (d : CircuitDAG G n) (k : Nat) where
  dag : CircuitDAG G n
  pref : CircuitDAG.Prefix d dag
  out : Fin k → Fin dag.N

namespace BuildResult

theorem le {d : CircuitDAG G n} (r : BuildResult (G := G) (n := n) d) : d.N ≤ r.dag.N :=
  r.pref.le

end BuildResult

/-- Build `k` children sequentially, threading a DAG through the computations. -/
def buildChildren :
    ∀ {k : Nat},
      (Fin k → ∀ d : CircuitDAG G n, BuildResult (G := G) (n := n) d) →
        ∀ d : CircuitDAG G n, ChildrenResult (G := G) (n := n) d k
  | 0, _, d =>
      ⟨d, CircuitDAG.Prefix.refl d, Fin.elim0⟩
  | k + 1, childBuild, d =>
      let r0 := childBuild 0 d
      let rt := buildChildren (k := k) (fun i => childBuild i.succ) r0.dag
      let out0 : Fin rt.dag.N := Fin.castLE rt.pref.le r0.out
      ⟨rt.dag, CircuitDAG.Prefix.trans r0.pref rt.pref, Fin.cons out0 rt.out⟩

/-- Build a tree formula into a DAG, allocating a fresh node for each subcircuit. -/
def buildFrom (c : Formula G n) : ∀ d : CircuitDAG G n, BuildResult (G := G) (n := n) d :=
  fun d =>
    match c with
    | .input i =>
        let dag := d.snoc (.input i)
        ⟨dag, CircuitDAG.Prefix.snoc (d := d) (nd := .input i), Fin.last d.N⟩
    | .const b =>
        let dag := d.snoc (.const b)
        ⟨dag, CircuitDAG.Prefix.snoc (d := d) (nd := .const b), Fin.last d.N⟩
    | .gate (k := k) g f =>
        let ch := buildChildren (G := G) (n := n) (k := k) (fun i => buildFrom (f i)) d
        let dagKids := ch.dag
        let nd : CircuitNode G n dagKids.N := .gate g ch.out
        let dag := dagKids.snoc nd
        let p := CircuitDAG.Prefix.trans ch.pref (CircuitDAG.Prefix.snoc (d := dagKids) (nd := nd))
        ⟨dag, p, Fin.last dagKids.N⟩

lemma buildFrom_input (i : Fin n) (d : CircuitDAG G n) :
    buildFrom (G := G) (n := n) (Formula.input i) d =
      ⟨d.snoc (.input i), CircuitDAG.Prefix.snoc (d := d) (nd := .input i), Fin.last d.N⟩ :=
  rfl

lemma buildFrom_const (b : Bool) (d : CircuitDAG G n) :
    buildFrom (G := G) (n := n) (Formula.const (G := G) (n := n) b) d =
      ⟨d.snoc (.const b), CircuitDAG.Prefix.snoc (d := d) (nd := .const b), Fin.last d.N⟩ :=
  rfl

lemma buildFrom_gate {k : Nat} (g : G k) (f : Fin k → Formula G n) (d : CircuitDAG G n) :
    buildFrom (G := G) (n := n) (Formula.gate (G := G) (n := n) (k := k) g f) d =
      let ch :=
        buildChildren (G := G) (n := n) (k := k) (fun i => buildFrom (G := G) (n := n) (f i)) d
      let dagKids := ch.dag
      let nd : CircuitNode G n dagKids.N := .gate g ch.out
      let dag := dagKids.snoc nd
      let p := CircuitDAG.Prefix.trans ch.pref (CircuitDAG.Prefix.snoc (d := dagKids) (nd := nd))
      ⟨dag, p, Fin.last dagKids.N⟩ :=
  rfl

/-- Convenience wrapper: build a formula from a given prefix DAG. -/
def build (d : CircuitDAG G n) (c : Formula G n) : BuildResult (G := G) (n := n) d :=
  buildFrom (G := G) (n := n) c d

section Correctness

variable [GateEval G]

theorem buildChildren_correct {k : Nat}
    (childBuild : Fin k → ∀ d : CircuitDAG G n, BuildResult (G := G) (n := n) d)
    (val : Fin k → (Fin n → Bool) → Bool)
    (hval : ∀ i d x, let r := childBuild i d; r.dag.evalAt x r.out.1 r.out.2 = val i x) :
    ∀ d x i,
      let ch := buildChildren (G := G) (n := n) (k := k) childBuild d
      ch.dag.evalAt x (ch.out i).1 (ch.out i).2 = val i x := by
  induction k with
  | zero =>
      intro d x i
      cases i with
      | mk v hv => cases Nat.not_lt_zero v hv
  | succ k hk =>
      intro d x i
      set r0 := childBuild 0 d
      set rt := buildChildren (G := G) (n := n) (k := k) (fun j => childBuild j.succ) r0.dag
      -- unfold `buildChildren` and split on `i = 0` vs `i = succ j`
      cases i using Fin.cases with
      | zero =>
          have hpres :
              rt.dag.evalAt x r0.out.1 (lt_of_lt_of_le r0.out.2 rt.pref.le) =
                r0.dag.evalAt x r0.out.1 r0.out.2 := by
            simpa using
              (CircuitDAG.evalAt_eq_of_prefix (d₀ := r0.dag) (d₁ := rt.dag) (h := rt.pref) (x := x)
                (i := r0.out.1) (hi := r0.out.2))
          -- `buildChildren` returns `Fin.cons` for the output map
          simpa [buildChildren, r0, rt] using hpres.trans (hval 0 d x)
      | succ j =>
          have ht :=
            hk
              (childBuild := fun t => childBuild t.succ)
              (val := fun t => val t.succ)
              (hval := fun t d x => hval t.succ d x)
              (d := r0.dag) (x := x) (i := j)
          simpa [buildChildren, r0, rt] using ht

theorem build_correct (c : Formula G n) :
    ∀ d x,
      let r := build (G := G) (n := n) d c
      r.dag.evalAt x r.out.1 r.out.2 = eval c x := by
  intro d x
  revert d x
  induction c with
  | input i =>
      intro d x
      simp [build, buildFrom_input, CircuitDAG.evalAt_snoc_last]
  | const b =>
      intro d x
      simp [build, buildFrom_const, CircuitDAG.evalAt_snoc_last]
  | gate g f ih =>
      intro d x
      -- build children, then add the gate node
      set ch :=
        buildChildren (G := G) (n := n) (k := _) (fun i => buildFrom (G := G) (n := n) (f i)) d
      have hchildren :
          ∀ j, ch.dag.evalAt x (ch.out j).1 (ch.out j).2 = eval (f j) x := by
        intro j
        have :=
          buildChildren_correct (G := G) (n := n)
            (k := _)
            (childBuild := fun i => buildFrom (G := G) (n := n) (f i))
            (val := fun i x => eval (f i) x)
            (hval := fun i d x => by simpa [build] using ih i d x)
            d x j
        simpa [ch] using this
      -- the new last node evaluates to the gate semantics applied to child values
      simp [build, buildFrom_gate, ch, CircuitDAG.evalAt_snoc_last, hchildren]

end Correctness

end ToCircuit

namespace ToCircuit

/-! ## Size and depth preservation -/

theorem buildChildren_N {k : Nat}
    (childBuild : Fin k → ∀ d : CircuitDAG G n, BuildResult (G := G) (n := n) d)
    (inc : Fin k → Nat)
    (hinc : ∀ i d, let r := childBuild i d; r.dag.N = d.N + inc i) :
    ∀ d : CircuitDAG G n,
      let ch := buildChildren (G := G) (n := n) (k := k) childBuild d
      ch.dag.N = d.N + ∑ i : Fin k, inc i := by
  classical
  induction k with
  | zero =>
      intro d
      simp [buildChildren]
  | succ k ih =>
      intro d
      set r0 := childBuild 0 d
      set rt :=
        buildChildren (G := G) (n := n) (k := k) (fun i => childBuild i.succ) r0.dag
      have hr0 : r0.dag.N = d.N + inc 0 := by
        simpa [r0] using (hinc 0 d)
      have hrt :
          rt.dag.N = r0.dag.N + ∑ i : Fin k, inc i.succ := by
        have hinc' :
            ∀ (i : Fin k) d,
              let r := (fun i => childBuild i.succ) i d
              r.dag.N = d.N + (fun i => inc i.succ) i := by
          intro i d
          simpa using (hinc i.succ d)
        simpa [rt] using
          (ih (childBuild := fun i => childBuild i.succ) (inc := fun i => inc i.succ) hinc' r0.dag)
      -- `buildChildren` returns `rt.dag` as the final DAG.
      -- Split the sum over `Fin (k+1)` into head + tail.
      have hsum : inc 0 + ∑ i : Fin k, inc i.succ = ∑ i : Fin (k + 1), inc i := by
        simpa using (Fin.sum_univ_succ (f := inc) (n := k)).symm
      -- Note: `buildChildren` returns `rt.dag` as the final DAG.
      simp [buildChildren, r0, rt, hrt, hr0, hsum, Nat.add_assoc]

theorem buildFrom_N (c : Formula G n) :
    ∀ d : CircuitDAG G n, let r := buildFrom (G := G) (n := n) c d; r.dag.N = d.N + size c := by
  classical
  induction c with
  | input i =>
      intro d
      simp [buildFrom_input, size, CircuitDAG.snoc_N]
  | const b =>
      intro d
      simp [buildFrom_const, size, CircuitDAG.snoc_N]
  | gate g f ih =>
      intro d
      set ch :=
        buildChildren (G := G) (n := n) (k := _) (fun i => buildFrom (G := G) (n := n) (f i)) d
      have hch :
          ch.dag.N = d.N + ∑ i : Fin _, size (f i) := by
        -- `buildFrom` adds exactly `size` nodes for each child.
        have hinc :
            ∀ i d,
              let r := buildFrom (G := G) (n := n) (f i) d
              r.dag.N = d.N + size (f i) := by
          intro i d
          simpa using ih i d
        simpa [ch] using
          (buildChildren_N (G := G) (n := n) (k := _)
              (childBuild := fun i => buildFrom (G := G) (n := n) (f i))
              (inc := fun i => size (f i)) hinc d)
      -- After building all children, we append one more gate node.
      simp [buildFrom_gate, ch, size, CircuitDAG.snoc_N, hch, Nat.add_left_comm, Nat.add_comm]

theorem buildChildren_depthAt {k : Nat}
    (childBuild : Fin k → ∀ d : CircuitDAG G n, BuildResult (G := G) (n := n) d)
    (val : Fin k → Nat)
    (hval : ∀ i d, let r := childBuild i d; r.dag.depthAt r.out.1 r.out.2 = val i) :
    ∀ d i,
      let ch := buildChildren (G := G) (n := n) (k := k) childBuild d
      ch.dag.depthAt (ch.out i).1 (ch.out i).2 = val i := by
  classical
  induction k with
  | zero =>
      intro d i
      cases i with
      | mk v hv => cases Nat.not_lt_zero v hv
  | succ k hk =>
      intro d i
      set r0 := childBuild 0 d
      set rt := buildChildren (G := G) (n := n) (k := k) (fun j => childBuild j.succ) r0.dag
      cases i using Fin.cases with
      | zero =>
          have hpres :
              rt.dag.depthAt r0.out.1 (lt_of_lt_of_le r0.out.2 rt.pref.le) =
                r0.dag.depthAt r0.out.1 r0.out.2 := by
            simpa using
              (CircuitDAG.depthAt_eq_of_prefix (d₀ := r0.dag) (d₁ := rt.dag) (h := rt.pref)
                (i := r0.out.1) (hi := r0.out.2))
          simpa [buildChildren, r0, rt] using hpres.trans (hval 0 d)
      | succ j =>
          have ht :=
            hk
              (childBuild := fun t => childBuild t.succ)
              (val := fun t => val t.succ)
              (hval := fun t d => hval t.succ d)
              (d := r0.dag) (i := j)
          simpa [buildChildren, r0, rt] using ht

theorem buildFrom_depthAt (c : Formula G n) :
    ∀ d : CircuitDAG G n,
      let r := buildFrom (G := G) (n := n) c d
      r.dag.depthAt r.out.1 r.out.2 = depth c := by
  classical
  induction c with
  | input i =>
      intro d
      simpa [buildFrom_input, depth] using
        CircuitDAG.depthAt_snoc_last (d := d) (nd := CircuitNode.input i)
  | const b =>
      intro d
      simpa [buildFrom_const, depth] using
        CircuitDAG.depthAt_snoc_last (d := d) (nd := CircuitNode.const b)
  | gate g f ih =>
      intro d
      set ch :=
        buildChildren (G := G) (n := n) (k := _) (fun i => buildFrom (G := G) (n := n) (f i)) d
      have hchildren :
          ∀ j : Fin _, ch.dag.depthAt (ch.out j).1 (ch.out j).2 = depth (f j) := by
        intro j
        have :=
          buildChildren_depthAt (G := G) (n := n) (k := _)
            (childBuild := fun i => buildFrom (G := G) (n := n) (f i))
            (val := fun i => depth (f i))
            (hval := fun i d => by simpa using ih i d)
            d j
        simpa [ch] using this
      -- The output node is the last appended gate node.
      have hsup :
          (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ =>
                ch.dag.depthAt (ch.out j).1 (ch.out j).2) =
            (Finset.sup (Finset.univ : Finset (Fin _)) fun j : Fin _ => depth (f j)) := by
        refine Finset.sup_congr rfl ?_
        intro j hj
        exact hchildren j
      -- Unfold `buildFrom` and reduce via `depthAt_snoc_last`.
      simp [buildFrom_gate, ch, depth, CircuitDAG.depthAt_snoc_last, hsup, -CircuitDAG.depthAt_def]

theorem build_N (d : CircuitDAG G n) (c : Formula G n) :
    let r := build (G := G) (n := n) d c
    r.dag.N = d.N + size c := by
  simpa [build] using (buildFrom_N (G := G) (n := n) (c := c) d)

theorem build_depthAt (d : CircuitDAG G n) (c : Formula G n) :
    let r := build (G := G) (n := n) d c
    r.dag.depthAt r.out.1 r.out.2 = depth c := by
  simpa [build] using (buildFrom_depthAt (G := G) (n := n) (c := c) d)

end ToCircuit

/-- Translate a tree formula to a DAG circuit. -/
def toCircuit (c : Formula G n) : Circuit G n :=
  let r := ToCircuit.build (G := G) (n := n) (d := CircuitDAG.empty G n) c
  { N := r.dag.N
    node := r.dag.node
    out := r.out }

theorem eval_toCircuit [GateEval G] (c : Formula G n) (x : Fin n → Bool) :
    (toCircuit (G := G) (n := n) c).eval x = eval c x := by
  -- unfold `toCircuit` and apply `build_correct` from the empty prefix
  simp [toCircuit, Circuit.eval,
    ToCircuit.build_correct (G := G) (n := n) (c := c) (d := CircuitDAG.empty G n)]

theorem size_toCircuit (c : Formula G n) : (toCircuit (G := G) (n := n) c).size = size c := by
  -- `toCircuit` allocates exactly one node per syntax-tree node.
  have h := ToCircuit.build_N (G := G) (n := n) (d := CircuitDAG.empty G n) (c := c)
  simpa [toCircuit, Circuit.size, CircuitDAG.empty] using h

theorem depth_toCircuit (c : Formula G n) :
    Circuit.depth (toCircuit (G := G) (n := n) c) = depth c := by
  have h := ToCircuit.build_depthAt (G := G) (n := n) (d := CircuitDAG.empty G n) (c := c)
  simpa [toCircuit, Circuit.depth] using h

end Formula

end Computability
