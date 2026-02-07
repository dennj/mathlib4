/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Gate
public import Mathlib.Computability.Formula.Encoding
public import Mathlib.Computability.Circuit.Basic

/-!
# Sharing compilation (formulas to circuits)

This file defines a sharing-aware compilation from tree formulas to circuits (DAGs).

Unlike `toCircuit` (which allocates a fresh node for every subcircuit), `toCircuitShare` memoizes
compiled subcircuits keyed by their `Encodable.encode` value, so repeated subcircuits are compiled
once and reused.

The compiler is defined by structural recursion on `Formula` (so it is computable), while the
correctness proof packages additional invariants about the memo table.
-/

@[expose] public section

namespace Computability

open Gate

namespace Formula

variable {G : Nat → Type} {n : Nat}

namespace Share

section

variable [∀ k, Encodable (G k)]

/-- A memo table for already compiled subcircuits.

For a DAG with `N` nodes, the table stores pairs of a formula (with `n` inputs) and the node index
computing it. Indices are always typed as `Fin N`, so they can be safely reused. -/
abbrev Cache (G : Nat → Type) (n : Nat) (N : Nat) : Type :=
  List (Formula G n × Fin N)

namespace Cache

variable {N : Nat}

/-- Lift a cache along `N ↦ N+1`. -/
def liftSucc (c : Cache G n N) : Cache G n (N + 1) :=
  c.map fun p => (p.1, Fin.castSucc p.2)

/-- Find a cached entry whose formula encodes to `key`.

We return membership evidence so the caller can use invariants about the cache. -/
def find? (c : Cache G n N) (key : Nat) :
    Option (Σ' c' : Formula G n, Σ' i : Fin N, (c', i) ∈ c ∧ Encodable.encode c' = key) :=
  match c with
  | [] => none
  | (c', i) :: cs =>
      if h : Encodable.encode c' = key then
        some ⟨c', i, ⟨by simp, h⟩⟩
      else
        (find? cs key).map fun ⟨c'', j, hj⟩ =>
          ⟨c'', j, ⟨List.mem_cons_of_mem _ hj.1, hj.2⟩⟩

end Cache

/-- Compiler state: a DAG prefix together with a cache of already compiled subcircuits. -/
structure State (G : Nat → Type) (n : Nat) : Type where
  dag : CircuitDAG G n
  cache : Cache G n dag.N

namespace State

/-- The initial state: the empty DAG and an empty cache. -/
def empty (G : Nat → Type) (n : Nat) : State G n :=
  ⟨CircuitDAG.empty G n, []⟩

instance : Inhabited (State G n) :=
  ⟨empty G n⟩

/-- Append a node, lifting the cache and inserting the new formula result. -/
def snoc (s : State G n) (nd : CircuitNode G n s.dag.N) (c : Formula G n) : State G n :=
  let dag' := s.dag.snoc nd
  let cache' : Cache G n dag'.N := (c, Fin.last s.dag.N) :: Cache.liftSucc s.cache
  ⟨dag', cache'⟩

omit [∀ k, Encodable (G k)] in
@[simp] theorem snoc_dag (s : State G n) (nd : CircuitNode G n s.dag.N) (c : Formula G n) :
    (snoc (G := G) (n := n) s nd c).dag = s.dag.snoc nd :=
  rfl

end State

section Correctness

variable [GateEval G]

/-- Cache correctness: every cached pair `(c, i)` evaluates like `c`. -/
def StateOk (s : State G n) : Prop :=
  ∀ {c : Formula G n} {i : Fin s.dag.N}, (c, i) ∈ s.cache → ∀ x, s.dag.evalAt x i.1 i.2 = eval c x

omit [∀ k, Encodable (G k)] in theorem stateOk_empty :
    StateOk (G := G) (n := n) (State.empty G n) := by
  intro c i hi
  cases hi

omit [∀ k, Encodable (G k)] in
/-- Update `StateOk` after appending a node and caching its result. -/
theorem stateOk_snoc (s : State G n) (hs : StateOk (G := G) (n := n) s)
    (nd : CircuitNode G n s.dag.N) (c : Formula G n)
    (hout : ∀ x,
      (s.dag.snoc nd).evalAt x s.dag.N (Nat.lt_succ_self _) = eval c x) :
    StateOk (G := G) (n := n) (State.snoc (G := G) (n := n) s nd c) := by
  intro c' i hi x
  -- Split into the newly inserted head entry or an entry from the lifted tail cache.
  rcases List.mem_cons.1 hi with h | hi_tail
  · cases h
    simpa [State.snoc, State.snoc_dag] using hout x
  · rcases List.mem_map.1 hi_tail with ⟨⟨c0, i0⟩, hi0, hEq⟩
    cases hEq
    have hpres :
        (s.dag.snoc nd).evalAt x i0.1 (lt_trans i0.2 (Nat.lt_succ_self _)) =
          s.dag.evalAt x i0.1 i0.2 := by
      simpa [State.snoc_dag] using
        CircuitDAG.evalAt_snoc_of_lt (d := s.dag) (nd := nd) (x := x) (i := i0.1) (hi := i0.2)
    have hold := hs (c := c0) (i := i0) hi0 x
    simpa [State.snoc, Cache.liftSucc, State.snoc_dag] using hpres.trans hold

/-- Result of compiling `c` starting from a state `s`. -/
structure BuildResult (c : Formula G n) (s : State G n) : Type where
  state : State G n
  pref : CircuitDAG.Prefix s.dag state.dag
  out : Fin state.dag.N
  ok : StateOk (G := G) (n := n) state
  out_correct : ∀ x, state.dag.evalAt x out.1 out.2 = eval c x

/-- Result of compiling children `f : Fin k → Formula G n` in order, starting from `s`. -/
structure ChildrenResult {k : Nat} (f : Fin k → Formula G n) (s : State G n) : Type where
  state : State G n
  pref : CircuitDAG.Prefix s.dag state.dag
  out : Fin k → Fin state.dag.N
  ok : StateOk (G := G) (n := n) state
  out_correct : ∀ i x, state.dag.evalAt x (out i).1 (out i).2 = eval (f i) x

/-- Compile children sequentially, threading the state. -/
def buildChildren :
    ∀ {k : Nat} (f : Fin k → Formula G n)
      (_childBuild :
        ∀ i : Fin k,
          ∀ s : State G n,
            StateOk (G := G) (n := n) s →
              BuildResult (G := G) (n := n) (f i) s),
      ∀ s : State G n,
        StateOk (G := G) (n := n) s →
          ChildrenResult (G := G) (n := n) f s
  | 0, _, _, s, hs =>
      ⟨s, CircuitDAG.Prefix.refl s.dag, Fin.elim0, hs, by intro i x; exact Fin.elim0 i⟩
  | k + 1, f, childBuild, s, hs =>
      let r0 := childBuild 0 s hs
      let rt :=
        buildChildren (k := k) (f := fun i => f i.succ)
          (_childBuild := fun i s hs => childBuild i.succ s hs) r0.state r0.ok
      let out0 : Fin rt.state.dag.N := Fin.castLE rt.pref.le r0.out
      let outAll : Fin (k + 1) → Fin rt.state.dag.N := Fin.cons out0 rt.out
      have pref : CircuitDAG.Prefix s.dag rt.state.dag := CircuitDAG.Prefix.trans r0.pref rt.pref
      have ok : StateOk (G := G) (n := n) rt.state := rt.ok
      have out_correct : ∀ i x,
          rt.state.dag.evalAt x (outAll i).1 (outAll i).2 = eval (f i) x := by
        intro i x
        cases i using Fin.cases with
        | zero =>
            have hpres :
                rt.state.dag.evalAt x r0.out.1 (lt_of_lt_of_le r0.out.2 rt.pref.le) =
                  r0.state.dag.evalAt x r0.out.1 r0.out.2 := by
              simpa using
                (CircuitDAG.evalAt_eq_of_prefix
                  (d₀ := r0.state.dag) (d₁ := rt.state.dag) (h := rt.pref)
                  (x := x) (i := r0.out.1) (hi := r0.out.2))
            simpa [outAll, out0, Fin.cons] using hpres.trans (r0.out_correct x)
        | succ j =>
            simpa [outAll, Fin.cons] using rt.out_correct j x
      ⟨rt.state, pref, outAll, ok, out_correct⟩

/-- Sharing-aware compilation of a formula into a DAG, starting from a state. -/
def buildFrom (c : Formula G n) :
    ∀ s : State G n, StateOk (G := G) (n := n) s → BuildResult (G := G) (n := n) c s :=
  fun s hs =>
    match c with
    | .input i =>
        let key := Encodable.encode (Formula.input (G := G) i)
        match Cache.find? s.cache key with
        | some ⟨c', idx, h⟩ => by
            have hmem : (c', idx) ∈ s.cache := h.1
            have henc : Encodable.encode c' = key := h.2
            have hc : c' = Formula.input (G := G) i := by
              exact Encodable.encode_injective (by simpa [key] using henc)
            refine ⟨s, CircuitDAG.Prefix.refl s.dag, idx, hs, ?_⟩
            intro x
            simpa [hc] using hs (c := c') (i := idx) hmem x
        | none => by
            let s' := State.snoc (G := G) (n := n) s (.input i) (Formula.input (G := G) i)
            have pref : CircuitDAG.Prefix s.dag s'.dag :=
              CircuitDAG.Prefix.snoc (d := s.dag) (nd := .input i)
            have hout :
                ∀ x,
                  s'.dag.evalAt x s.dag.N (Nat.lt_succ_self _) =
                    eval (Formula.input (G := G) i) x := by
              intro x
              simp [s', State.snoc, CircuitDAG.evalAt_snoc_last, eval]
            have ok : StateOk (G := G) (n := n) s' :=
              stateOk_snoc (G := G) (n := n) s hs (.input i) (Formula.input (G := G) i) hout
            refine ⟨s', pref, Fin.last s.dag.N, ok, ?_⟩
            intro x
            simpa using hout x
    | .const b =>
        let key := Encodable.encode (Formula.const (G := G) (n := n) b)
        match Cache.find? s.cache key with
        | some ⟨c', idx, h⟩ => by
            have hmem : (c', idx) ∈ s.cache := h.1
            have henc : Encodable.encode c' = key := h.2
            have hc : c' = Formula.const (G := G) (n := n) b := by
              exact Encodable.encode_injective (by simpa [key] using henc)
            refine ⟨s, CircuitDAG.Prefix.refl s.dag, idx, hs, ?_⟩
            intro x
            simpa [hc] using hs (c := c') (i := idx) hmem x
        | none => by
            let s' :=
              State.snoc (G := G) (n := n) s (.const b) (Formula.const (G := G) (n := n) b)
            have pref : CircuitDAG.Prefix s.dag s'.dag :=
              CircuitDAG.Prefix.snoc (d := s.dag) (nd := .const b)
            have hout :
                ∀ x,
                  s'.dag.evalAt x s.dag.N (Nat.lt_succ_self _) =
                    eval (Formula.const (G := G) (n := n) b) x := by
              intro x
              simp [s', State.snoc, CircuitDAG.evalAt_snoc_last, eval]
            have ok : StateOk (G := G) (n := n) s' :=
              stateOk_snoc (G := G) (n := n) s hs (.const b) (Formula.const (G := G) (n := n) b)
                hout
            refine ⟨s', pref, Fin.last s.dag.N, ok, ?_⟩
            intro x
            simpa using hout x
    | .gate (k := k) g f =>
        let key := Encodable.encode (Formula.gate (G := G) (n := n) (k := k) g f)
        match Cache.find? s.cache key with
        | some ⟨c', idx, h⟩ => by
            have hmem : (c', idx) ∈ s.cache := h.1
            have henc : Encodable.encode c' = key := h.2
            have hc : c' = Formula.gate (G := G) (n := n) (k := k) g f := by
              exact Encodable.encode_injective (by simpa [key] using henc)
            refine ⟨s, CircuitDAG.Prefix.refl s.dag, idx, hs, ?_⟩
            intro x
            simpa [hc] using hs (c := c') (i := idx) hmem x
        | none => by
            let ch :=
              buildChildren (G := G) (n := n) (k := k) (f := f)
                (_childBuild := fun i s hs => buildFrom (c := f i) s hs) s hs
            let dagKids := ch.state.dag
            let nd : CircuitNode G n dagKids.N := .gate g ch.out
            let s' :=
              State.snoc (G := G) (n := n) ch.state nd
                (Formula.gate (G := G) (n := n) (k := k) g f)
            have prefKids : CircuitDAG.Prefix s.dag dagKids := ch.pref
            have pref : CircuitDAG.Prefix s.dag s'.dag :=
              CircuitDAG.Prefix.trans prefKids (CircuitDAG.Prefix.snoc (d := dagKids) (nd := nd))
            have hchildren : ∀ i x, dagKids.evalAt x (ch.out i).1 (ch.out i).2 = eval (f i) x := by
              intro i x
              simpa using ch.out_correct i x
            have hout :
                ∀ x,
                  s'.dag.evalAt x dagKids.N (Nat.lt_succ_self _) =
                    eval (Formula.gate (G := G) (n := n) (k := k) g f) x := by
              intro x
              -- Use the semantic description of the newly appended node.
              simp [s', State.snoc, dagKids, nd, CircuitDAG.evalAt_snoc_last, eval, hchildren]
            have ok : StateOk (G := G) (n := n) s' :=
              stateOk_snoc (G := G) (n := n) ch.state ch.ok nd
                (Formula.gate (G := G) (n := n) (k := k) g f) hout
            refine ⟨s', pref, Fin.last dagKids.N, ok, ?_⟩
            intro x
            simpa using hout x

end Correctness

section

variable [GateEval G]

/-- Sharing-aware compilation from tree formulas to circuits. -/
def toCircuitShare (c : Formula G n) : Circuit G n :=
  let s0 : State G n := State.empty G n
  let r := buildFrom (G := G) (n := n) c s0 stateOk_empty
  { N := r.state.dag.N
    node := r.state.dag.node
    out := r.out }

theorem eval_toCircuitShare (c : Formula G n) (x : Fin n → Bool) :
    (toCircuitShare (G := G) (n := n) c).eval x = eval c x := by
  let s0 : State G n := State.empty G n
  let r := buildFrom (G := G) (n := n) c s0 stateOk_empty
  simpa [toCircuitShare, Circuit.eval, s0, r] using r.out_correct x

end

end

end Share

open Share

section

variable [∀ k, Encodable (G k)] [GateEval G]

/-- Sharing-aware compilation from tree formulas to circuits. -/
def toCircuitShare (c : Formula G n) : Circuit G n :=
  Share.toCircuitShare (G := G) (n := n) c

theorem eval_toCircuitShare (c : Formula G n) (x : Fin n → Bool) :
    (toCircuitShare (G := G) (n := n) c).eval x = eval c x :=
  Share.eval_toCircuitShare (G := G) (n := n) c x

end

end Formula

end Computability
