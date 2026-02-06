/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Circuit.CNFGate
public import Mathlib.Computability.Circuit.Gate
import Mathlib.Data.List.OfFn

/-!
# Polynomial-size CNF templates for threshold / majority gates

This file defines a sequential-counter style CNF encoding of the relation

`out = decide (t ≤ countTrue inputs)`,

using auxiliary variables. The encoding avoids the truth-table blowup for unbounded fan-in gates.

This file also provides a small, tactic-free correctness API: soundness (any satisfying assignment
enforces the threshold relation on base variables) and completeness (given any base assignment with
the correct output value, there is a canonical auxiliary assignment satisfying the CNF).
-/

@[expose] public section

namespace Computability

namespace Circuit

namespace CNFEnc

open CNF

variable {V : Type}

/-! ## Variables -/

inductive ThrAux (k t : Nat) : Type where
  /-- DP table entry `s i j`: among the first `i` inputs, at least `j` are `true`. -/
  | s : Fin (k + 1) → Fin (t + 1) → ThrAux k t
  /-- Conjunction helper `a i j = x[i] ∧ s[i][j]`. -/
  | a : Fin k → Fin t → ThrAux k t

abbrev ThrVar (V : Type) (k t : Nat) : Type :=
  Sum V (ThrAux k t)

def inVar {k t : Nat} (v : V) : ThrVar V k t :=
  Sum.inl v

def sVar {k t : Nat} (i : Fin (k + 1)) (j : Fin (t + 1)) : ThrVar V k t :=
  Sum.inr (.s i j)

def aVar {k t : Nat} (i : Fin k) (j : Fin t) : ThrVar V k t :=
  Sum.inr (.a i j)

/-! ## Clauses -/

section Clauses

variable {k t : Nat}

def thrBaseJ0 : CNF.Formula (ThrVar V k t) :=
  List.flatten <|
    List.ofFn fun i : Fin (k + 1) =>
      constClauses (V := ThrVar V k t) (sVar (V := V) (k := k) (t := t) i 0) true

def thrBaseI0 : CNF.Formula (ThrVar V k t) :=
  List.flatten <|
    List.ofFn fun j : Fin t =>
      constClauses (V := ThrVar V k t) (sVar (V := V) (k := k) (t := t) 0 j.succ) false

def thrRecClauses (x : Fin k → V) : CNF.Formula (ThrVar V k t) :=
  List.flatten <|
    List.ofFn fun i : Fin k =>
      List.flatten <|
        List.ofFn fun j : Fin t =>
          and2Clauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) (x i))
              (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))
              (aVar (V := V) (k := k) (t := t) i j) ++
            or2Clauses (V := ThrVar V k t)
              (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j))
              (aVar (V := V) (k := k) (t := t) i j)
              (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j))

def thrEqvClauses (out : V) : CNF.Formula (ThrVar V k t) :=
  eqvClauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) out)
    (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t))

def thrCore (x : Fin k → V) (out : V) : CNF.Formula (ThrVar V k t) :=
  thrBaseJ0 (V := V) (k := k) (t := t) ++
    thrBaseI0 (V := V) (k := k) (t := t) ++
      thrRecClauses (V := V) (k := k) (t := t) x ++
        thrEqvClauses (V := V) (k := k) (t := t) out

def thrClauses (k t : Nat) (x : Fin k → V) (out : V) : CNF.Formula (ThrVar V k t) :=
  match t with
  | 0 => constClauses (V := ThrVar V k 0) (inVar (V := V) (k := k) (t := 0) out) true
  | t + 1 =>
      if _ : k < t + 1 then
        constClauses (V := ThrVar V k (t + 1)) (inVar (V := V) (k := k) (t := t + 1) out) false
      else
        thrCore (V := V) (k := k) (t := t + 1) x out

end Clauses

/-! ## Sequential counter semantics -/

def dp (b : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | i + 1, j + 1 => dp b i (j + 1) || (b i && dp b i j)

def pref (b : Nat → Bool) (i : Nat) : Fin i → Bool :=
  fun j => b j.1

theorem pref_succ (b : Nat → Bool) (i : Nat) :
    pref b (i + 1) =
      Fin.snoc (α := fun _ : Fin (i + 1) => Bool) (pref b i) (b i) := by
  funext j
  cases j using Fin.lastCases with
  | cast j =>
      simp [pref]
  | last =>
      simp [pref]

theorem countTrue_pref_succ (b : Nat → Bool) (i : Nat) :
    countTrue (pref b (i + 1)) = countTrue (pref b i) + (if b i then 1 else 0) := by
  simpa [pref_succ] using (countTrue_snoc (x := pref b i) (b := b i))

theorem decide_succ_le_add_ite (j c : Nat) (b : Bool) :
    decide (j + 1 ≤ c + (if b then 1 else 0)) =
      (decide (j + 1 ≤ c) || (b && decide (j ≤ c))) := by
  cases b with
  | false =>
      simp
  | true =>
      by_cases hj : j ≤ c
      · simp [hj, Nat.succ_le_succ_iff]
      · have hnotSucc : ¬ j + 1 ≤ c := by
          intro h
          exact hj (Nat.le_trans (Nat.le_succ j) h)
        simp [hj, hnotSucc, Nat.succ_le_succ_iff]

theorem dp_eq_decide_le_countTrue_pref (b : Nat → Bool) :
    ∀ i j : Nat, dp b i j = decide (j ≤ countTrue (pref b i)) := by
  intro i j
  induction i generalizing j with
  | zero =>
      cases j with
      | zero =>
          simp [dp, pref, countTrue]
      | succ j =>
          simp [dp, pref, countTrue]
  | succ i ih =>
      cases j with
      | zero =>
          simp [dp]
      | succ j =>
          have ih1 : dp b i (j + 1) = decide (j + 1 ≤ countTrue (pref b i)) :=
            ih (j := j + 1)
          have ih0 : dp b i j = decide (j ≤ countTrue (pref b i)) :=
            ih (j := j)
          -- Rewrite `countTrue (pref b (i+1))` using `snoc`.
          have hcnt :
              countTrue (pref b (i + 1)) =
                countTrue (pref b i) + (if b i then 1 else 0) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using countTrue_pref_succ b i
          -- Reduce to the arithmetic lemma.
          calc
            dp b (i + 1) (j + 1) = (dp b i (j + 1) || (b i && dp b i j)) := by
              simp [dp]
            _ =
                (decide (j + 1 ≤ countTrue (pref b i)) ||
                  (b i && decide (j ≤ countTrue (pref b i)))) := by
              simp [ih1, ih0]
            _ = decide (j + 1 ≤ countTrue (pref b i) + (if b i then 1 else 0)) := by
              simpa using
                (decide_succ_le_add_ite (j := j) (c := countTrue (pref b i)) (b := b i)).symm
            _ = decide (j + 1 ≤ countTrue (pref b (i + 1))) := by
              rw [← hcnt]

/-! ## Correctness for the threshold template -/

section Correctness

variable {k t : Nat}

theorem satisfies_flatten_ofFn {m : Nat} {W : Type} {F : Fin m → CNF.Formula W} {σ : W → Bool}
    (h : CNF.Formula.Satisfies (List.flatten (List.ofFn F)) σ) :
    ∀ i : Fin m, CNF.Formula.Satisfies (F i) σ := by
  intro i cl hcl
  apply h cl
  refine List.mem_flatten.2 ?_
  refine ⟨F i, ?_, hcl⟩
  exact List.mem_ofFn.2 ⟨i, rfl⟩

theorem satisfies_flatten_ofFn_intro {m : Nat} {W : Type} {F : Fin m → CNF.Formula W} {σ : W → Bool}
    (h : ∀ i : Fin m, CNF.Formula.Satisfies (F i) σ) :
    CNF.Formula.Satisfies (List.flatten (List.ofFn F)) σ := by
  intro cl hcl
  rcases List.mem_flatten.1 hcl with ⟨fi, hfi, hcl⟩
  rcases List.mem_ofFn.1 hfi with ⟨i, rfl⟩
  exact h i cl hcl

theorem satisfies_append_left {W : Type} {f g : CNF.Formula W} {σ : W → Bool}
    (h : CNF.Formula.Satisfies (f ++ g) σ) : CNF.Formula.Satisfies f σ := by
  intro cl hcl
  exact h cl (List.mem_append.2 (Or.inl hcl))

theorem satisfies_append_right {W : Type} {f g : CNF.Formula W} {σ : W → Bool}
    (h : CNF.Formula.Satisfies (f ++ g) σ) : CNF.Formula.Satisfies g σ := by
  intro cl hcl
  exact h cl (List.mem_append.2 (Or.inr hcl))

theorem satisfies_append {W : Type} {f g : CNF.Formula W} {σ : W → Bool}
    (hf : CNF.Formula.Satisfies f σ) (hg : CNF.Formula.Satisfies g σ) :
    CNF.Formula.Satisfies (f ++ g) σ := by
  intro cl hcl
  rcases List.mem_append.1 hcl with hcl | hcl
  · exact hf cl hcl
  · exact hg cl hcl

theorem satisfies_thrCore_sound (x : Fin k → V) (out : V) (σ : ThrVar V k t → Bool) :
    CNF.Formula.Satisfies (thrCore (V := V) (k := k) (t := t) x out) σ →
      σ (inVar (V := V) (k := k) (t := t) out) =
        decide (t ≤ countTrue (fun i : Fin k => σ (inVar (V := V) (k := k) (t := t) (x i)))) := by
  intro hsat
  classical
  have hprefix :
      CNF.Formula.Satisfies
        ((thrBaseJ0 (V := V) (k := k) (t := t) ++ thrBaseI0 (V := V) (k := k) (t := t)) ++
          thrRecClauses (V := V) (k := k) (t := t) x) σ := by
    exact satisfies_append_left (h := hsat)
  have heqv : CNF.Formula.Satisfies (thrEqvClauses (V := V) (k := k) (t := t) out) σ := by
    exact satisfies_append_right (h := hsat)
  have h12 :
      CNF.Formula.Satisfies
        (thrBaseJ0 (V := V) (k := k) (t := t) ++ thrBaseI0 (V := V) (k := k) (t := t)) σ := by
    exact satisfies_append_left (h := hprefix)
  have hrec : CNF.Formula.Satisfies (thrRecClauses (V := V) (k := k) (t := t) x) σ := by
    exact satisfies_append_right (h := hprefix)
  have hbaseJ0 : CNF.Formula.Satisfies (thrBaseJ0 (V := V) (k := k) (t := t)) σ := by
    exact satisfies_append_left (h := h12)
  have hbaseI0 : CNF.Formula.Satisfies (thrBaseI0 (V := V) (k := k) (t := t)) σ := by
    exact satisfies_append_right (h := h12)
  have hout_eq :
      σ (inVar (V := V) (k := k) (t := t) out) =
        σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) := by
    have heqv' :
        CNF.Formula.Satisfies
          (eqvClauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) out)
            (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t))) σ := by
      simpa [thrEqvClauses] using heqv
    exact
      (satisfies_eqvClauses_iff (V := ThrVar V k t) (σ := σ)
        (v := inVar (V := V) (k := k) (t := t) out)
        (w := sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t))).1 heqv'
  -- Define the input stream `b : Nat → Bool`.
  let b : Nat → Bool :=
    fun i => if h : i < k then σ (inVar (V := V) (k := k) (t := t) (x ⟨i, h⟩)) else false
  have hbFin : ∀ i : Fin k, b i.1 = σ (inVar (V := V) (k := k) (t := t) (x i)) := by
    intro i
    simp [b, i.2]
  -- Recover the DP table from satisfaction.
  have hs_i0 : ∀ i : Fin (k + 1),
      σ (sVar (V := V) (k := k) (t := t) i 0) = true := by
    intro i
    have hiSat := satisfies_flatten_ofFn (m := k + 1)
      (F := fun i : Fin (k + 1) =>
        constClauses (V := ThrVar V k t) (sVar (V := V) (k := k) (t := t) i 0) true)
      (σ := σ) (by simpa [thrBaseJ0] using hbaseJ0) i
    exact (satisfies_constClauses_iff (V := ThrVar V k t) (σ := σ)
      (v := sVar (V := V) (k := k) (t := t) i 0) (b := true)).1 hiSat
  have hs_0j : ∀ j : Fin t,
      σ (sVar (V := V) (k := k) (t := t) 0 j.succ) = false := by
    intro j
    have hjSat := satisfies_flatten_ofFn (m := t)
      (F := fun j : Fin t =>
        constClauses (V := ThrVar V k t) (sVar (V := V) (k := k) (t := t) 0 j.succ) false)
      (σ := σ) (by simpa [thrBaseI0] using hbaseI0) j
    exact (satisfies_constClauses_iff (V := ThrVar V k t) (σ := σ)
      (v := sVar (V := V) (k := k) (t := t) 0 j.succ) (b := false)).1 hjSat
  have hs_rec :
      ∀ i : Fin k, ∀ j : Fin t,
        σ (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j)) =
          (σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j)) ||
            (σ (inVar (V := V) (k := k) (t := t) (x i)) &&
              σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j)))) := by
    intro i j
    have hiSat :=
      satisfies_flatten_ofFn (m := k)
        (F := fun i : Fin k =>
          List.flatten <|
            List.ofFn fun j : Fin t =>
              and2Clauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) (x i))
                  (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))
                  (aVar (V := V) (k := k) (t := t) i j) ++
                or2Clauses (V := ThrVar V k t)
                  (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j))
                  (aVar (V := V) (k := k) (t := t) i j)
                  (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j)))
        (σ := σ) (by simpa [thrRecClauses] using hrec) i
    have hjSat :=
      satisfies_flatten_ofFn (m := t)
        (F := fun j : Fin t =>
          and2Clauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) (x i))
              (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))
              (aVar (V := V) (k := k) (t := t) i j) ++
            or2Clauses (V := ThrVar V k t)
              (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j))
              (aVar (V := V) (k := k) (t := t) i j)
              (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j)))
        (σ := σ) hiSat j
    have hand : CNF.Formula.Satisfies
        (and2Clauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) (x i))
          (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))
          (aVar (V := V) (k := k) (t := t) i j)) σ := by
      exact satisfies_append_left (f := _) (g := _) (σ := σ) (by simpa using hjSat)
    have hor : CNF.Formula.Satisfies
        (or2Clauses (V := ThrVar V k t)
          (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j))
          (aVar (V := V) (k := k) (t := t) i j)
          (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j))) σ := by
      exact satisfies_append_right (f := _) (g := _) (σ := σ) (by simpa using hjSat)
    have ha :
        σ (aVar (V := V) (k := k) (t := t) i j) =
          (σ (inVar (V := V) (k := k) (t := t) (x i)) &&
            σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))) := by
      exact satisfies_and2Clauses (V := ThrVar V k t) (σ := σ) hand
    have hs :
        σ (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j)) =
          (σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j)) ||
            σ (aVar (V := V) (k := k) (t := t) i j)) := by
      exact satisfies_or2Clauses (V := ThrVar V k t) (σ := σ) hor
    simp [hs, ha]
  -- Prove that `sVar` matches `dp b`.
  have hs_dp :
      ∀ i j : Nat, ∀ hi : i ≤ k, ∀ hj : j ≤ t,
        σ (sVar (V := V) (k := k) (t := t) ⟨i, Nat.lt_succ_of_le hi⟩
            ⟨j, Nat.lt_succ_of_le hj⟩) = dp b i j := by
    intro i j hi hj
    induction i generalizing j with
    | zero =>
        cases j with
        | zero =>
            have : σ (sVar (V := V) (k := k) (t := t) 0 0) = true := hs_i0 0
            simpa [dp] using this
        | succ j =>
            have hj' : j < t := Nat.lt_of_succ_le hj
            have hfin :
                σ (sVar (V := V) (k := k) (t := t) 0 ⟨j + 1, Nat.succ_lt_succ hj'⟩) = false := by
              have : σ (sVar (V := V) (k := k) (t := t) 0 (Fin.succ ⟨j, hj'⟩)) = false :=
                hs_0j ⟨j, hj'⟩
              simpa using this
            simpa [dp] using hfin
    | succ i ih =>
        cases j with
        | zero =>
            have : σ (sVar (V := V) (k := k) (t := t) ⟨i + 1, Nat.lt_succ_of_le hi⟩ 0) = true :=
              hs_i0 ⟨i + 1, Nat.lt_succ_of_le hi⟩
            simpa [dp] using this
        | succ j =>
            have hi' : i < k := lt_of_lt_of_le (Nat.lt_succ_self i) hi
            have hj' : j < t := Nat.lt_of_succ_le hj
            let iFin : Fin k := ⟨i, hi'⟩
            let jFin : Fin t := ⟨j, hj'⟩
            have hsRec := hs_rec iFin jFin
            have hcastI :
                (⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi')⟩ : Fin (k + 1)) = Fin.castSucc iFin := by
              ext; rfl
            have hsuccI :
                (⟨i + 1, Nat.lt_succ_of_le hi⟩ : Fin (k + 1)) = Fin.succ iFin := by
              ext; rfl
            have hcastJ :
                (⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hj')⟩ : Fin (t + 1)) = Fin.castSucc jFin := by
              ext; rfl
            have hsuccJ :
                (⟨j + 1, Nat.lt_succ_of_le hj⟩ : Fin (t + 1)) = Fin.succ jFin := by
              ext; rfl
            have hsRec' :
                σ (sVar (V := V) (k := k) (t := t) ⟨i + 1, Nat.lt_succ_of_le hi⟩
                    ⟨j + 1, Nat.lt_succ_of_le hj⟩) =
                  (σ (sVar (V := V) (k := k) (t := t) ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi')⟩
                      ⟨j + 1, Nat.lt_succ_of_le hj⟩) ||
                    (σ (inVar (V := V) (k := k) (t := t) (x iFin)) &&
                      σ (sVar (V := V) (k := k) (t := t) ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi')⟩
                        ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hj')⟩))) := by
              simpa [hcastI, hsuccI, hcastJ, hsuccJ] using hsRec
            have ih1 :
                σ (sVar (V := V) (k := k) (t := t) ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi')⟩
                    ⟨j + 1, Nat.lt_succ_of_le hj⟩) = dp b i (j + 1) :=
              ih (j := j + 1) (Nat.le_of_lt hi') hj
            have ih0 :
                σ (sVar (V := V) (k := k) (t := t) ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi')⟩
                    ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hj')⟩) = dp b i j :=
              ih (j := j) (Nat.le_of_lt hi') (Nat.le_of_lt hj')
            have hb : σ (inVar (V := V) (k := k) (t := t) (x iFin)) = b i := by
              simpa using (hbFin iFin).symm
            simp [hsRec', ih1, ih0, hb, dp]
  -- Specialize at `i = k`, `j = t`.
  have hskt :
      σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) = dp b k t := by
    have hk : (k : Nat) ≤ k := le_rfl
    have ht : (t : Nat) ≤ t := le_rfl
    -- `Fin.last` has value `k` and `t`.
    have hfinK : (Fin.last k : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := by
      rfl
    have hfinT : (Fin.last t : Fin (t + 1)) = ⟨t, Nat.lt_succ_self t⟩ := by
      rfl
    simpa [hfinK, hfinT] using hs_dp k t hk ht
  -- Relate `dp` to `countTrue`.
  have hdp :
      dp b k t = decide (t ≤ countTrue (pref b k)) :=
    dp_eq_decide_le_countTrue_pref (b := b) (i := k) (j := t)
  have hprefix :
      pref b k = fun i : Fin k => σ (inVar (V := V) (k := k) (t := t) (x i)) := by
    funext i
    simp [pref, hbFin i]
  -- Put everything together.
  calc
    σ (inVar (V := V) (k := k) (t := t) out)
        = σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) := hout_eq
    _ = dp b k t := hskt
    _ = decide (t ≤ countTrue (pref b k)) := hdp
    _ = decide (t ≤ countTrue (fun i : Fin k => σ (inVar (V := V) (k := k) (t := t) (x i)))) := by
        simp [hprefix]

def extend (σ₀ : V → Bool) (x : Fin k → V) : ThrVar V k t → Bool
  | Sum.inl v => σ₀ v
  | Sum.inr u =>
      match u with
      | .s i j =>
          dp (fun n => if h : n < k then σ₀ (x ⟨n, h⟩) else false) i.1 j.1
      | .a i j =>
          let b : Nat → Bool := fun n => if h : n < k then σ₀ (x ⟨n, h⟩) else false
          b i.1 && dp b i.1 j.1

theorem satisfies_thrCore_complete (x : Fin k → V) (out : V) (σ₀ : V → Bool)
    (hout :
      σ₀ out =
        decide (t ≤ countTrue (fun i : Fin k => σ₀ (x i)))) :
    CNF.Formula.Satisfies (thrCore (V := V) (k := k) (t := t) x out)
      (extend (V := V) (k := k) (t := t) σ₀ x) := by
  classical
  let σ : ThrVar V k t → Bool := extend (V := V) (k := k) (t := t) σ₀ x
  let b : Nat → Bool := fun n => if h : n < k then σ₀ (x ⟨n, h⟩) else false
  have hbFin : ∀ i : Fin k, b i.1 = σ₀ (x i) := by
    intro i
    simp [b, i.2]
  have hs_i0 : ∀ i : Fin (k + 1), σ (sVar (V := V) (k := k) (t := t) i 0) = true := by
    intro i
    simp [σ, extend, dp, sVar]
  have hs_0j : ∀ j : Fin t, σ (sVar (V := V) (k := k) (t := t) 0 j.succ) = false := by
    intro j
    simp [σ, extend, dp, sVar]
  have hbaseJ0 : CNF.Formula.Satisfies (thrBaseJ0 (V := V) (k := k) (t := t)) σ := by
    unfold thrBaseJ0
    refine satisfies_flatten_ofFn_intro ?_
    intro i
    exact (satisfies_constClauses_iff (V := ThrVar V k t) (σ := σ)
      (v := sVar (V := V) (k := k) (t := t) i 0) (b := true)).2 (hs_i0 i)
  have hbaseI0 : CNF.Formula.Satisfies (thrBaseI0 (V := V) (k := k) (t := t)) σ := by
    unfold thrBaseI0
    refine satisfies_flatten_ofFn_intro ?_
    intro j
    exact (satisfies_constClauses_iff (V := ThrVar V k t) (σ := σ)
      (v := sVar (V := V) (k := k) (t := t) 0 j.succ) (b := false)).2 (hs_0j j)
  have hrec : CNF.Formula.Satisfies (thrRecClauses (V := V) (k := k) (t := t) x) σ := by
    unfold thrRecClauses
    refine satisfies_flatten_ofFn_intro ?_
    intro i
    refine satisfies_flatten_ofFn_intro ?_
    intro j
    have handEq :
        σ (aVar (V := V) (k := k) (t := t) i j) =
          (σ (inVar (V := V) (k := k) (t := t) (x i)) &&
            σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))) := by
      simp [σ, extend, aVar, inVar, sVar]
    have horEq :
        σ (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j)) =
          (σ (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j)) ||
            σ (aVar (V := V) (k := k) (t := t) i j)) := by
      simp [σ, extend, aVar, sVar, dp]
    have hand :
        CNF.Formula.Satisfies
          (and2Clauses (V := ThrVar V k t) (inVar (V := V) (k := k) (t := t) (x i))
            (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.castSucc j))
            (aVar (V := V) (k := k) (t := t) i j)) σ :=
      satisfies_and2Clauses_of_eq (V := ThrVar V k t) (σ := σ) handEq
    have hor :
        CNF.Formula.Satisfies
          (or2Clauses (V := ThrVar V k t)
            (sVar (V := V) (k := k) (t := t) (Fin.castSucc i) (Fin.succ j))
            (aVar (V := V) (k := k) (t := t) i j)
            (sVar (V := V) (k := k) (t := t) (Fin.succ i) (Fin.succ j))) σ :=
      satisfies_or2Clauses_of_eq (V := ThrVar V k t) (σ := σ) horEq
    exact satisfies_append hand hor
  have hdp :
      dp b k t = decide (t ≤ countTrue (fun i : Fin k => σ₀ (x i))) := by
    have h' := dp_eq_decide_le_countTrue_pref (b := b) (i := k) (j := t)
    have hpref : pref b k = fun i : Fin k => σ₀ (x i) := by
      funext i
      simp [pref, b, i.2]
    simpa [hpref] using h'
  have hsLast :
      σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) = dp b k t := by
    simp [σ, extend, b, sVar]
  have heq :
      σ (inVar (V := V) (k := k) (t := t) out) =
        σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) := by
    calc
      σ (inVar (V := V) (k := k) (t := t) out) = σ₀ out := rfl
      _ = decide (t ≤ countTrue (fun i : Fin k => σ₀ (x i))) := hout
      _ = dp b k t := by
            simpa using hdp.symm
      _ = σ (sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t)) := hsLast.symm
  have heqv : CNF.Formula.Satisfies (thrEqvClauses (V := V) (k := k) (t := t) out) σ := by
    unfold thrEqvClauses
    exact
      (satisfies_eqvClauses_iff (V := ThrVar V k t) (σ := σ)
        (v := inVar (V := V) (k := k) (t := t) out)
        (w := sVar (V := V) (k := k) (t := t) (Fin.last k) (Fin.last t))).2 heq
  have h12 :
      CNF.Formula.Satisfies
        (thrBaseJ0 (V := V) (k := k) (t := t) ++ thrBaseI0 (V := V) (k := k) (t := t)) σ :=
    satisfies_append hbaseJ0 hbaseI0
  have h123 :
      CNF.Formula.Satisfies
        (thrBaseJ0 (V := V) (k := k) (t := t) ++ thrBaseI0 (V := V) (k := k) (t := t) ++
          thrRecClauses (V := V) (k := k) (t := t) x) σ :=
    satisfies_append h12 hrec
  have h1234 :
      CNF.Formula.Satisfies
        (thrBaseJ0 (V := V) (k := k) (t := t) ++ thrBaseI0 (V := V) (k := k) (t := t) ++
          thrRecClauses (V := V) (k := k) (t := t) x ++
            thrEqvClauses (V := V) (k := k) (t := t) out) σ :=
    satisfies_append h123 heqv
  simpa [thrCore, σ] using h1234

theorem satisfies_thrClauses_sound (k t : Nat) (x : Fin k → V) (out : V) (σ : ThrVar V k t → Bool) :
    CNF.Formula.Satisfies (thrClauses (V := V) k t x out) σ →
      σ (inVar (V := V) (k := k) (t := t) out) =
        decide (t ≤ countTrue (fun i : Fin k => σ (inVar (V := V) (k := k) (t := t) (x i)))) := by
  classical
  cases t with
  | zero =>
      intro hsat
      have hout' :
          σ (inVar (V := V) (k := k) (t := 0) out) = true := by
        have :=
          (satisfies_constClauses_iff (V := ThrVar V k 0) (σ := σ)
            (v := inVar (V := V) (k := k) (t := 0) out) (b := true)).1 hsat
        simpa using this
      simp [hout']
  | succ t =>
      by_cases hk : k < t + 1
      · intro hsat
        have hout' :
            σ (inVar (V := V) (k := k) (t := t + 1) out) = false := by
          have :
              CNF.Formula.Satisfies
                (constClauses (V := ThrVar V k (t + 1))
                  (inVar (V := V) (k := k) (t := t + 1) out) false) σ := by
            simpa [thrClauses, hk] using hsat
          exact
            (satisfies_constClauses_iff (V := ThrVar V k (t + 1)) (σ := σ)
              (v := inVar (V := V) (k := k) (t := t + 1) out) (b := false)).1 this
        have hct :
            countTrue (fun i : Fin k => σ (inVar (V := V) (k := k) (t := t + 1) (x i))) ≤ k :=
          countTrue_le _
        have hnot : ¬ (t + 1 ≤ countTrue (fun i : Fin k =>
            σ (inVar (V := V) (k := k) (t := t + 1) (x i)))) := by
          intro ht
          have : t + 1 ≤ k := Nat.le_trans ht hct
          exact Nat.not_lt_of_ge this hk
        have hdec :
            decide (t + 1 ≤ countTrue (fun i : Fin k =>
              σ (inVar (V := V) (k := k) (t := t + 1) (x i)))) = false := by
          exact (decide_eq_false_iff_not).2 hnot
        exact hout'.trans hdec.symm
      · intro hsat
        have :
            CNF.Formula.Satisfies (thrCore (V := V) (k := k) (t := t + 1) x out) σ := by
          simpa [thrClauses, hk] using hsat
        have hsound :=
          satisfies_thrCore_sound (V := V) (k := k) (t := t + 1) (x := x) (out := out) (σ := σ) this
        simpa using hsound

theorem satisfies_thrClauses_complete (k t : Nat) (x : Fin k → V) (out : V) (σ₀ : V → Bool)
    (hout :
      σ₀ out =
        decide (t ≤ countTrue (fun i : Fin k => σ₀ (x i)))) :
    CNF.Formula.Satisfies (thrClauses (V := V) k t x out)
      (extend (V := V) (k := k) (t := t) σ₀ x) := by
  classical
  cases t with
  | zero =>
      -- Output must be `true`.
      have hout' : σ₀ out = true := by simpa using hout
      have :
          (extend (V := V) (k := k) (t := 0) σ₀ x)
              (inVar (V := V) (k := k) (t := 0) out) = true := by
        simpa [CNFEnc.extend, inVar] using hout'
      exact
        (satisfies_constClauses_iff (V := ThrVar V k 0)
          (σ := extend (V := V) (k := k) (t := 0) σ₀ x)
          (v := inVar (V := V) (k := k) (t := 0) out) (b := true)).2 this
  | succ t =>
      by_cases hk : k < t + 1
      · -- Output forced `false`.
        have hct : countTrue (fun i : Fin k => σ₀ (x i)) ≤ k := countTrue_le _
        have hnot : ¬ (t + 1 ≤ countTrue (fun i : Fin k => σ₀ (x i))) := by
          intro ht
          have : t + 1 ≤ k := Nat.le_trans ht hct
          exact Nat.not_lt_of_ge this hk
        have hdec : decide (t + 1 ≤ countTrue (fun i : Fin k => σ₀ (x i))) = false := by
          exact (decide_eq_false_iff_not).2 hnot
        have hout' : σ₀ out = false :=
          hout.trans hdec
        have :
            (extend (V := V) (k := k) (t := t + 1) σ₀ x)
                (inVar (V := V) (k := k) (t := t + 1) out) = false := by
          simpa [CNFEnc.extend, inVar] using hout'
        have :
            CNF.Formula.Satisfies
              (constClauses (V := ThrVar V k (t + 1))
                (inVar (V := V) (k := k) (t := t + 1) out) false)
              (extend (V := V) (k := k) (t := t + 1) σ₀ x) :=
          (satisfies_constClauses_iff (V := ThrVar V k (t + 1))
            (σ := extend (V := V) (k := k) (t := t + 1) σ₀ x)
            (v := inVar (V := V) (k := k) (t := t + 1) out) (b := false)).2 this
        simpa [thrClauses, hk] using this
      · -- General case: reduce to `thrCore`.
        have :
            CNF.Formula.Satisfies (thrCore (V := V) (k := k) (t := t + 1) x out)
              (extend (V := V) (k := k) (t := t + 1) σ₀ x) :=
          satisfies_thrCore_complete (V := V) (k := k) (t := t + 1)
            (x := x) (out := out) (σ₀ := σ₀) hout
        simpa [thrClauses, hk] using this

end Correctness

end CNFEnc

end Circuit

end Computability
