/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Computability.Formula.Basic
public import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.OfFn

/-!
# Encoding formulas

This file provides an `Encodable` instance for syntax-tree formulas `Formula G n`, assuming the
gate labels are encodable: `[∀ k, Encodable (G k)]`.

The approach is to translate formulas to a small s-expression type `S`, and then use a fixed
encoding `S → ℕ` based on `Nat.pair`.
-/

@[expose] public section

namespace Computability

namespace Formula

namespace Encoding

variable {G : Nat → Type} {n : Nat}

/-!
## A small s-expression type

We use a minimal tree type with natural leaves, equipped with an `Encodable` instance via a
pairing-based `S ≃ ℕ` encoding. The construction follows the same idea as the `Encodable` deriving
handler.
-/

inductive S : Type where
  | nat (n : ℕ)
  | cons (a b : S)

namespace S

def encode : S → ℕ
  | nat n => Nat.pair 0 n
  | cons a b => Nat.pair (encode a + 1) (encode b)

lemma right_lt_pair_of_left_ne_zero {a b : ℕ} (ha : a ≠ 0) : b < Nat.pair a b := by
  by_cases h : a < b
  · -- `pair a b = b*b + a`
    have ha' : 0 < a := Nat.pos_of_ne_zero ha
    have hb' : 0 < b := lt_trans ha' h
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb'
    have hb_le : b ≤ b * b := by
      simpa [Nat.mul_one] using (Nat.mul_le_mul_left b hb1)
    have hb_lt : b * b < b * b + a := Nat.lt_add_of_pos_right (n := b * b) (k := a) ha'
    have : b < b * b + a := lt_of_le_of_lt hb_le hb_lt
    simpa [Nat.pair, h] using this
  · -- `pair a b = a*a + a + b`
    have ha' : 0 < a := Nat.pos_of_ne_zero ha
    have hpos : 0 < a * a + a := Nat.add_pos_right (a := a * a) (b := a) ha'
    have hb_lt : b < b + (a * a + a) := Nat.lt_add_of_pos_right (n := b) (k := a * a + a) hpos
    have : b < a * a + a + b := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb_lt
    simpa [Nat.pair, h] using this

lemma unpair_right_lt_of_fst_ne_zero {n : ℕ} (h : (Nat.unpair n).1 ≠ 0) :
    (Nat.unpair n).2 < n := by
  have hn : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := Nat.pair_unpair n
  simpa [hn] using
    right_lt_pair_of_left_ne_zero (a := (Nat.unpair n).1) (b := (Nat.unpair n).2) h

def decode (n : ℕ) : S :=
  let p := Nat.unpair n
  if h : p.1 = 0 then
    S.nat p.2
  else
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      -- `Nat.unpair 0 = 0`, contradicting `p.1 ≠ 0`.
      exact h (by simp [p])
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hp1_lt : p.1 < n := Nat.unpair_lt hn1
    have hp1_pos : 0 < p.1 := Nat.pos_of_ne_zero (by simpa [Prod.fst] using h)
    have : p.1 - 1 < n := lt_trans (Nat.sub_lt hp1_pos Nat.zero_lt_one) hp1_lt
    have : p.2 < n := unpair_right_lt_of_fst_ne_zero (by simpa [Prod.fst] using h)
    S.cons (decode (p.1 - 1)) (decode p.2)

theorem decode_encode : ∀ s : S, decode (encode s) = s
  | nat n => by
      simp [encode, decode]
  | cons a b => by
      simp [encode, decode, decode_encode a, decode_encode b]

instance : Encodable S where
  encode := encode
  decode := fun n => some (decode n)
  encodek := by
    intro s
    simp [decode_encode]

def list : List S → S
  | [] => S.nat 0
  | x :: xs => S.cons x (list xs)

lemma sizeOf_lt_cons_left (a b : S) : sizeOf a < sizeOf (S.cons a b) := by
  -- `sizeOf (cons a b) = 1 + sizeOf a + sizeOf b`
  have h : sizeOf a < sizeOf a + Nat.succ (sizeOf b) :=
    Nat.lt_add_of_pos_right (n := sizeOf a) (k := Nat.succ (sizeOf b)) (Nat.succ_pos _)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma sizeOf_lt_cons_right (a b : S) : sizeOf b < sizeOf (S.cons a b) := by
  have h : sizeOf b < sizeOf b + Nat.succ (sizeOf a) :=
    Nat.lt_add_of_pos_right (n := sizeOf b) (k := Nat.succ (sizeOf a)) (Nat.succ_pos _)
  -- Rearrange into `1 + sizeOf a + sizeOf b`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

lemma zero_lt_one_add_sizeOf (a : S) : 0 < 1 + sizeOf a := by
  -- `Nat.succ_pos` gives `0 < sizeOf a + 1`; swap the addends.
  simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Nat.succ_pos (sizeOf a))

lemma sizeOf_lt_gateChildren (k g : ℕ) (ch : S) :
    sizeOf ch <
      sizeOf
        (S.cons (S.nat 2)
          (S.cons (S.nat k) (S.cons (S.nat g) (S.cons ch (S.nat 0))))) := by
  have h0 : sizeOf ch < sizeOf (S.cons ch (S.nat 0)) := sizeOf_lt_cons_left _ _
  have h1 :
      sizeOf (S.cons ch (S.nat 0)) <
        sizeOf (S.cons (S.nat g) (S.cons ch (S.nat 0))) := sizeOf_lt_cons_right _ _
  have h2 :
      sizeOf (S.cons (S.nat g) (S.cons ch (S.nat 0))) <
        sizeOf (S.cons (S.nat k) (S.cons (S.nat g) (S.cons ch (S.nat 0)))) :=
    sizeOf_lt_cons_right _ _
  have h3 :
      sizeOf (S.cons (S.nat k) (S.cons (S.nat g) (S.cons ch (S.nat 0)))) <
        sizeOf
          (S.cons (S.nat 2)
            (S.cons (S.nat k) (S.cons (S.nat g) (S.cons ch (S.nat 0))))) :=
    sizeOf_lt_cons_right _ _
  exact lt_trans h0 (lt_trans h1 (lt_trans h2 h3))

end S

section

variable [∀ k, Encodable (G k)]

def toS : Formula G n → S
  | .input i =>
      S.cons (S.nat 0) (S.cons (S.nat (Encodable.encode i)) (S.nat 0))
  | .const b =>
      S.cons (S.nat 1) (S.cons (S.nat (Encodable.encode b)) (S.nat 0))
  | .gate (k := k) g f =>
      S.cons (S.nat 2)
        (S.cons (S.nat k)
          (S.cons (S.nat (Encodable.encode g))
            (S.cons (S.list (List.ofFn fun i : Fin k => toS (f i))) (S.nat 0))))

mutual

def fromS : S → Option (Formula G n)
  | S.cons (S.nat 0) (S.cons (S.nat i) (S.nat 0)) =>
      (Encodable.decode i).map Formula.input
  | S.cons (S.nat 1) (S.cons (S.nat b) (S.nat 0)) =>
      (Encodable.decode b).map Formula.const
  | S.cons (S.nat 2) (S.cons (S.nat k) (S.cons (S.nat g) (S.cons ch (S.nat 0)))) => by
      classical
      refine (Encodable.decode (α := G k) g).bind fun g => ?_
      refine (fromSChildren k ch).map fun f => ?_
      exact Formula.gate g f
  | _ => none
termination_by s => sizeOf s

def fromSChildren : (k : Nat) → S → Option (Fin k → Formula G n)
  | 0, s =>
      match s with
      | S.nat 0 => some Fin.elim0
      | _ => none
  | k + 1, S.cons a b =>
      (fromS a).bind fun c =>
        (fromSChildren k b).map fun f => Fin.cons c f
  | k + 1, _ => none
termination_by _ s => sizeOf s
decreasing_by
  all_goals
    simp_wf
    first
    | simpa using S.sizeOf_lt_cons_left _ _
    | simpa using S.sizeOf_lt_cons_right _ _
    | simpa using S.sizeOf_lt_gateChildren _ _ _
    | simpa using S.zero_lt_one_add_sizeOf _

end

theorem fromSChildren_list_ofFn :
    ∀ {k : Nat} (f : Fin k → Formula G n),
      (∀ i : Fin k, fromS (toS (f i)) = some (f i)) →
        fromSChildren k (S.list (List.ofFn fun i : Fin k => toS (f i))) = some f := by
  intro k f hf
  induction k with
  | zero =>
      have hf0 : f = (Fin.elim0 : Fin 0 → Formula G n) := by
        funext i
        cases (Nat.not_lt_zero i.1 i.2)
      subst hf0
      simp [S.list, fromSChildren, List.ofFn_zero]
  | succ k hk =>
      have hf_head : fromS (toS (f 0)) = some (f 0) := hf 0
      have hf_tail : ∀ i : Fin k, fromS (toS (f i.succ)) = some (f i.succ) :=
        fun i => hf i.succ
      have hk' :
          fromSChildren k
              (S.list (List.ofFn fun i : Fin k => toS (f i.succ))) =
            some (fun i : Fin k => f i.succ) :=
        hk (f := fun i : Fin k => f i.succ) hf_tail
      have hcons : Fin.cons (f 0) (fun i : Fin k => f i.succ) = f := by
        funext i
        cases i using Fin.cases with
        | zero => simp
        | succ j => simp
      have hofn :
          List.ofFn (fun i : Fin (Nat.succ k) => toS (f i)) =
            toS (f 0) :: List.ofFn (fun i : Fin k => toS (f i.succ)) := by
        have hfun :
            (fun i : Fin (Nat.succ k) => toS (f i)) =
              Fin.cons (toS (f 0)) (fun i : Fin k => toS (f i.succ)) := by
          funext i
          cases i using Fin.cases with
          | zero => simp
          | succ j => simp
        simp [hfun]
      -- Unfold one step of the list encoding and child decoder.
      rw [hofn]
      simp [S.list, fromSChildren, hf_head, hk', hcons]

theorem fromS_toS : ∀ c : Formula G n, fromS (toS c) = some c := by
  intro c
  induction c with
  | input i =>
      simp [toS, fromS, Encodable.encodek]
  | const b =>
      simp [toS, fromS, Encodable.encodek]
  | gate g f ih =>
      classical
      have hf : ∀ i, fromS (toS (f i)) = some (f i) := ih
      have hch :
          fromSChildren _ (S.list (List.ofFn fun i => toS (f i))) =
            some f :=
        fromSChildren_list_ofFn (f := f) hf
      -- Now unfold `fromS` at the gate constructor.
      simp [toS, fromS, hch, Encodable.encodek]

instance : Encodable (Formula G n) :=
  Encodable.ofLeftInjection (α := S) (β := Formula G n) toS fromS fromS_toS

end

end Encoding

end Formula

end Computability
