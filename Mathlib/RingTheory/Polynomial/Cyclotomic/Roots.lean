/-
Copyright (c) 2020 Riccardo Brasca, 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Dennj Osele
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `IsPrimitiveRoot.isRoot_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `isRoot_cyclotomic_iff` : if `NeZero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `Polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `Polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `Polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

public section


namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : ℕ} (hi : i ∈ n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub, eval_X_pow, eval_one] at this
  convert eq_add_of_sub_eq' this
  convert (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section IsDomain

variable [IsDomain R]

theorem _root_.isRoot_of_unity_iff (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nthRoots h, nthRoots, mem_roots <| X_pow_sub_C_ne_zero h _, C_1, ←
      prod_cyclotomic_eq_X_pow_sub_one h, isRoot_prod]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n R`. -/
theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R), cyclotomic_eq_prod_X_sub_primitiveRoots h,
    roots_prod_X_sub_C, ← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

private theorem isRoot_cyclotomic_iff' {n : ℕ} {K : Type*} [Field K] {μ : K} [NeZero (n : K)] :
    IsRoot (cyclotomic n K) μ ↔ IsPrimitiveRoot μ n := by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_contra hnμ
  have ho : 0 < orderOf μ := (isOfFinOrder_iff_pow_eq_one.2 <| ⟨n, hnpos, hμn⟩).orderOf_pos
  have := pow_orderOf_eq_one μ
  rw [isRoot_of_unity_iff ho] at this
  obtain ⟨i, hio, hiμ⟩ := this
  replace hio := Nat.dvd_of_mem_divisors hio
  rw [IsPrimitiveRoot.not_iff] at hnμ
  rw [← orderOf_dvd_iff_pow_eq_one] at hμn
  have key : i < n := (Nat.le_of_dvd ho hio).trans_lt ((Nat.le_of_dvd hnpos hμn).lt_of_ne hnμ)
  have key' : i ∣ n := hio.trans hμn
  rw [← Polynomial.dvd_iff_isRoot] at hμ hiμ
  have hni : {i, n} ⊆ n.divisors := by simpa [Finset.insert_subset_iff, key'] using hnpos.ne'
  obtain ⟨k, hk⟩ := hiμ
  obtain ⟨j, hj⟩ := hμ
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K
  rw [← Finset.prod_sdiff hni, Finset.prod_pair key.ne, hk, hj] at this
  have hn := (X_pow_sub_one_separable_iff.mpr <| NeZero.natCast_ne n K).squarefree
  rw [← this, Squarefree] at hn
  specialize hn (X - C μ) ⟨(∏ x ∈ n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩
  simp [Polynomial.isUnit_iff_degree_eq_zero] at hn

theorem isRoot_cyclotomic_iff [NeZero (n : R)] {μ : R} :
    IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n := by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  haveI : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf, ← IsPrimitiveRoot.map_iff_of_injective hf, map_cyclotomic, ←
    isRoot_cyclotomic_iff']

theorem roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup := by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R, isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
      cyclotomic.dvd_X_pow_sub_one n R) hζ.nthRoots_one_nodup

theorem cyclotomic.roots_to_finset_eq_primitiveRoots [NeZero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : Finset _) = primitiveRoots n R := by
  ext a
  simp [cyclotomic_ne_zero n R, ← isRoot_cyclotomic_iff, mem_primitiveRoots,
    NeZero.pos_of_neZero_natCast R]

theorem cyclotomic.roots_eq_primitiveRoots_val [NeZero (n : R)] :
    (cyclotomic n R).roots = (primitiveRoots n R).val := by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
theorem isRoot_cyclotomic_iff_charZero {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {μ : R} (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ IsPrimitiveRoot μ n :=
  letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

end IsDomain

/-- Over a ring `R` of characteristic zero, `fun n => cyclotomic n R` is injective. -/
theorem cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · haveI := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom ℂ)) hnm
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm
    have hprim := Complex.isPrimitiveRoot_exp _ hzero
    have hroot := isRoot_cyclotomic_iff (R := ℂ).2 hprim
    rw [hnm] at hroot
    haveI hmzero : NeZero m := ⟨fun h => by simp [h] at hroot⟩
    rw [isRoot_cyclotomic_iff (R := ℂ)] at hroot
    replace hprim := hprim.eq_orderOf
    rwa [← IsPrimitiveRoot.eq_orderOf hroot] at hprim

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [Field K] {μ : K}
    (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ := by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

section minpoly

open IsPrimitiveRoot Complex

theorem _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] {μ : R} {n : ℕ} [Algebra K R] (hμ : IsPrimitiveRoot μ n)
    (h : Irreducible <| cyclotomic n K) [NeZero (n : K)] : cyclotomic n K = minpoly K μ := by
  haveI := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n ℤ] using totient_le_degree_minpoly h

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℚ = minpoly ℚ μ := by
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

/-- `cyclotomic n ℤ` is irreducible. -/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) := by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

/-- `cyclotomic n ℚ` is irreducible. -/
theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ) := by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n ℤ)).1
    (cyclotomic.irreducible hpos)

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
theorem cyclotomic.isCoprime_rat {n m : ℕ} (h : n ≠ m) :
    IsCoprime (cyclotomic n ℚ) (cyclotomic m ℚ) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
  exact fun hdiv => h <| cyclotomic_injective <|
    eq_of_monic_of_associated (cyclotomic.monic n ℚ) (cyclotomic.monic m ℚ) <|
      Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero)
        (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

end Polynomial

/-!
## Vanishing sums of roots of unity

For a prime `p`, a ℚ-linear combination of `p`-th roots of unity vanishes if and only if
all coefficients are equal. This is a fundamental result in algebraic number theory,
following from the irreducibility of the `p`-th cyclotomic polynomial.

## References

* Washington, *Introduction to Cyclotomic Fields*, Lemma 2.8.5
-/

namespace IsPrimitiveRoot

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : ℕ} [Fact (Nat.Prime p)] {ζ : K}

/-- For a prime `p` and a primitive `p`-th root `ζ` in a characteristic zero field,
a ℚ-linear combination `∑ αᵢ ζ^i` vanishes if and only if all coefficients `αᵢ` are equal.

This characterizes exactly when such sums vanish, and follows from the irreducibility
of the cyclotomic polynomial. -/
theorem sum_eq_zero_iff_eq_coeff (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℚ) :
    ∑ i : Fin p, (α i : K) * ζ ^ i.val = 0 ↔ ∀ i j : Fin p, α i = α j := by
  constructor
  -- Forward direction: vanishing implies equal coefficients
  · intro hsum
    classical
    have hprime : Nat.Prime p := Fact.out
    have hpos : 0 < p := hprime.pos
    have hne0 : p ≠ 0 := hprime.ne_zero
    have hone_lt : 1 < p := hprime.one_lt
    haveI : NeZero p := ⟨hne0⟩
    -- Use a total function on ℕ to avoid dependent Fin casts.
    let αNat : ℕ → ℚ := fun i => if hi : i < p then α ⟨i, hi⟩ else 0
    -- Rewrite the sum over `Fin p` as a sum over `Finset.range p`.
    have hαNat_val : ∀ i : Fin p, αNat i.val = α i := fun ⟨_, hi⟩ => dif_pos hi
    have hsum_range : ∑ i ∈ Finset.range p, (αNat i : K) * ζ ^ i = 0 := by
      have := Fin.sum_univ_eq_sum_range (fun i => (αNat i : K) * ζ ^ i) p
      simp only [hαNat_val] at this; rw [← this]; exact hsum
    -- Split off the last term at index `n = p - 1`.
    set n : ℕ := p.pred with hn
    have hn_succ : n.succ = p := by subst n; exact Nat.succ_pred_eq_of_pos hpos
    let g : ℕ → K := fun i => (αNat i : K) * ζ ^ i
    have hsum_split : ∑ i ∈ Finset.range n, g i + g n = 0 := by
      have hn1 : n + 1 = p := by simpa [Nat.succ_eq_add_one] using hn_succ
      have : ∑ i ∈ Finset.range (n + 1), g i = 0 := by simpa [g, hn1] using hsum_range
      simpa [Finset.sum_range_succ] using this
    -- Use the standard relation for primitive roots: `ζ^{p-1} = -∑_{i<p-1} ζ^i`.
    have hzpow : ζ ^ n = -∑ i ∈ Finset.range n, ζ ^ i := by
      subst n
      simpa using hζ.pow_sub_one_eq hone_lt
    -- Derive a vanishing relation with coefficients `αᵢ - α_{p-1}` and exponents `< n`.
    have hrel : ∑ i ∈ Finset.range n, ((αNat i - αNat n) : K) * ζ ^ i = 0 := by
      have h1 : ∑ i ∈ Finset.range n, g i + (αNat n : K) * ζ ^ n = 0 := by
        simpa [g] using hsum_split
      have h2 : ∑ i ∈ Finset.range n, g i - (αNat n : K) * ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
        simpa [hzpow, sub_eq_add_neg, mul_neg, g, mul_assoc, add_assoc] using h1
      simpa [g, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul] using h2
    -- Package the relation as a polynomial over ℚ.
    let q : ℚ[X] := ∑ i ∈ Finset.range n, Polynomial.monomial i (αNat i - αNat n)
    have hq_aeval : Polynomial.aeval ζ q = 0 := by
      have halg : ∀ x : ℚ, (algebraMap ℚ K) x = (x : K) := fun _ => rfl
      simp only [q, map_sum, Polynomial.aeval_monomial, halg, map_sub]
      convert hrel using 2 with i
      ring
    -- The cyclotomic polynomial is the minimal polynomial, so it divides `q`.
    have hmin : Polynomial.cyclotomic p ℚ = minpoly ℚ ζ :=
      Polynomial.cyclotomic_eq_minpoly_rat hζ hpos
    have hdvd : Polynomial.cyclotomic p ℚ ∣ q := by
      have : minpoly ℚ ζ ∣ q := minpoly.dvd ℚ ζ hq_aeval
      simpa [hmin] using this
    -- The polynomial `q` has degree `< p - 1`, while `cyclotomic p` has degree `p - 1`.
    have hn_pos : 0 < n := by
      subst n
      have : 0 < p - 1 := Nat.sub_pos_of_lt hone_lt
      simpa [Nat.pred_eq_sub_one] using this
    have hq_natDegree_le : q.natDegree ≤ n - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range n)
        (f := fun i => Polynomial.monomial i (αNat i - αNat n)) fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have hi_le : i ≤ n - 1 := Nat.le_pred_of_lt hi'
      exact (Polynomial.natDegree_monomial_le (a := αNat i - αNat n) (m := i)).trans hi_le
    have hcycl_natDegree : (Polynomial.cyclotomic p ℚ).natDegree = n := by
      subst n
      simp [Polynomial.natDegree_cyclotomic, Nat.totient_prime hprime]
    -- Hence `q = 0`.
    have hq0 : q = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd <| by
      rw [hcycl_natDegree]
      exact lt_of_le_of_lt hq_natDegree_le (Nat.sub_lt hn_pos Nat.one_pos)
    -- Extract coefficient equalities: for every `i < n`, `αNat i = αNat n`.
    have hαNat_eq (i : ℕ) (hi : i < n) : αNat i = αNat n := by
      have hcoeff : q.coeff i = αNat i - αNat n := by
        simp only [q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji])
            (fun h => (h (Finset.mem_range.mpr hi)).elim)]
        simp
      simp only [hq0, Polynomial.coeff_zero] at hcoeff
      linarith
    -- Translate back to `Fin p`: all coefficients equal α at position n.
    have hlast : n < p := by simp only [hn_succ.symm, Nat.lt_succ_self]
    suffices ∀ i : Fin p, α i = αNat n by exact fun i j => (this i).trans (this j).symm
    intro i
    have hi_le : i.val ≤ n := by
      have : i.val < n.succ := hn_succ.symm ▸ i.isLt
      exact Nat.lt_succ_iff.mp this
    rcases hi_le.lt_or_eq with hi_lt | hi_eq
    · exact (hαNat_val i).symm.trans (hαNat_eq i.val hi_lt)
    · have : i = ⟨n, hlast⟩ := Fin.ext hi_eq
      rw [this, ← hαNat_val ⟨n, hlast⟩]
  -- Reverse direction: equal coefficients implies vanishing
  · intro heq
    have hprime : Nat.Prime p := Fact.out
    have hone_lt : 1 < p := hprime.one_lt
    have hconst : ∀ i : Fin p, α i = α 0 := fun i => heq i 0
    calc ∑ i : Fin p, (α i : K) * ζ ^ i.val
        = ∑ i : Fin p, (α 0 : K) * ζ ^ i.val := by congr 1; ext i; rw [hconst i]
      _ = (α 0 : K) * ∑ i : Fin p, ζ ^ i.val := by rw [Finset.mul_sum]
      _ = (α 0 : K) * ∑ i ∈ Finset.range p, ζ ^ i := by
          congr 1; rw [← Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) p]
      _ = (α 0 : K) * 0 := by rw [hζ.geom_sum_eq_zero hone_lt]
      _ = 0 := mul_zero _

/-- Variant of `sum_eq_zero_iff_eq_coeff` with integer coefficients. -/
theorem sum_eq_zero_iff_eq_coeff' (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℤ) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ ∀ i j, α i = α j :=
  ⟨fun hsum i j ↦ by simpa using (sum_eq_zero_iff_eq_coeff hζ (α ·)).mp (by simpa using hsum) i j,
    fun heq ↦ by simpa using (sum_eq_zero_iff_eq_coeff hζ (α ·)).mpr (by simpa using heq)⟩

end IsPrimitiveRoot
