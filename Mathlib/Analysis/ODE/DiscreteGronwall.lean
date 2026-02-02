/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Discrete Grönwall Inequality

This file provides various forms of the discrete Grönwall inequality, which bounds
solutions to recurrence inequalities of the form `u(n+1) ≤ c(n) * u(n) + b(n)` or
the variant `u(n+1) ≤ (1 + c(n)) * u(n) + b(n)`.

## Main results

* `discrete_gronwall_prod_general`: Product form for `u(n+1) ≤ c(n) * u(n) + b(n)`.
  Works over any linearly ordered commutative ring.
* `discrete_gronwall`: Classical exponential bound for the `(1 + c)` form (ℝ-specific).
* `discrete_gronwall_Ico`: Uniform bound over an interval (ℝ-specific).

## References

* Grönwall, T. H. (1919). "Note on the derivatives with respect to a parameter of the
  solutions of a system of differential equations". *Annals of Mathematics*, 20(4), 292–296.

## See also

* `Mathlib.Analysis.ODE.Gronwall` for the continuous Grönwall inequality for ODEs.
-/

@[expose] public section

open Real Finset

section General

/-! ### Generalized product form

These theorems work over any linearly ordered commutative ring, using the unbundled
typeclasses `[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]`. -/

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {u b c : ℕ → R}

/-- Discrete Grönwall inequality: product form (generalized).

Given a recurrence `u(n+1) ≤ c(n) * u(n) + b(n)` with `c(n) ≥ 1`, we have
`u(n) ≤ u(n₀) * ∏ c(i) + ∑ b(k) * ∏ c(i)` where products are over appropriate ranges. -/
theorem discrete_gronwall_prod_general
    {n₀ : ℕ}
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ c n * u n + b n)
    (hc : ∀ n ≥ n₀, 1 ≤ c n) :
    ∀ n, n₀ ≤ n → u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, c i +
      ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, c i := by
  intro n hn
  refine Nat.le_induction ?base ?succ n hn
  case base => simp
  case succ =>
    intro k hk ih
    have hck_nonneg : 0 ≤ c k := le_trans zero_le_one (hc k (by omega))
    calc u (k + 1)
      _ ≤ c k * u k + b k := hu k (by omega)
      _ ≤ c k * (u n₀ * ∏ i ∈ Ico n₀ k, c i +
            ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ((∏ i ∈ Ico n₀ k, c i) * c k) +
            (c k * ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i + b k) := by ring
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            (c k * ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i + b k) := by
          rw [prod_Ico_mul_eq_prod_Ico_add_one (by omega)]
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            (∑ j ∈ Ico n₀ k, b j * ((∏ i ∈ Ico (j + 1) k, c i) * c k) + b k) := by
          rw [mul_sum]; congr 1; congr 1; apply sum_congr rfl; intro j _; ring
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            (∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) (k + 1), c i + b k) := by
          congr 2; apply sum_congr rfl; intro j hj
          simp only [mem_Ico] at hj; rw [prod_Ico_mul_eq_prod_Ico_add_one (by omega)]
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            ∑ j ∈ Ico n₀ (k + 1), b j * ∏ i ∈ Ico (j + 1) (k + 1), c i := by
          rw [← sum_Ico_add_eq_sum_Ico_add_one]
          · simp
          · omega

/-- The product over a suffix `Ico (k+1) n` is bounded by the product over `Ico n₀ n`. -/
lemma prod_one_add_Ico_mono
    {n₀ n : ℕ}
    (hc : ∀ i ≥ n₀, 0 ≤ c i) :
    ∀ k ∈ Ico n₀ n, ∏ i ∈ Ico (k + 1) n, (1 + c i) ≤ ∏ i ∈ Ico n₀ n, (1 + c i) := by
  intro k hk
  simp only [mem_Ico] at hk
  have h1 : (1 : R) ≤ ∏ i ∈ Ico n₀ (k + 1), (1 + c i) := by
    calc (1 : R) = ∏ _ ∈ Ico n₀ (k + 1), (1 : R) := by simp
      _ ≤ ∏ i ∈ Ico n₀ (k + 1), (1 + c i) :=
          prod_le_prod (fun _ _ ↦ zero_le_one) fun i hi ↦ by
            simp only [mem_Ico] at hi; linarith [hc i (by omega)]
  have hprod_nonneg : 0 ≤ ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
    prod_nonneg fun i hi ↦ by simp only [mem_Ico] at hi; linarith [hc i (by omega)]
  calc ∏ i ∈ Ico (k + 1) n, (1 + c i)
      _ ≤ (∏ i ∈ Ico n₀ (k + 1), (1 + c i)) * ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
          le_mul_of_one_le_left hprod_nonneg h1
      _ = ∏ i ∈ Ico n₀ n, (1 + c i) := prod_Ico_consecutive _ (by omega) (by omega)

end General

/-! ### Real-valued theorems

The following theorems are specific to `ℝ` and use exponential bounds.
For the product form without exponentials, use `discrete_gronwall_prod_general`
which works over any linearly ordered commutative ring. -/

variable {u b c : ℕ → ℝ}

/-- Discrete Grönwall inequality: classical exponential form.

For a recurrence `u(n+1) ≤ (1 + c(n)) * u(n) + b(n)` with non-negative `b`, `c`, and `u(n₀)`,
we have `u(n) ≤ (u(n₀) + ∑ b(k)) * exp(∑ c(i))`. -/
theorem discrete_gronwall
    {n₀ : ℕ}
    (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
    (hc : ∀ n ≥ n₀, 0 ≤ c n)
    (hb : ∀ n ≥ n₀, 0 ≤ b n) :
    ∀ n, n₀ ≤ n →
      u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
  intro n hn
  have hprod_le_exp : ∏ i ∈ Ico n₀ n, (1 + c i) ≤ exp (∑ i ∈ Ico n₀ n, c i) :=
    calc ∏ i ∈ Ico n₀ n, (1 + c i)
        _ ≤ ∏ i ∈ Ico n₀ n, exp (c i) := prod_le_prod
            (fun i hi ↦ by simp only [mem_Ico] at hi; linarith [hc i (by omega)])
            (fun i _ ↦ by rw [add_comm]; exact add_one_le_exp (c i))
        _ = exp (∑ i ∈ Ico n₀ n, c i) := (exp_sum ..).symm
  calc u n
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (fun m hm => by linarith [hc m hm]) n hn
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico n₀ n, (1 + c i) := by
        gcongr with j hj
        · simp only [mem_Ico] at hj; exact hb j (by omega)
        · exact prod_one_add_Ico_mono hc j hj
    _ = (u n₀ + ∑ k ∈ Ico n₀ n, b k) * ∏ i ∈ Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) :=
        mul_le_mul_of_nonneg_left hprod_le_exp (add_nonneg hun₀
          (sum_nonneg fun i hi ↦ by simp only [mem_Ico] at hi; exact hb i (by omega)))

/-- Discrete Grönwall inequality: uniform bound over an interval.

Provides a uniform bound for all `n ∈ [n₀, n₁)`. -/
theorem discrete_gronwall_Ico
    {n₀ n₁ : ℕ}
    (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
    (hc : ∀ n ≥ n₀, 0 ≤ c n)
    (hb : ∀ n ≥ n₀, 0 ≤ b n) :
    ∀ n ∈ Ico n₀ n₁,
      u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
  intro n hn
  simp only [mem_Ico] at hn
  have hsum_b : ∑ k ∈ Ico n₀ n, b k ≤ ∑ k ∈ Ico n₀ n₁, b k :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
      fun i hi _ ↦ by simp only [mem_Ico] at hi; exact hb i (by omega)
  have hsum_c : ∑ i ∈ Ico n₀ n, c i ≤ ∑ i ∈ Ico n₀ n₁, c i :=
    sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
      fun i hi _ ↦ by simp only [mem_Ico] at hi; exact hc i (by omega)
  have hsum_b₁_nonneg : 0 ≤ ∑ k ∈ Ico n₀ n₁, b k :=
    sum_nonneg fun i hi ↦ by simp only [mem_Ico] at hi; exact hb i (by omega)
  calc u n
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) :=
        discrete_gronwall hun₀ hu hc hb n hn.1
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) :=
        mul_le_mul (by linarith) (exp_le_exp_of_le hsum_c) (by positivity)
          (add_nonneg hun₀ hsum_b₁_nonneg)
