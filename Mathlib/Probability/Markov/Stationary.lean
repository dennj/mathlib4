/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Stationary Distributions for Stochastic Matrices

This file proves that every row-stochastic matrix on a finite nonempty state space has a
stationary distribution in the standard simplex.

## Main definitions

* `IsStationary`: A distribution `μ` is stationary for a matrix `P` if `μ ᵥ* P = μ`.
* `cesaroAverage`: The Cesàro average of the iterates of a vector under a matrix.
* `uniformDistribution`: The uniform distribution on a finite nonempty type.

## Main results

* `Matrix.rowStochastic.exists_stationary_distribution`: Every row-stochastic matrix on a finite
  nonempty state space has a stationary distribution in the standard simplex.

## Proof outline

The existence proof uses the Cesàro averaging technique:
1. Start with the uniform distribution `x₀`
2. Form Cesàro averages `xₖ = (1/(k+1)) ∑ᵢ x₀ ᵥ* Pⁱ`
3. By compactness of the simplex, extract a convergent subsequence `xₖₙ → μ`
4. Show `μ` is stationary using the L¹ non-expansiveness of stochastic matrices

## Tags

stochastic matrix, Markov chain, stationary distribution, Cesàro average
-/

@[expose] public section

open Finset Function Matrix ENNReal Filter
open scoped BigOperators

variable {R n : Type*} [Fintype n] [DecidableEq n]

/-! ### Stationary distributions -/

section Stationary

variable {R : Type*} [Semiring R]

/-- A distribution `μ` is stationary for a matrix `P` if `μ ᵥ* P = μ`. -/
class IsStationary (μ : n → R) (P : Matrix n n R) : Prop where
  stationary : μ ᵥ* P = μ

/-- Powers of a matrix preserve stationary distributions. -/
lemma IsStationary.pow (μ : n → R) (P : Matrix n n R) [IsStationary μ P] (k : ℕ) :
    IsStationary μ (P ^ k) :=
  ⟨by induction k with
      | zero => simp [Matrix.vecMul_one]
      | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, IsStationary.stationary]⟩

end Stationary

/-! ### Cesàro averages -/

section CesaroAverage

variable {R : Type*} [DivisionRing R] [PartialOrder R] [IsStrictOrderedRing R]

/-- The Cesàro average of the iterates of a vector under a matrix. -/
def cesaroAverage (x₀ : n → R) (P : Matrix n n R) (k : ℕ) : n → R :=
  (k + 1 : R)⁻¹ • ∑ i ∈ Finset.range (k + 1), x₀ ᵥ* (P ^ i)

variable [Nonempty n]

/-- The uniform distribution on a finite nonempty type. -/
@[reducible, nolint unusedArguments]
def uniformDistribution (R : Type*) (n : Type*) [Fintype n] [DivisionRing R] :
    n → R := fun _ => 1 / Fintype.card n

end CesaroAverage

/-! ### L¹ non-expansiveness for row-stochastic matrices -/

section L1Norm

variable {M : Matrix n n ℝ}

omit [DecidableEq n] in
/-- The L¹ norm of a function equals the sum of absolute values. -/
private lemma l1_nnnorm_eq_sum (f : PiLp 1 (fun _ : n => ℝ)) : (‖f‖₊ : ℝ) = ∑ i, |f.ofLp i| := by
  rw [PiLp.nnnorm_eq_sum one_ne_top]
  simp only [ENNReal.toReal_one, NNReal.rpow_one, div_one, NNReal.coe_sum, coe_nnnorm,
    Real.norm_eq_abs]

omit [DecidableEq n] in
/-- The L¹ norm of a probability vector is 1. -/
private lemma l1_nnnorm_eq_one {x : n → ℝ} (hx : x ∈ stdSimplex ℝ n) : ‖WithLp.toLp 1 x‖₊ = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, l1_nnnorm_eq_sum,
    (sum_congr rfl fun i _ => abs_of_nonneg (hx.1 i) : ∑ i, |x i| = ∑ i, x i), hx.2]

namespace Matrix.rowStochastic

/-- Powers of row-stochastic matrices are row-stochastic. -/
theorem pow_mem (hM : M ∈ rowStochastic ℝ n) (k : ℕ) : M ^ k ∈ rowStochastic ℝ n :=
  Submonoid.pow_mem (rowStochastic ℝ n) hM k

/-- Row-stochastic matrices are non-expansive operators on probability vectors in the L¹ norm.
This is the key contraction property for Markov chains. -/
theorem nnnorm_vecMul_sub_le (hM : M ∈ rowStochastic ℝ n) (x y : n → ℝ) :
    ‖WithLp.toLp 1 (x ᵥ* M - y ᵥ* M)‖₊ ≤ ‖WithLp.toLp 1 (x - y)‖₊ := by
  have hxy : x ᵥ* M - y ᵥ* M = fun j => ∑ i, (x i - y i) * M i j := by
    ext j; simp only [Pi.sub_apply, vecMul, dotProduct, sub_mul, sum_sub_distrib]
  have key : ∑ j, |∑ i, (x i - y i) * M i j| ≤ ∑ i, |x i - y i| := calc
    ∑ j, |∑ i, (x i - y i) * M i j|
      ≤ ∑ j, ∑ i, |x i - y i| * M i j := sum_le_sum fun j _ => (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i _ => by rw [abs_mul, abs_of_nonneg (hM.1 i j)])
    _ = ∑ i, |x i - y i| := by
        rw [sum_comm]; simp_rw [← mul_sum, sum_row_of_mem_rowStochastic hM, mul_one]
  have hnorm : (‖WithLp.toLp 1 (x ᵥ* M - y ᵥ* M)‖₊ : ℝ) = ∑ j, |∑ i, (x i - y i) * M i j| := by
    rw [l1_nnnorm_eq_sum]; exact sum_congr rfl fun j _ => congrArg abs (congrFun hxy j)
  exact NNReal.coe_le_coe.mp (by rw [hnorm, l1_nnnorm_eq_sum]; exact key)

/-- Row-stochastic matrices are non-expansive in L¹ norm (version with norm instead of nnnorm). -/
theorem norm_vecMul_sub_le (hM : M ∈ rowStochastic ℝ n) (x y : n → ℝ) :
    ‖WithLp.toLp 1 (x ᵥ* M - y ᵥ* M)‖ ≤ ‖WithLp.toLp 1 (x - y)‖ :=
  mod_cast nnnorm_vecMul_sub_le hM x y

end Matrix.rowStochastic

end L1Norm

/-! ### Existence of stationary distributions -/

section Existence

variable {M : Matrix n n ℝ}

/-- The Cesàro average of a probability vector under a row-stochastic matrix
belongs to the standard simplex. -/
lemma cesaroAverage_mem_stdSimplex (hM : M ∈ Matrix.rowStochastic ℝ n)
    {x₀ : n → ℝ} (hx₀ : x₀ ∈ stdSimplex ℝ n) (k : ℕ) :
    cesaroAverage x₀ M k ∈ stdSimplex ℝ n := by
  have hmem i : x₀ ᵥ* M ^ i ∈ stdSimplex ℝ n :=
    vecMul_mem_stdSimplex (Matrix.rowStochastic.pow_mem hM i) hx₀
  refine ⟨fun j => mul_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ k + 1))
    (by simp only [Finset.sum_apply]; exact sum_nonneg fun i _ => (hmem i).1 j), ?_⟩
  simp only [cesaroAverage, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ← mul_sum,
    sum_comm (γ := n)]
  rw [show ∑ i ∈ range (k + 1), ∑ j, (x₀ ᵥ* M ^ i) j = k + 1 from
    (sum_congr rfl fun i _ => (hmem i).2).trans (by simp), mul_comm]
  exact mul_inv_cancel₀ (by linarith : (k : ℝ) + 1 ≠ 0)

/-- The Cesàro average is almost invariant: applying the matrix changes it by at most `2/(k+1)`. -/
lemma norm_cesaroAverage_vecMul_sub_le (hM : M ∈ Matrix.rowStochastic ℝ n)
    {x₀ : n → ℝ} (hx₀ : x₀ ∈ stdSimplex ℝ n) (k : ℕ) :
    ‖WithLp.toLp 1 (cesaroAverage x₀ M k ᵥ* M - cesaroAverage x₀ M k)‖ ≤ 2 / (k + 1) := by
  have hk : (0 : ℝ) < k + 1 := by linarith
  have hsimp : cesaroAverage x₀ M k ᵥ* M - cesaroAverage x₀ M k =
      (k + 1 : ℝ)⁻¹ • (x₀ ᵥ* M ^ (k + 1) - x₀) := by
    unfold cesaroAverage
    rw [Matrix.smul_vecMul, ← smul_sub, Matrix.sum_vecMul]; congr 1
    have h1 : ∀ i, (x₀ ᵥ* M ^ i) ᵥ* M = x₀ ᵥ* M ^ (i + 1) := fun i => by
      rw [Matrix.vecMul_vecMul, ← pow_succ]
    simp_rw [h1]
    rw [Finset.sum_range_succ' (fun i => x₀ ᵥ* M ^ i), Finset.sum_range_succ, pow_zero,
      Matrix.vecMul_one]; abel
  rw [hsimp, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
  have h1 := vecMul_mem_stdSimplex (Matrix.rowStochastic.pow_mem hM (k + 1)) hx₀
  have : ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1) - x₀)‖ ≤ 2 := calc
    ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1) - x₀)‖₊
    _ = ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1)) - WithLp.toLp 1 x₀‖₊ := by rw [← WithLp.toLp_sub]
    _ ≤ ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1))‖₊ + ‖WithLp.toLp 1 x₀‖₊ := nnnorm_sub_le _ _
    _ = 2 := by rw [l1_nnnorm_eq_one h1, l1_nnnorm_eq_one hx₀]; norm_num
  calc (k + 1 : ℝ)⁻¹ * ‖WithLp.toLp 1 (x₀ ᵥ* M ^ (k + 1) - x₀)‖
    _ ≤ (k + 1 : ℝ)⁻¹ * 2 := by gcongr
    _ = 2 / (k + 1) := by ring

variable [Nonempty n]

omit [DecidableEq n] in
/-- The uniform distribution belongs to the standard simplex. -/
lemma uniformDistribution_mem_stdSimplex : uniformDistribution ℝ (n := n) ∈ stdSimplex ℝ n :=
  ⟨fun _ => by simp only [uniformDistribution, one_div, inv_nonneg]; positivity,
   by simp [uniformDistribution, Finset.card_univ, nsmul_eq_mul]⟩

namespace Matrix.rowStochastic

/-- Every row-stochastic matrix on a finite nonempty state space has a stationary distribution. -/
theorem exists_stationary_distribution (hM : M ∈ rowStochastic ℝ n) :
    ∃ μ : n → ℝ, μ ∈ stdSimplex ℝ n ∧ IsStationary μ M := by
  let x₀ := uniformDistribution ℝ (n := n)
  let xₖ : ℕ → n → ℝ := fun k => cesaroAverage x₀ M k
  have hxₖ k : xₖ k ∈ stdSimplex ℝ n :=
    cesaroAverage_mem_stdSimplex hM uniformDistribution_mem_stdSimplex k
  obtain ⟨μ, hμ_mem, nₖ, hnₖ_mono, hnₖ_lim⟩ := (isCompact_stdSimplex n).tendsto_subseq hxₖ
  refine ⟨μ, hμ_mem, ⟨?_⟩⟩
  have h_lim_diff : Tendsto (fun k => xₖ (nₖ k) ᵥ* M - xₖ (nₖ k)) atTop (nhds (μ ᵥ* M - μ)) :=
    ((Continuous.matrix_vecMul continuous_id continuous_const).continuousAt.tendsto.comp
      hnₖ_lim).sub hnₖ_lim
  have h_error_tendsto : Tendsto (fun k => ‖WithLp.toLp 1 (xₖ (nₖ k) ᵥ* M - xₖ (nₖ k))‖)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_const_nhds.div_atTop tendsto_id).comp
        ((tendsto_natCast_atTop_atTop.comp hnₖ_mono.tendsto_atTop).atTop_add tendsto_const_nhds))
      (fun _ => norm_nonneg _)
      (fun k => norm_cesaroAverage_vecMul_sub_le hM uniformDistribution_mem_stdSimplex (nₖ k))
  have h_norm_zero := tendsto_nhds_unique
    (((PiLp.continuous_toLp 1 (fun _ => ℝ)).continuousAt.tendsto.comp h_lim_diff).norm)
    h_error_tendsto
  exact sub_eq_zero.mp ((WithLp.toLp_injective 1).eq_iff.mp (norm_eq_zero.mp h_norm_zero))

end Matrix.rowStochastic

end Existence
