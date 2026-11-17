import GptLean.SymmetricLift.FullMetric
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Normalize

/-!
The tensor-lift pair bound for smooth approximants taking values in the
closed unit ball. Only static tensor multilinearity is added as background.
No regularity, approximation, or derivative estimate for the lift is assumed.

Normalization is used algebraically at a fixed configuration. The normalized
one-particle map need not be continuous. In particular this argument does not
require smooth approximation by unit-valued maps.
-/

noncomputable section
namespace GptLean.SymmetricLift

open Filter Topology MeasureTheory TopologicalSpace
open scoped BigOperators

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- The usual continuous multilinear realization of a finite pure tensor.
These fields concern fixed tensor spaces only. -/
structure TensorMultilinearData (B : TensorBackground V) where
  pureMap : ∀ n, ContinuousMultilinearMap ℂ (fun _ : Fin n => V) (B.H n)
  pure_eq : ∀ n u, pureMap n u = B.pure n u

namespace TensorMultilinearData

variable {B : TensorBackground V} (M : TensorMultilinearData B)
include M

theorem pure_real_smul (n : ℕ) (c : Fin n → ℝ) (u : Fin n → V) :
    B.pure n (fun i => c i • u i) = (∏ i, c i) • B.pure n u := by
  simpa only [ContinuousMultilinearMap.coe_restrictScalars, M.pure_eq] using
    ((M.pureMap n).restrictScalars ℝ).map_smul_univ c u

theorem pure_zero_of_factor_zero {n : ℕ} (u : Fin n → V) (i : Fin n)
    (hi : u i = 0) : B.pure n u = 0 := by
  rw [← M.pure_eq]
  exact (M.pureMap n).map_coord_zero i hi

/-- The full pure-tensor norm identity follows from multilinearity and the
existing unit-tensor norm law, including tuples with a zero factor. -/
theorem pure_norm (n : ℕ) (u : Fin n → V) : ‖B.pure n u‖ = ∏ i, ‖u i‖ := by
  classical
  by_cases hz : ∃ i, u i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [M.pure_zero_of_factor_zero u i hi, norm_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  · have hne : ∀ i, u i ≠ 0 := by simpa only [not_exists] using hz
    have hs : ∀ i, ‖NormedSpace.normalize (u i)‖ = 1 :=
      fun i => NormedSpace.norm_normalize (hne i)
    have he := M.pure_real_smul n (fun i => ‖u i‖)
      (fun i => NormedSpace.normalize (u i))
    simp only [NormedSpace.norm_smul_normalize] at he
    rw [he, norm_smul, B.pure_unit n _ hs, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg (u i))]

theorem pure_norm_le_one {n : ℕ} (u : Fin n → V) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖B.pure n u‖ ≤ 1 := by
  rw [M.pure_norm]
  exact Finset.prod_le_one (fun i _ => norm_nonneg (u i)) (fun i _ => hu i)

theorem pure_continuous (n : ℕ) : Continuous (B.pure n) := by
  have h := (M.pureMap n).cont
  change Continuous (fun u => (M.pureMap n) u) at h
  simpa only [M.pure_eq] using h

/-- Convergence in each one-particle factor gives convergence of the tensor. -/
theorem configurationTensor_tendsto {ι : Type*} {l : Filter ι} {n : ℕ}
    {t : ι → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (x : Configuration n)
    (ht : ∀ i, Tendsto (fun k => t k (particle x i)) l (𝓝 (t₀ (particle x i)))) :
    Tendsto (fun k => configurationTensor B (t k) x) l (𝓝 (configurationTensor B t₀ x)) :=
  ((M.pure_continuous n).tendsto _).comp (tendsto_pi_nhds.2 ht)

/-- The almost-everywhere form requires convergence at all particle positions
of almost every configuration. Pulling one-particle null sets back to
configuration space is a separate measure-theoretic step. -/
theorem ae_configurationTensor_tendsto {ι : Type*} {l : Filter ι} {n : ℕ}
    {μ : Measure (Configuration n)}
    {t : ι → EuclideanSpace ℝ (Fin 3) → V} {t₀ : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ᵐ x ∂μ, ∀ i,
      Tendsto (fun k => t k (particle x i)) l (𝓝 (t₀ (particle x i)))) :
    ∀ᵐ x ∂μ, Tendsto (fun k => configurationTensor B (t k) x) l
      (𝓝 (configurationTensor B t₀ x)) :=
  ht.mono fun x hx => M.configurationTensor_tendsto x hx

end TensorMultilinearData

/-- Homogeneity of the metric in the tensor argument. -/
theorem operatorCoordinateMetric_real_smul {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {n : ℕ} (U : Configuration n → H →L[ℂ] K)
    (x : Configuration n) (u : H) (a : ℝ) :
    operatorCoordinateMetric U x (a • u) = a ^ 2 * operatorCoordinateMetric U x u := by
  unfold operatorCoordinateMetric
  simp only [ContinuousLinearMap.map_smul_of_tower, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]

/-- The proved pair bound applies to closed-unit-ball inputs. Smooth
mollifications can therefore be used without normalizing them smoothly. -/
theorem recursiveLiftCandidate_pair_bound_of_norm_le_one
    (B : TensorBackground V) (M : TensorMultilinearData B) (n : ℕ)
    {x : Configuration n} (hx : x ∈ distinctConfigurations n)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ ≤ 1) :
    operatorCoordinateMetric (recursiveLiftCandidate B n).operator x
      (configurationTensor B t x) ≤ liftMetricConstant n * pairEnergy x := by
  classical
  by_cases hn : n ≤ 1
  · rw [recursiveLiftCandidate_eq, ite_eq_left hn, identityLiftCandidate_coordinate_metric]
    exact mul_nonneg (recursiveLiftCandidate_metric_properties B n).nonneg (pairEnergy_nonneg x)
  · by_cases hz : ∃ i : Fin n, t (particle x i) = 0
    · obtain ⟨i, hi⟩ := hz
      have he : configurationTensor B t x = 0 := M.pure_zero_of_factor_zero _ i hi
      rw [he]
      simp only [operatorCoordinateMetric, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero]
      exact mul_nonneg (recursiveLiftCandidate_metric_properties B n).nonneg (pairEnergy_nonneg x)
    · have hne : ∀ i : Fin n, t (particle x i) ≠ 0 := by simpa only [not_exists] using hz
      let i₀ : Fin n := ⟨0, by omega⟩
      let v := NormedSpace.normalize (t (particle x i₀))
      have hv : ‖v‖ = 1 := NormedSpace.norm_normalize (hne i₀)
      let s : EuclideanSpace ℝ (Fin 3) → V :=
        fun y => if t y = 0 then v else NormedSpace.normalize (t y)
      have hs : ∀ y, ‖s y‖ = 1 := by
        intro y
        by_cases hy : t y = 0
        · simpa [s, hy] using hv
        · simp [s, hy, NormedSpace.norm_normalize hy]
      let a : ℝ := ∏ i : Fin n, ‖t (particle x i)‖
      have ha0 : 0 ≤ a := Finset.prod_nonneg fun i _ => norm_nonneg _
      have ha1 : a ≤ 1 :=
        Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ht _)
      have he : configurationTensor B t x = a • configurationTensor B s x := by
        have h := M.pure_real_smul n (fun i => ‖t (particle x i)‖)
          (fun i => s (particle x i))
        simpa only [configurationTensor, a, s, ite_eq_right (hne _),
          NormedSpace.norm_smul_normalize] using h
      rw [he, operatorCoordinateMetric_real_smul]
      have hbound := (recursiveLiftCandidate_metric_properties B n).pair x hx s hs
      have hmetric := operatorCoordinateMetric_nonneg
        (recursiveLiftCandidate B n).operator x (configurationTensor B s x)
      have ha2 : a ^ 2 ≤ 1 := by nlinarith
      exact (mul_le_of_le_one_left hmetric ha2).trans hbound

end GptLean.SymmetricLift
