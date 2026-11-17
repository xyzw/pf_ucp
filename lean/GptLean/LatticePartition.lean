import GptLean.LatticePartitionBound
import GptLean.ElectronicLocalizationMetric
import GptLean.Repair.MeasuredTagSobolev
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
The concrete three-dimensional lattice square partition used in exact
removal. The one-dimensional normalized bump is tensored in Cartesian
coordinates and rescaled by the positive localization length. Every
property required by the symmetric electronic localization follows from
this fixed construction, including its inverse-square derivative bound.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.LatticePartition

open Finset Metric
open GptLean.ElectronicLocalization
open scoped Topology ContDiff

abbrev Lattice := Fin 3 → ℤ
abbrev Position := EuclideanSpace ℝ (Fin 3)

/-- The derivative constant is selected once from the fixed unit-scale bump. -/
def oneDimensionalMetricConstant : ℝ := Classical.choose exists_metric_bound

theorem oneDimensionalMetricConstant_pos : 0 < oneDimensionalMetricConstant :=
  (Classical.choose_spec exists_metric_bound).1

theorem oneDimensionalMetricConstant_bound (x : ℝ) :
    (∑' z : ℤ, deriv (eta z) x ^ 2) ≤ oneDimensionalMetricConstant :=
  (Classical.choose_spec exists_metric_bound).2 x

def scaledEta (R : ℝ) (z : ℤ) (x : ℝ) : ℝ := eta z (x / R)

theorem scaledEta_nonneg (R : ℝ) (z : ℤ) (x : ℝ) : 0 ≤ scaledEta R z x :=
  eta_nonneg z (x / R)

theorem scaledEta_contDiff (R : ℝ) (z : ℤ) : ContDiff ℝ ∞ (scaledEta R z) :=
  (eta_contDiff z).comp (contDiff_id.div_const R)

theorem scaledEta_differentiable (R : ℝ) (z : ℤ) : Differentiable ℝ (scaledEta R z) :=
  (scaledEta_contDiff R z).differentiable (by simp)

theorem scaledEta_locallyFinite (R : ℝ) :
    LocallyFinite (fun z : ℤ => Function.support (scaledEta R z)) :=
  eta_locallyFinite.preimage_continuous (continuous_id.div_const R)

theorem scaledEta_hasSum_sq (R x : ℝ) :
    HasSum (fun z : ℤ => scaledEta R z x ^ 2) 1 := eta_hasSum_sq (x / R)

theorem scaledEta_deriv (R : ℝ) (z : ℤ) (x : ℝ) :
    deriv (scaledEta R z) x = deriv (eta z) (x / R) / R := by
  have h := (((eta_contDiff z).differentiable (by simp)) (x / R)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const R)
  change deriv (fun y => eta z (y / R)) x = _
  simpa only [Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using h.deriv

theorem scaledEta_metric_le (R : ℝ) (hR : 0 < R) (x : ℝ) :
    (∑' z : ℤ, deriv (scaledEta R z) x ^ 2) ≤ oneDimensionalMetricConstant / R ^ 2 := by
  simp_rw [scaledEta_deriv, div_pow]
  rw [tsum_div_const]
  exact div_le_div_of_nonneg_right (oneDimensionalMetricConstant_bound (x / R))
    (sq_pos_of_pos hR).le

/-- The lattice point at the same physical scale as the multiplier. -/
def centre (R : ℝ) (a : Lattice) : Position :=
  R • WithLp.toLp 2 (fun j => (a j : ℝ))

/-- The actual smooth, nonnegative three-dimensional multiplier. -/
def multiplier (R : ℝ) (a : Lattice) (x : Position) : ℝ :=
  tensorMultiplier (scaledEta R) a (WithLp.ofLp x)

theorem multiplier_nonneg (R : ℝ) (a : Lattice) (x : Position) :
    0 ≤ multiplier R a x :=
  tensorMultiplier_nonneg (scaledEta R) (scaledEta_nonneg R) a (WithLp.ofLp x)

theorem multiplier_contDiff (R : ℝ) (a : Lattice) : ContDiff ℝ ∞ (multiplier R a) := by
  change ContDiff ℝ ∞ (fun x : Position => ∏ j : Fin 3, scaledEta R (a j) (x j))
  apply contDiff_prod
  intro j _
  exact (scaledEta_contDiff R (a j)).comp (contDiff_piLp_apply 2)

theorem multiplier_differentiable (R : ℝ) (a : Lattice) :
    Differentiable ℝ (multiplier R a) :=
  (multiplier_contDiff R a).differentiable (by simp)

theorem multiplier_locallyFinite (R : ℝ) :
    LocallyFinite (fun a : Lattice => Function.support (multiplier R a)) :=
  (tensorMultiplier_locallyFinite (scaledEta R) (scaledEta_locallyFinite R)).preimage_continuous
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem multiplier_hasSum_sq (R : ℝ) (x : Position) :
    HasSum (fun a : Lattice => multiplier R a x ^ 2) 1 :=
  tensorMultiplier_hasSum_sq (scaledEta R) (scaledEta_locallyFinite R)
    (scaledEta_hasSum_sq R) (WithLp.ofLp x)

theorem multiplier_support (R : ℝ) (hR : 0 < R) (a : Lattice) (x : Position)
    (hx : multiplier R a x ≠ 0) : dist x (centre R a) < 4 * R := by
  have hp : (∏ j : Fin 3, eta (a j) (x j / R)) ≠ 0 := hx
  have hcoord (j : Fin 3) : |x j - R * (a j : ℝ)| < 2 * R := by
    have hj : eta (a j) (x j / R) ≠ 0 :=
      prod_ne_zero_iff.mp hp j (mem_univ j)
    have hb := eta_support (a j) (x j / R) hj
    have heq : x j - R * (a j : ℝ) = (x j / R - (a j : ℝ)) * R := by
      calc
        _ = x j - (a j : ℝ) * R := by ring
        _ = _ := by rw [sub_mul, div_mul_cancel₀ _ hR.ne']
    rw [heq, abs_mul, abs_of_pos hR]
    exact mul_lt_mul_of_pos_right hb hR
  have hsq (j : Fin 3) : (x j - R * (a j : ℝ)) ^ 2 ≤ (2 * R) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (x j - R * (a j : ℝ))) (by positivity)).2 (hcoord j).le
  have hnorm : ‖x - centre R a‖ ^ 2 ≤ 12 * R ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin 3, (2 * R) ^ 2 := by
        apply sum_le_sum
        intro j _
        simpa only [centre, PiLp.sub_apply, PiLp.smul_apply, PiLp.toLp_apply,
          smul_eq_mul] using hsq j
      _ = 12 * R ^ 2 := by norm_num; ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - centre R a), sq_pos_of_pos hR]

theorem multiplier_tsupport_subset_closedBall (R : ℝ) (hR : 0 < R) (a : Lattice) :
    tsupport (multiplier R a) ⊆ Metric.closedBall (centre R a) (4 * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  exact (multiplier_support R hR a x hx).le

theorem multiplier_tsupport_subset_ball (R : ℝ) (hR : 0 < R) (a : Lattice) :
    tsupport (multiplier R a) ⊆ Metric.ball (centre R a) (5 * R) := by
  intro x hx
  have h := multiplier_tsupport_subset_closedBall R hR a hx
  change dist x (centre R a) ≤ 4 * R at h
  change dist x (centre R a) < 5 * R
  linarith

theorem multiplier_hasCompactSupport (R : ℝ) (hR : 0 < R) (a : Lattice) :
    HasCompactSupport (multiplier R a) :=
  (isCompact_closedBall (centre R a) (4 * R)).of_isClosed_subset
    (isClosed_tsupport _) (multiplier_tsupport_subset_closedBall R hR a)

theorem multiplier_fderiv_coordinate (R : ℝ) (a : Lattice) (x : Position) (j : Fin 3) :
    fderiv ℝ (multiplier R a) x (EuclideanSpace.single j 1) =
      fderiv ℝ (tensorMultiplier (scaledEta R) a) (WithLp.ofLp x) (Pi.single j 1) := by
  have hd : Differentiable ℝ (tensorMultiplier (scaledEta R) a) := by
    simpa only [Equiv.coe_refl, Function.comp_id] using
      permutedTensor_differentiable (scaledEta R) (scaledEta_differentiable R) a
        (Equiv.refl (Fin 3))
  have h := (hd (WithLp.ofLp x)).hasFDerivAt.comp x
    (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 x)
  change fderiv ℝ (tensorMultiplier (scaledEta R) a ∘ WithLp.ofLp) x
    (EuclideanSpace.single j 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- Each spatial coordinate factors exactly into the one-dimensional metric. -/
theorem multiplier_coordinate_hasSum_sq (R : ℝ) (x : Position) (j : Fin 3) :
    HasSum (fun a : Lattice =>
      fderiv ℝ (multiplier R a) x (EuclideanSpace.single j 1) ^ 2)
      (∑' z : ℤ, deriv (scaledEta R z) (x j) ^ 2) := by
  simpa only [multiplier_fderiv_coordinate, fderiv_apply_one_eq_deriv] using
    tensorMultiplier_single_hasSum_sq (scaledEta R) (scaledEta_locallyFinite R)
      (scaledEta_differentiable R) (scaledEta_nonneg R) (scaledEta_hasSum_sq R)
      (WithLp.ofLp x) j (1 : ℝ)

/-- This fixed positive constant is independent of the scale and lattice point. -/
def metricConstant : ℝ := 3 * oneDimensionalMetricConstant

theorem metricConstant_pos : 0 < metricConstant :=
  mul_pos (by norm_num) oneDimensionalMetricConstant_pos

/-- The concrete one-electron derivative estimate used by exact removal. -/
theorem multiplier_metric_le (R : ℝ) (hR : 0 < R) (x : Position) :
    (∑ j : Fin 3, ∑' a : Lattice,
      fderiv ℝ (multiplier R a) x (EuclideanSpace.single j 1) ^ 2) ≤
      metricConstant / R ^ 2 := by
  calc
    _ = ∑ j : Fin 3, ∑' z : ℤ, deriv (scaledEta R z) (x j) ^ 2 := by
      apply sum_congr rfl
      intro j _
      exact (multiplier_coordinate_hasSum_sq R x j).tsum_eq
    _ ≤ ∑ _j : Fin 3, oneDimensionalMetricConstant / R ^ 2 :=
      sum_le_sum fun j _ => scaledEta_metric_le R hR (x j)
    _ = metricConstant / R ^ 2 := by simp [metricConstant, mul_div_assoc]

/-- Instantiation of the symmetric many-electron partition at the concrete lattice. -/
theorem symmetric_metric_le (R : ℝ) (hR : 0 < R) {N : ℕ}
    (X : Fin N → Position) :
    (∑ i : Fin N, ∑ j : Fin 3, ∑' α : Fin N → Lattice,
      fderiv ℝ (symmetricMultiplier (multiplier R) α) X
        (Pi.single i (EuclideanSpace.single j 1)) ^ 2) ≤
      N * metricConstant / R ^ 2 := by
  simpa only [mul_div_assoc] using symmetricMultiplier_total_metric_le (multiplier R)
    (fun j : Fin 3 => EuclideanSpace.single j 1) (multiplier_locallyFinite R)
    (multiplier_differentiable R) (multiplier_nonneg R) (multiplier_hasSum_sq R)
    (metricConstant / R ^ 2) (multiplier_metric_le R hR) X

theorem symmetric_spatial_support (R : ℝ) (hR : 0 < R) {N : ℕ}
    (α : Fin N → Lattice) (X : Fin N → Position)
    (hX : symmetricMultiplier (multiplier R) α X ≠ 0) :
    ∃ π : Equiv.Perm (Fin N), ∀ i, dist (X (π i)) (centre R (α i)) < 4 * R :=
  symmetricMultiplier_spatial_support (multiplier R) (centre R) (4 * R)
    (multiplier_support R hR) α X hX

/-- No independent one-electron partition assumption remains in the weak H1 bridge. -/
theorem symmetric_hasWeakH1Local (R : ℝ) (hR : 0 < R) {N : ℕ}
    (α : Fin N → Lattice) :
    GptLean.SymmetricLift.HasWeakH1Local
      (fun x : GptLean.SymmetricLift.Configuration N =>
        symmetricMultiplier (multiplier R) α (fun i => GptLean.SymmetricLift.particle x i))
      (fun q x => fderiv ℝ
        (fun y : GptLean.SymmetricLift.Configuration N =>
          symmetricMultiplier (multiplier R) α (fun i => GptLean.SymmetricLift.particle y i)) x
        (EuclideanSpace.single q 1)) :=
  GptLean.Repair.electronicLocalization_hasWeakH1Local (multiplier R)
    (multiplier_locallyFinite R) (multiplier_differentiable R) (multiplier_nonneg R)
    (multiplier_hasSum_sq R) (metricConstant / R ^ 2) (multiplier_metric_le R hR) α

end GptLean.LatticePartition
