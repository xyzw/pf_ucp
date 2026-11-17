import PfHk.CounterexampleField
import PfHk.PhysicalDiamagneticPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The counterexample potentials as actual elements of the article's
global potential spaces. The Coulomb singularity is split at unit radius. -/

noncomputable section
namespace PfHk.CounterexamplePotentials

open MeasureTheory Filter GptLean.PhysicalPairDuality
  GptLean.TransformationsPotentials PfHk.CounterexampleField
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 400000

theorem inverse_norm_memLp_ball {p : ℝ} (hp : 0 < p) (hp3 : p < 3)
    (o : Space) (r : ℝ) :
    MemLp (fun x : Space => ‖x‖⁻¹) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) := by
  have hm : AEStronglyMeasurable (fun x : Space => ‖x‖⁻¹) volume := by
    fun_prop
  apply (integrable_norm_rpow_iff hm.restrict (ENNReal.ofReal_ne_zero_iff.mpr hp) (by simp)).mp
  have hi : LocallyIntegrable (fun x : Space => ‖x‖ ^ (-p)) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := p)
      (by norm_num [Space, finrank_euclideanSpace]) ?_ ?_ ?_
    · simpa [Space, finrank_euclideanSpace] using hp3
    · exact ae_of_all _ fun x => by simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    · exact (measurable_norm.pow_const (-p)).aestronglyMeasurable
  have hib := (hi.integrableOn_isCompact (isCompact_closedBall o r)).mono_set
    Metric.ball_subset_closedBall
  simpa only [IntegrableOn, ENNReal.toReal_ofReal hp.le, norm_inv, norm_norm,
    Real.rpow_neg_eq_inv_rpow] using hib

private def coulombNear (Z : ℝ) : Space → ℝ :=
  (Metric.ball 0 1).indicator (fun x => -Z / ‖x‖)

private def coulombFar (Z : ℝ) : Space → ℝ :=
  (Metric.ball 0 1)ᶜ.indicator (fun x => -Z / ‖x‖)

private theorem coulombNear_memLp (Z : ℝ) : MemLp (coulombNear Z) (3 / 2) volume := by
  apply (memLp_indicator_iff_restrict measurableSet_ball).mpr
  have h := (inverse_norm_memLp_ball (p := 3 / 2) (by norm_num) (by norm_num) 0 1).const_mul (-Z)
  have hexp : ENNReal.ofReal ((3 : ℝ) / 2) = (3 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hexp] at h
  simpa only [div_eq_mul_inv] using h

private theorem coulombFar_memLp (Z : ℝ) : MemLp (coulombFar Z) ∞ volume := by
  apply memLp_top_of_bound
    ((measurable_const.div measurable_norm).indicator measurableSet_ball.compl).aestronglyMeasurable |Z|
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ (Metric.ball (0 : Space) 1)ᶜ
    · rw [Set.indicator_of_mem hx]
      change ‖-Z / ‖x‖‖ ≤ |Z|
      rw [norm_div, Real.norm_eq_abs, abs_neg, norm_norm]
      have hr : 1 ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_zero_right] using hx
      exact (div_le_self (abs_nonneg Z) hr)
    · simp [Set.indicator_of_notMem hx]

/-- The physical Coulomb scalar class. -/
def coulomb (Z : ℝ) : ScalarPotential :=
  ofParts ((coulombFar_memLp Z).toLp (coulombFar Z))
    ((coulombNear_memLp Z).toLp (coulombNear Z))

theorem coulomb_ae (Z : ℝ) :
    ((coulomb Z).val : Space → ℝ) =ᵐ[volume] fun x => -Z / ‖x‖ := by
  filter_upwards [coeFn_ofParts ((coulombFar_memLp Z).toLp (coulombFar Z))
      ((coulombNear_memLp Z).toLp (coulombNear Z)),
    (coulombFar_memLp Z).coeFn_toLp, (coulombNear_memLp Z).coeFn_toLp] with x hs hf hn
  change (coulomb Z).val x = _ at hs ⊢
  rw [hs, hf, hn]
  by_cases hx : x ∈ Metric.ball (0 : Space) 1 <;> simp [coulombFar, coulombNear, hx]

theorem vector_memLp_top (t : ℝ) : MemLp (vectorPotential t) ∞ volume :=
  field_memLp_top.const_smul t

/-- The physical bounded vector-potential class. -/
def vector (t : ℝ) : VectorPotential :=
  ofParts ((vector_memLp_top t).toLp (vectorPotential t)) 0

theorem vector_ae (t : ℝ) :
    ((vector t).val : Space → Space) =ᵐ[volume] vectorPotential t :=
  (coeFn_ofParts_zero ((vector_memLp_top t).toLp (vectorPotential t))).trans
    (vector_memLp_top t).coeFn_toLp

/-- The compensating scalar class in the counterexample. -/
def scalar (Z t : ℝ) : ScalarPotential :=
  coulomb Z - PhysicalDiamagneticPotential.halfSquare (vector t)

theorem scalar_ae (Z t : ℝ) :
    ((scalar Z t).val : Space → ℝ) =ᵐ[volume] scalarPotential Z t := by
  have hs : ((scalar Z t).val : Space → ℝ) =ᵐ[volume]
      fun x => (coulomb Z).val x - (PhysicalDiamagneticPotential.halfSquare (vector t)).val x :=
    AEEqFun.coeFn_sub _ _
  filter_upwards [hs, coulomb_ae Z, PhysicalDiamagneticPotential.coeFn_halfSquare (vector t),
    vector_ae t] with x hsub hZ hsq ht
  rw [hsub, hZ, hsq, ht]
  simp only [scalarPotential, vectorPotential, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

@[simp] theorem shifted_eq (Z t : ℝ) :
    PhysicalDiamagneticPotential.shifted (scalar Z t) (vector t) = (coulomb Z, vector t) := by
  simp [PhysicalDiamagneticPotential.shifted, scalar]

theorem coulomb_local_memLp {p : ℝ} (hp : 0 < p) (hp3 : p < 3)
    (Z : ℝ) (o : Space) (r : ℝ) :
    MemLp ((coulomb Z).val : Space → ℝ) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) := by
  apply ((inverse_norm_memLp_ball hp hp3 o r).const_mul (-Z)).ae_eq
  filter_upwards [ae_restrict_of_ae (coulomb_ae Z)] with x hx
  simpa only [div_eq_mul_inv] using hx.symm

end PfHk.CounterexamplePotentials
