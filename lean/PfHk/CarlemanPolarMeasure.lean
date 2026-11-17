import PfHk.LogPolarCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact logarithmic Jacobian and conformal factors in the Carleman
densities, followed by change of measure on the actual small ball. -/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory Set
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (I : Type*) [Fintype I] [DecidableEq I]

def conformalExponent : ℝ := ((Fintype.card I : ℝ)-2)/2

theorem logarithmicJacobian_eq_conformal (t : ℝ) :
    logarithmicJacobian I t = Real.exp (-conformalExponent I*t)^2 * Real.exp (-t)^2 := by
  unfold logarithmicJacobian conformalExponent
  simp only [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem source_factor (t : ℝ) :
    (2*Real.exp (-(conformalExponent I+2)*t))^2 =
      4*logarithmicJacobian I t*Real.exp (-t)^2 := by
  rw [mul_pow, show (2 : ℝ)^2=4 by norm_num, mul_assoc]
  congr 1
  unfold logarithmicJacobian
  simp only [pow_two, ← Real.exp_add]
  congr 1
  unfold conformalExponent
  ring

theorem density_factors (τ β t M D R : ℝ) :
    τ^3*β*(Real.exp (-conformalExponent I*t)^2*M) +
      τ*β*(Real.exp (-conformalExponent I*t)^2*Real.exp (-t)^2*D) +
      τ*Real.exp (-t)^2*(2*Real.exp (-conformalExponent I*t)^2*R) =
    logarithmicJacobian I t *
      (τ^3*β*(Real.exp (-t)^2)⁻¹*M + τ*β*D + 2*τ*R) := by
  rw [logarithmicJacobian_eq_conformal]
  have hr : Real.exp (-t) ≠ 0 := Real.exp_ne_zero _
  field_simp
  <;> ring

theorem integral_logPolar (P : StandardLogPolarCalculus I) (hd : 0 < Fintype.card I)
    (f : Position I → ℝ) (hf : Integrable f) :
    (∫ X, f X) = ∫ t : ℝ, ∫ θ : UnitSphere I,
      logarithmicJacobian I t * f (Real.exp (-t) • θ.val) ∂sphereMeasure I := by
  have hp := (P.integrable_change hd f).mp hf
  exact (P.integral_change hd f hf).trans (integral_prod _ hp)

theorem logarithmic_mem_ball (t₀ t : ℝ) (θ : UnitSphere I) :
    Real.exp (-t) • θ.val ∈ Metric.ball (0 : Position I) (Real.exp (-t₀)) ↔ t₀ < t := by
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), unitSphere_norm, mul_one, Real.exp_lt_exp]
  exact neg_lt_neg_iff

theorem integral_ball_logPolar (P : StandardLogPolarCalculus I) (hd : 0 < Fintype.card I)
    (t₀ : ℝ) (f : Position I → ℝ) (hf : IntegrableOn f (Metric.ball 0 (Real.exp (-t₀)))) :
    (∫ X in Metric.ball 0 (Real.exp (-t₀)), f X) =
      ∫ t in Ioi t₀, ∫ θ : UnitSphere I,
        logarithmicJacobian I t * f (Real.exp (-t) • θ.val) ∂sphereMeasure I := by
  let B := Metric.ball (0 : Position I) (Real.exp (-t₀))
  have hB : MeasurableSet B := measurableSet_ball
  have hif : Integrable (B.indicator f) := (integrable_indicator_iff hB).mpr hf
  have h := integral_logPolar I P hd (B.indicator f) hif
  rw [integral_indicator hB] at h
  calc
    _ = ∫ t : ℝ, ∫ θ : UnitSphere I,
        logarithmicJacobian I t * B.indicator f (Real.exp (-t) • θ.val) ∂sphereMeasure I := h
    _ = ∫ t : ℝ, (Ioi t₀).indicator (fun s => ∫ θ : UnitSphere I,
        logarithmicJacobian I s * f (Real.exp (-s) • θ.val) ∂sphereMeasure I) t := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      dsimp only
      by_cases ht : t₀ < t
      · rw [Set.indicator_of_mem (show t ∈ Ioi t₀ from ht)]
        apply integral_congr_ae
        exact ae_of_all _ fun θ => by
          dsimp only
          rw [Set.indicator_of_mem (show Real.exp (-t) • θ.val ∈ B from
            (logarithmic_mem_ball I t₀ t θ).mpr ht)]
      · rw [Set.indicator_of_notMem (show t ∉ Ioi t₀ from ht)]
        have hz : (fun θ : UnitSphere I =>
            logarithmicJacobian I t * B.indicator f (Real.exp (-t) • θ.val)) = 0 := by
          funext θ
          rw [Set.indicator_of_notMem (show Real.exp (-t) • θ.val ∉ B from
            fun hb => ht ((logarithmic_mem_ball I t₀ t θ).mp hb)), mul_zero]
          rfl
        rw [hz]
        change (∫ θ : UnitSphere I, (0 : ℝ) ∂sphereMeasure I) = 0
        exact integral_zero _ _
    _ = _ := integral_indicator measurableSet_Ioi

end PfHk.PolarCalculus
