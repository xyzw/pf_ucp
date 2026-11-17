import PfHk.UniqueContinuation

/-! The endpoint of the cutoff passage is a nonnegative integral bound.
This file performs exponential separation directly from that bound, so no
integrability of a singular weight is inserted as a premise. -/

noncomputable section
namespace PfHk.UniqueContinuation

open MeasureTheory Filter
open scoped ENNReal Topology

set_option maxHeartbeats 20000
set_option Elab.async false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X}

theorem radialMassIntegrand_measurable {ψ : X → H} {r : X → ℝ}
    (hψ : Measurable (fun x => ‖ψ x‖)) (hr : Measurable r) (α τ : ℝ) :
    Measurable (radialMassIntegrand r ψ α τ) := by
  unfold radialMassIntegrand weightedNormSq CarlemanWeights.beta CarlemanWeights.weight
  fun_prop

/-- A finite bound on the actual radial mass nonnegative integral gives
both the needed singular integrability and almost-everywhere vanishing. -/
theorem ae_zero_of_radial_lintegral_outer_error {ψ : X → H} {r : X → ℝ}
    {α inner outer C τ₀ : ℝ} (hα : 0 < α)
    (hinner : 0 < inner) (hio : inner < outer) (houter : outer ≤ Real.exp (-2))
    (hC : 0 ≤ C) (hr : ∀ᵐ x ∂μ, 0 < r x ∧ r x < inner)
    (hcoef : ∀ s, 0 < s → s ≤ inner →
      1 ≤ CarlemanWeights.beta α (-Real.log s) * s ^ (-2 : ℝ))
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hmeas : ∀ τ, max τ₀ 1 ≤ τ →
      AEStronglyMeasurable (radialMassIntegrand r ψ α τ) μ)
    (hbound : ∀ τ, max τ₀ 1 ≤ τ →
      (∫⁻ x, ENNReal.ofReal (radialMassIntegrand r ψ α τ x) ∂μ) ≤
        ENNReal.ofReal (C * Real.exp
          (2 * τ * CarlemanWeights.weight α (-Real.log outer)))) :
    ∀ᵐ x ∂μ, ψ x = 0 := by
  have hm : 0 ≤ ∫ x, ‖ψ x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hz : (∫ x, ‖ψ x‖ ^ 2 ∂μ) = 0 :=
    mass_eq_zero_of_exponential_separation hm
      (radial_weight_gap hα hinner hio houter) (by
        intro τ hτ
        have hτ0 : 0 ≤ τ := le_trans zero_le_one ((le_max_right _ _).trans hτ)
        have hpos : 0 ≤ᵐ[μ] radialMassIntegrand r ψ α τ := by
          filter_upwards [hr] with x hx
          have hw := (zero_le_one.trans (hcoef (r x) hx.1 hx.2.le))
          exact mul_nonneg (pow_nonneg hτ0 3)
            (mul_nonneg (mul_nonneg hw (Real.exp_pos _).le) (sq_nonneg _))
        obtain ⟨hint, hupper⟩ := integrable_and_integral_le_of_lintegral_bound
          (hmeas τ hτ) hpos (mul_nonneg hC (Real.exp_pos _).le) (hbound τ hτ)
        have hlower : τ ^ 3 * Real.exp
            (2 * τ * CarlemanWeights.weight α (-Real.log inner)) *
              (∫ x, ‖ψ x‖ ^ 2 ∂μ) ≤
            ∫ x, radialMassIntegrand r ψ α τ x ∂μ := by
          rw [← integral_const_mul]
          apply integral_mono_ae (hψ.const_mul _) hint
          filter_upwards [hr] with x hx
          have hphase := (radial_weight_gap hα hx.1 hx.2
            (hio.le.trans houter)).le
          have hexp := Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hphase (by positivity : 0 ≤ 2 * τ))
          have hweight := mul_le_mul (hcoef (r x) hx.1 hx.2.le) hexp
            (Real.exp_pos _).le (zero_le_one.trans (hcoef (r x) hx.1 hx.2.le))
          simp only [one_mul] at hweight
          simpa only [radialMassIntegrand, weightedNormSq, mul_assoc] using
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖ψ x‖)) (pow_nonneg hτ0 3)
        exact hlower.trans hupper)
  have hnorm := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖ψ x‖) hψ).mp hz
  filter_upwards [hnorm] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

end PfHk.UniqueContinuation
