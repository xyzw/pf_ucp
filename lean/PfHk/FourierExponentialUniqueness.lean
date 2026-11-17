import PfHk.ExponentialFourierAnalytic
import PfHk.SeparateAnalyticUniqueness
import PfHk.FourierUniqueness

/-! Exponential decay makes the physical Fourier coefficient separately
analytic. A nontrivial separately analytic function is nonzero almost
everywhere, so an arbitrary nonzero measurable cutoff class suffices for
Fourier uniqueness. Its nonzero set need not contain an open ball. -/

noncomputable section

namespace PfHk.FourierExponentialUniqueness

open MeasureTheory GptLean GptLean.Gaussian GptLean.PhysicalGroundState

set_option autoImplicit false
set_option Elab.async false

/-- An exponentially integrable physical Fourier coefficient is either
identically zero or nonzero almost everywhere. -/
theorem fourierCoeff_eq_zero_or_ae_ne_zero (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume) :
    fourierCoeff w = 0 ∨ ∀ᵐ k ∂volume, fourierCoeff w k ≠ 0 := by
  apply SeparateAnalyticUniqueness.euclidean_eq_zero_or_ae_ne_zero
    (continuous_fourierCoeff w hw)
  exact fun x j =>
    ExponentialFourierAnalytic.analyticOnNhd_fourierCoeff_update w hw hβ hm x j

/-- Vanishing after multiplication by any nonzero cutoff class forces an
exponentially integrable function to vanish. No open cutoff support or
almost-everywhere nonvanishing of the cutoff is assumed. -/
theorem ae_eq_zero_of_cutoff_mul_fourierCoeff_zero (w : FieldSpace → ℝ)
    (hw : Integrable w volume) {β : ℝ} (hβ : 0 < β)
    (hm : Integrable (fun x => Real.exp (β * ‖x‖) * |w x|) volume)
    (g : FieldSpace → ℂ) (hg : ¬ (g =ᵐ[volume] 0))
    (hzero : ∀ᵐ k ∂volume, g k * fourierCoeff w k = 0) :
    w =ᵐ[volume] 0 := by
  rcases fourierCoeff_eq_zero_or_ae_ne_zero w hw hβ hm with hz | hn
  · exact FourierUniqueness.ae_eq_zero_of_fourierCoeff_zero w hw
      (fun k => congrFun hz k)
  · exfalso
    apply hg
    filter_upwards [hzero, hn] with k hk hkn
    exact (mul_eq_zero.mp hk).resolve_right hkn

end PfHk.FourierExponentialUniqueness
