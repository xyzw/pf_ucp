import GptLean.PhysicalH1Fourier

/-!
The weak H1 Fourier bridge identifies the coordinate kinetic integrals
with their actual derivative norms. Dropping the factor (2π)^2 gives
the unscaled frequency control needed by the joint Rellich symbol.
-/

noncomputable section

namespace GptLean.PhysicalH1Fourier

open MeasureTheory ElectronicH1Space
open scoped ENNReal

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem frequencySymbol_norm_sq (i : I) (ξ : EuclideanSpace ℝ I) :
    ‖frequencySymbol i ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (ξ i) ^ 2 := by
  simp [frequencySymbol, EuclideanSpace.inner_single_right,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow]

theorem derivative_energy_lintegral (u : H1 H I) (i : I) :
    ENNReal.ofReal (‖derivative i u‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2 * (ξ i) ^ 2) *
        ‖fourier (value u) ξ‖ₑ ^ 2 := by
  have h := Repair.toL2_norm_sq (Lp.memLp (fourier (derivative i u)))
  simp only [Lp.toLp_coeFn, fourier.norm_map] at h
  rw [h, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    (ae_of_all _ fun _ => sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [derivative_ae u i] with ξ hx
  rw [hx, norm_smul, mul_pow, frequencySymbol_norm_sq,
    ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The Fourier convention strengthens the unscaled coordinate estimate. -/
theorem coordinate_frequency_bound (u : H1 H I) (i : I) :
    (∫⁻ ξ, ENNReal.ofReal ((ξ i) ^ 2) * ‖fourier (value u) ξ‖ₑ ^ 2) ≤
      ENNReal.ofReal (‖derivative i u‖ ^ 2) := by
  rw [derivative_energy_lintegral]
  apply lintegral_mono
  intro ξ
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [sq_nonneg (ξ i)]

theorem complex_coordinate_frequency_bound (u : ElectronicH1Complex.ComplexH1 H I) (i : I) :
    (∫⁻ ξ, ENNReal.ofReal ((ξ i) ^ 2) *
      ‖fourier (ElectronicH1Complex.value u) ξ‖ₑ ^ 2) ≤
        ENNReal.ofReal (‖ElectronicH1Complex.derivative i u‖ ^ 2) :=
  coordinate_frequency_bound (ElectronicH1Complex.realEquiv u) i

end GptLean.PhysicalH1Fourier
