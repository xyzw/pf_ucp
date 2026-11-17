import PfHk.VectorUniqueness
import PfHk.PhysicalExponentialMoment
import PfHk.FourierExponentialUniqueness

/-!
The exponential-moment alternative in the physical vector-potential
uniqueness theorem. The cutoff may vanish on a set of positive measure.
Its almost-everywhere class must be nonzero, and the common density must
have one positive exponential moment.
-/

noncomputable section

namespace PfHk

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.PhysicalFock GptLean.PhysicalPolarization GptLean.Gaussian
  GptLean.Representability
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)
  (W : ConcreteWeylLaw photonMeasure)

include W in
/-- `thm-vector-uniqueness`, alternative (ii). An exponential moment of
the common density replaces almost-everywhere nonvanishing of the cutoff.
The density-weighted vector difference vanishes almost everywhere. -/
theorem vector_uniqueness_exponential_moment
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) {α : ℝ} (hα : 0 < α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 ((model i F χ C B S e).density p₁) x) volume) :
    vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) =ᵐ[volume] 0 := by
  have hkernel := (cutoff_kernel i F χ C B S e W h₁ h₂ hd he).2
  have hcomponents : ∀ j : Fin 3, ∀ᵐ x ∂volume,
      vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x j = 0 := by
    intro j
    exact FourierExponentialUniqueness.ae_eq_zero_of_cutoff_mul_fourierCoeff_zero
      (fun x => vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x j)
      ((EuclideanSpace.proj j : Vector →L[ℝ] ℝ).integrable_comp
        (vectorDifference_integrable a₁ a₂ _))
      (div_pos hα (by norm_num : (0 : ℝ) < 2))
      (PhysicalExponentialMoment.model_component_integrable F χ C B S e i p₁
        a₁ a₂ hα.le hmoment j)
      (fun k => χ.value (-k))
      (PhysicalExponentialMoment.cutoff_not_ae_zero_neg χ hχ)
      (hkernel.mono fun _ hk => hk j)
  filter_upwards [ae_all_iff.mpr hcomponents] with x hx
  change vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x = 0
  ext j
  exact hx j

include W in
/-- The exponential-moment alternative gives equality of the actual
external vector potentials when the common density is positive almost
everywhere. Physical UCP supplies that positivity in the HK assembly. -/
theorem vector_potential_eq_of_density_positive_exponential_moment
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) {α : ℝ} (hα : 0 < α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 ((model i F χ C B S e).density p₁) x) volume)
    (hρ : ∀ᵐ x ∂volume, 0 < densityL1 ((model i F χ C B S e).density p₁) x) :
    a₁.2.val =ᵐ[volume] a₂.2.val := by
  have hzero := vector_uniqueness_exponential_moment i F χ C B S e W
    h₁ h₂ hd he hχ hα hmoment
  filter_upwards [hzero, hρ] with x hx hρx
  change densityL1 ((model i F χ C B S e).density p₁) x •
    (a₁.2.val x - a₂.2.val x) = 0 at hx
  exact sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_left (ne_of_gt hρx))

end PfHk
