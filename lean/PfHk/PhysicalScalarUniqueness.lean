import PfHk.ScalarUniqueness
import GptLean.RepresentabilityAmplitudeMeasure

/-! Scalar uniqueness on the actual electronic configuration space.
The existing measure-preserving grouping of Cartesian coordinates supplies
Fubini's one-particle reduction. Scalar test functions against the joint
probability density suffice for the distributional cancellation step. -/

noncomputable section
namespace PfHk.PhysicalScalarUniqueness

open MeasureTheory Filter GptLean GptLean.SymmetricLift GptLean.Representability
open scoped ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 60000

/-- Grouping the Cartesian coordinates recovers the actual particle map. -/
theorem amplitudePositions_particle {N : ℕ} (X : Configuration N) (n : Fin N) :
    amplitudePositions (Fin N) X n = particle X n := by
  ext b
  rfl

/-- The exact scalar constant, after cancellation of the nonvanishing
physical wave function. No regularity of the one-body difference is needed. -/
theorem potential_difference_constant_of_sum_eq {N : ℕ} (hN : 0 < N)
    (v₁ v₂ : EuclideanSpace ℝ (Fin 3) → ℝ) (E₁ E₂ : ℝ)
    (hsum : ∀ᵐ X : Configuration N ∂volume,
      ∑ n, (v₁ (particle X n) - v₂ (particle X n)) = E₁ - E₂) :
    ∀ᵐ x ∂volume, v₁ x = v₂ x + (E₁ - E₂) / N := by
  let e := amplitudePositions (Fin N)
  have he : MeasurePreserving e.symm volume volume :=
    (amplitudePositions_measurePreserving (Fin N)).symm
  have hs : ∀ᵐ x : Fin N → EuclideanSpace ℝ (Fin 3) ∂volume,
      ∑ n, (v₁ (x n) - v₂ (x n)) = E₁ - E₂ := by
    filter_upwards [he.quasiMeasurePreserving.ae hsum] with x hx
    have hp (n : Fin N) : particle (e.symm x) n = x n :=
      (amplitudePositions_particle (e.symm x) n).symm.trans
        (congrArg (fun y : Fin N → EuclideanSpace ℝ (Fin 3) => y n) (e.apply_symm_apply x))
    simpa only [hp] using hx
  have hd := ScalarUniqueness.ae_eq_div_of_sum_eq
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (NeZero.ne volume) hN
    (fun x => v₁ x - v₂ x) (E₁ - E₂) hs
  filter_upwards [hd] with x hx
  linarith

/-- A nonzero almost-everywhere weight can be cancelled after the scalar
fundamental lemma for distributions. -/
theorem ae_eq_zero_of_weak_weight
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (w ρ : X → ℝ)
    (hρ : ∀ᵐ x ∂μ, ρ x ≠ 0)
    (hi : Integrable (fun x => w x * ρ x) μ)
    (hweak : ∀ η : X → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ x, η x * (w x * ρ x) ∂μ = 0) :
    ∀ᵐ x ∂μ, w x = 0 := by
  have hz : ∀ᵐ x ∂μ, w x * ρ x = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.locallyIntegrable hweak
  filter_upwards [hz, hρ] with x hx hρx
  exact (mul_eq_zero.mp hx).resolve_right hρx

/-- Scalar tests of the physical joint density determine the potential
difference. The weak identity is supplied by subtracting the actual forms. -/
theorem potential_difference_constant_of_weak_density
    {N : ℕ} (hN : 0 < N) {H : Type*} [NormedAddCommGroup H]
    (v₁ v₂ : EuclideanSpace ℝ (Fin 3) → ℝ) (E₁ E₂ : ℝ)
    (ψ : Configuration N → H) (hψ : ∀ᵐ X ∂volume, ψ X ≠ 0)
    (hi : Integrable (fun X =>
      ((∑ n, (v₁ (particle X n) - v₂ (particle X n))) - (E₁ - E₂)) * ‖ψ X‖ ^ 2) volume)
    (hweak : ∀ η : Configuration N → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ X, η X * (((∑ n, (v₁ (particle X n) - v₂ (particle X n))) - (E₁ - E₂)) *
        ‖ψ X‖ ^ 2) = 0) :
    ∀ᵐ x ∂volume, v₁ x = v₂ x + (E₁ - E₂) / N := by
  apply potential_difference_constant_of_sum_eq hN v₁ v₂ E₁ E₂
  have hz := ae_eq_zero_of_weak_weight volume
    (fun X : Configuration N =>
      (∑ n, (v₁ (particle X n) - v₂ (particle X n))) - (E₁ - E₂))
    (fun X => ‖ψ X‖ ^ 2)
    (hψ.mono fun X hX => pow_ne_zero 2 (norm_ne_zero_iff.mpr hX)) hi hweak
  exact hz.mono fun X hX => sub_eq_zero.mp hX

end PfHk.PhysicalScalarUniqueness
