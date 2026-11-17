import PfHk.PauliPhotonVariation
import PfHk.PauliGaugeVariation
import PfHk.VectorUniqueness

/-! Both longitudinal and transverse cutoff identities for the actual
spinful Pauli ground-state density and combined current. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliVectorUniqueness

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.PhysicalPairSpace GptLean.Representability GptLean.TransformationsGauge
  PfHk.PauliGroundState

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave
  PauliGroundState.energy PauliGroundState.data

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (W : ConcreteWeylLaw photonMeasure) (hN : 0 < N)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (p₁ p₂ : State N)
  (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
  (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
  (hd : data C e F χ p₁.vector = data C e F χ p₂.vector)

include W hN h₁ h₂ hd

theorem cutoff_kernel (he : e ≠ 0) :
    (∀ g : SpatialGauge, ∫ x, inner ℝ (g.gradientVector x)
      (PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x) = 0) ∧
    (∀ᵐ k ∂volume, ∀ a : Fin 3, χ.value (-k) * PhysicalGroundState.fourierCoeff
      (fun x => PfHk.vectorDifference (v₁, A₁) (v₂, A₂)
        (data C e F χ p₁.vector) x a) k = 0) := by
  have hdiv := PauliGaugeVariation.vectorDifference_divergence C e F χ hN
    A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd
  refine ⟨hdiv, ?_⟩
  exact PfHk.cutoff_mul_fourier_zero_of_source F χ
    (PfHk.vectorDifference_integrable (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector))
    (PauliPhotonVariation.currentSource_zero C e F χ W hN
      A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he)
    (PfHk.fourier_transverse_of_gauge_tests
      (PfHk.vectorDifference_integrable (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector)) hdiv)

theorem vector_uniqueness_nonvanishing_cutoff (he : e ≠ 0)
    (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0) :
    PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) =ᵐ[volume] 0 := by
  have hkernel := (cutoff_kernel C e F χ W hN A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he).2
  apply FourierUniqueness.vector_ae_eq_zero_of_fourierCoeff_ae_zero
  · intro a
    exact (EuclideanSpace.proj a : Vector →L[ℝ] ℝ).integrable_comp
      (PfHk.vectorDifference_integrable (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector))
  · filter_upwards [hkernel, PfHk.cutoff_nonzero_neg_ae χ hχ] with k hk hkn
    intro a
    exact (mul_eq_zero.mp (hk a)).resolve_left hkn

theorem vector_potential_eq_nonvanishing_cutoff (he : e ≠ 0)
    (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0)
    (hρ : ∀ᵐ x ∂volume, 0 < densityL1 (data C e F χ p₁.vector) x) :
    A₁.val =ᵐ[volume] A₂.val := by
  have hz := vector_uniqueness_nonvanishing_cutoff C e F χ W hN
    A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hχ
  filter_upwards [hz, hρ] with x hx hρx
  change densityL1 (data C e F χ p₁.vector) x • (A₁.val x - A₂.val x) = 0 at hx
  exact sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_left (ne_of_gt hρx))

end PfHk.PauliVectorUniqueness

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
