import PfHk.PauliCutoffKernel
import PfHk.PhysicalExponentialMoment
import PfHk.FourierExponentialUniqueness

/-! Both physical cutoff alternatives for spinful vector-potential
uniqueness. The exponential moment is that of the actual spin-summed density. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliVectorUniqueness

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.PhysicalPairSpace GptLean.Representability
  PfHk.PauliGroundState

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 90000

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

theorem vector_uniqueness_exponential_moment (he : e ≠ 0)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) {α : ℝ} (hα : 0 < α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 (data C e F χ p₁.vector) x) volume) :
    PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) =ᵐ[volume] 0 := by
  have hkernel := (cutoff_kernel C e F χ W hN A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he).2
  have hnonneg : ∀ᵐ x ∂volume, 0 ≤ densityL1 (data C e F χ p₁.vector) x := by
    rw [data_density_eq C e F χ hN]
    exact PhysicalElectronicDensity.density_nonneg (PauliReference.wave p₁.vector)
  have hcomponents : ∀ a : Fin 3, ∀ᵐ x ∂volume,
      PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x a = 0 := by
    intro a
    exact FourierExponentialUniqueness.ae_eq_zero_of_cutoff_mul_fourierCoeff_zero
      (fun x => PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x a)
      ((EuclideanSpace.proj a : Vector →L[ℝ] ℝ).integrable_comp
        (PfHk.vectorDifference_integrable (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector)))
      (div_pos hα (by norm_num : (0 : ℝ) < 2))
      (PhysicalExponentialMoment.component_integrable (v₁, A₁) (v₂, A₂)
        (data C e F χ p₁.vector) hα.le hnonneg hmoment a)
      (fun k => χ.value (-k)) (PhysicalExponentialMoment.cutoff_not_ae_zero_neg χ hχ)
      (hkernel.mono fun _ hk => hk a)
  filter_upwards [ae_all_iff.mpr hcomponents] with x hx
  change PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x = 0
  ext a
  exact hx a

theorem vector_potential_eq_exponential_moment (he : e ≠ 0)
    (hχ : ¬ (χ.value =ᵐ[volume] 0)) {α : ℝ} (hα : 0 < α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      densityL1 (data C e F χ p₁.vector) x) volume)
    (hρ : ∀ᵐ x ∂volume, 0 < densityL1 (data C e F χ p₁.vector) x) :
    A₁.val =ᵐ[volume] A₂.val := by
  have hz := vector_uniqueness_exponential_moment C e F χ W hN
    A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hχ hα hmoment
  filter_upwards [hz, hρ] with x hx hρx
  change densityL1 (data C e F χ p₁.vector) x • (A₁.val x - A₂.val x) = 0 at hx
  exact sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_left (ne_of_gt hρx))

theorem vector_potential_eq (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
    (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
      ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
        densityL1 (data C e F χ p₁.vector) x) volume)
    (hρ : ∀ᵐ x ∂volume, 0 < densityL1 (data C e F χ p₁.vector) x) :
    A₁.val =ᵐ[volume] A₂.val := by
  rcases hcutoff with hnonzero | ⟨α, hα, hm⟩
  · exact vector_potential_eq_nonvanishing_cutoff C e F χ W hN
      A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hnonzero hρ
  · exact vector_potential_eq_exponential_moment C e F χ W hN
      A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hχ hα hm hρ

end PfHk.PauliVectorUniqueness

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
