import PfHk.PauliWeylCurrent
import PfHk.PauliCommonGroundState
import PfHk.CutoffKernel

/-! Photon stationarity of actual Pauli variational ground states and
vanishing of the density-weighted external-vector source. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliPhotonVariation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.PhysicalPairSpace GptLean.Representability
  PfHk.PauliGroundState PfHk.PauliWeylEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave
  PauliGroundState.energy PauliGroundState.data
  PauliWeylEnergy.currentShift PauliWeylEnergy.densityShift PauliWeylEnergy.amplitude

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (W : ConcreteWeylLaw photonMeasure)

include W

theorem ground_real_amplitude (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (p : State N)
    (hp : IsGroundState C e F χ A v c hc p)
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ k ∂photonMeasure, K.val.2 k = (Real.sqrt ‖k.1‖ : ℂ) * f k) :
    2 * PauliWeylEnergy.amplitude K p.vector =
      e * PauliWeylEnergy.currentShift F χ C e A v c hc f p.vector := by
  have hz := PhysicalGroundState.linear_zero
    (X := 2 * PauliWeylEnergy.amplitude K p.vector -
      e * PauliWeylEnergy.currentShift F χ C e A v c hc f p.vector)
    (Y := ‖K.val.2‖ ^ 2 * ‖PauliReference.wave p.vector‖ ^ 2 +
      (e ^ 2 / 2) * PauliWeylEnergy.densityShift F χ f p.vector) (fun t => by
      have ht := hp (PauliWeyl.state W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) p)
      change PauliGroundState.energy C e F χ A v c hc p.vector ≤
        PauliGroundState.energy C e F χ A v c hc
          (PauliWeyl.displaced W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) p.vector) at ht
      have hpoly := ht.trans_eq
        (PauliWeylEnergy.energy_scaled F χ C e A v c hc W K hK t p.vector)
      linarith only [hpoly])
  exact sub_eq_zero.mp hz

theorem weyl_orthogonality (hN : 0 < N)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (p₁ p₂ : State N)
    (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
    (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
    (hd : data C e F χ p₁.vector = data C e F χ p₂.vector) (he : e ≠ 0)
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ k ∂photonMeasure, K.val.2 k = (Real.sqrt ‖k.1‖ : ℂ) * f k) :
    (∑ a, ∫ x, classicalVector F χ f a x *
      PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector) x a) = 0 := by
  have hcommon := (PauliGroundState.common_ground_state C e F χ hN
    A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd).2.1
  have hleft := ground_real_amplitude C e F χ W A₁ v₁ c hc p₁ h₁ K hK
  have hright := ground_real_amplitude C e F χ W A₂ v₂ c hc p₁ hcommon K hK
  have hJ := mul_left_cancel₀ he (hleft.symm.trans hright)
  exact (PauliWeylEnergy.currentShift_difference F χ C e c hc
    A₁ A₂ v₁ v₂ f p₁.vector hN).symm.trans (sub_eq_zero.mpr hJ)

theorem currentSource_zero (hN : 0 < N)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (p₁ p₂ : State N)
    (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
    (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
    (hd : data C e F χ p₁.vector = data C e F χ p₂.vector) (he : e ≠ 0) :
    PfHk.currentSource F χ
      (PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector)) = 0 := by
  apply PfHk.weightedKernel_zero_of_trunc_pairings
  intro m
  let b := PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector)
  have hp := PfHk.currentSource_pairing F χ
    (PfHk.vectorDifference_integrable (v₁, A₁) (v₂, A₂) (data C e F χ p₁.vector))
    (PhysicalWeyl.truncDirection m (PfHk.currentSource F χ b))
  have hz := weyl_orthogonality C e F χ W hN A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he
    (PhysicalWeyl.truncKernel m (PfHk.currentSource F χ b))
    (PhysicalWeyl.truncKernel_direction m (PfHk.currentSource F χ b))
  have hh : 2 * (inner ℂ (PfHk.currentSource F χ b).val.1
      (PhysicalWeyl.truncDirection m (PfHk.currentSource F χ b))).re = 0 :=
    hp.trans hz
  linarith

end PfHk.PauliPhotonVariation

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
