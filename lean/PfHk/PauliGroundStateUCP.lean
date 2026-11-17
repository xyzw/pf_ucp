import PfHk.PauliUCPConsequences
import PfHk.PauliFermionicReduction
import PfHk.PauliCurrentGroundState

/-! Unique continuation and spin-summed density positivity for actual
normalized variational Pauli ground states. The unrestricted weak
equation follows from the checked joint fermionic reduction. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliGroundStateUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliGroundState PfHk.PauliPhysicalLocalRegularity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}
  (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave

section OpenSet

variable {Ω : Set PhysicalSourceCoordinates.Position}
  (a : RegularityOn A v Ω) (hN : 0 < N)
  (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
  (hfull : ∀ᵐ x ∂volume, x ∈ Ω)
  (p : State N) (hp : IsGroundState C e F χ A v c hc p)

include B a hN hΩ hconn hfull hp

/-- Nonvanishing of the full spin--photon wave function, with regularity
needed only on the given open full-measure set. -/
theorem ae_nonzero_on_open :
    ∀ᵐ X ∂volume, PauliReference.wave p.vector X ≠ 0 :=
  PauliUCPConsequences.ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull
    (PauliGroundStateWeak.full_weak_equation C e F χ A v c hc p hp) p.vector_ne_zero

theorem ae_norm_pos_on_open :
    ∀ᵐ X ∂volume, 0 < ‖PauliReference.wave p.vector X‖ :=
  (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull p hp).mono
    fun _ hX => norm_pos_iff.mpr hX

/-- Strict positivity of the actual electronic marginal, summed over
all electron spin configurations. -/
theorem electronic_density_pos_on_open :
    ∀ᵐ x ∂volume, 0 < PauliReference.density p.vector x :=
  PauliReference.density_pos_ae hN p.vector
    (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull p hp)

/-- Positivity of the density component of the physical Pauli
density-current pair. -/
theorem model_density_pos_on_open :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
      (PauliGroundState.data C e F χ p.vector) x :=
  PauliGroundState.data_density_pos_ae C e F χ hN p.vector
    (ae_nonzero_on_open F χ C e A v c hc B a hN hΩ hconn hfull p hp)

end OpenSet

section Global

variable (a : RegularityOn A v Set.univ) (hN : 0 < N)
  (p : State N) (hp : IsGroundState C e F χ A v c hc p)

include B a hN hp

theorem ae_nonzero : ∀ᵐ X ∂volume, PauliReference.wave p.vector X ≠ 0 :=
  ae_nonzero_on_open F χ C e A v c hc B a hN isOpen_univ isPreconnected_univ
    (ae_of_all _ fun _ => Set.mem_univ _) p hp

theorem ae_norm_pos : ∀ᵐ X ∂volume, 0 < ‖PauliReference.wave p.vector X‖ :=
  (ae_nonzero F χ C e A v c hc B a hN p hp).mono fun _ hX => norm_pos_iff.mpr hX

theorem electronic_density_pos :
    ∀ᵐ x ∂volume, 0 < PauliReference.density p.vector x :=
  PauliReference.density_pos_ae hN p.vector
    (ae_nonzero F χ C e A v c hc B a hN p hp)

theorem model_density_pos :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
      (PauliGroundState.data C e F χ p.vector) x :=
  PauliGroundState.data_density_pos_ae C e F χ hN p.vector
    (ae_nonzero F χ C e A v c hc B a hN p hp)

end Global

end PfHk.PauliGroundStateUCP

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
