import PfHk.PauliScalarWeakUniqueness
import PfHk.PauliGroundStateUCP
import PfHk.PauliCommonGroundState
import PfHk.PauliVectorUniqueness

/-! Integrated spinful Hohenberg--Kohn uniqueness for the actual Pauli
form, variational ground states and spin-summed density-current data.
Both cutoff alternatives are included. Regularity is needed for only
one potential pair, and only away from the stated exceptional set. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliHohenbergKohn

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliGroundState PfHk.PauliPhysicalLocalRegularity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] referenceSubspace inclusion PauliReference.wave
  PauliGroundState.energy PauliGroundState.data

variable {N : ℕ} (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (F : Frame) (χ : ArticleCutoff) (hN : 0 < N)
  (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (p₁ p₂ : State N)
  (h₁ : IsGroundState C e F χ A₁ v₁ c hc p₁)
  (h₂ : IsGroundState C e F χ A₂ v₂ c hc p₂)
  (hd : data C e F χ p₁.vector = data C e F χ p₂.vector)
  (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
  (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
    ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
      PhysicalPairSpace.densityL1 (data C e F χ p₁.vector) x) volume)

include hN U h₁ h₂ hd he hχ hcutoff

theorem hohenberg_kohn_on_open {Ω : Set PhysicalSourceCoordinates.Position}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hfull : ∀ᵐ x ∂volume, x ∈ Ω)
    (hreg : Nonempty (RegularityOn A₁ v₁ Ω) ∨ Nonempty (RegularityOn A₂ v₂ Ω)) :
    A₁.val =ᵐ[volume] A₂.val ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (energy C e F χ A₁ v₁ c hc p₁.vector -
          energy C e F χ A₂ v₂ c hc p₂.vector) / N := by
  have hcommon : IsGroundState C e F χ A₂ v₂ c hc p₁ :=
    (PauliGroundState.common_ground_state C e F χ hN A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd).2.1
  have hn : ∀ᵐ X ∂volume, PauliReference.wave p₁.vector X ≠ 0 := by
    rcases hreg with hleft | hright
    · obtain ⟨a⟩ := hleft
      exact PauliGroundStateUCP.ae_nonzero_on_open F χ C e A₁ v₁ c hc U a hN
        hΩ hconn hfull p₁ h₁
    · obtain ⟨a⟩ := hright
      exact PauliGroundStateUCP.ae_nonzero_on_open F χ C e A₂ v₂ c hc U a hN
        hΩ hconn hfull p₁ hcommon
  have hρ : ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1 (data C e F χ p₁.vector) x :=
    PauliGroundState.data_density_pos_ae C e F χ hN p₁.vector hn
  have hA := PauliVectorUniqueness.vector_potential_eq C e F χ U.weyl hN
    A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hχ hcutoff hρ
  have hs := scalar_of_common_ground_state C e F χ hN A₁ A₂ v₁ v₂ c hc
    p₁ h₁ hcommon hA hn
  have hE : energy C e F χ A₂ v₂ c hc p₁.vector =
      energy C e F χ A₂ v₂ c hc p₂.vector := le_antisymm (hcommon p₂) (h₂ p₁)
  refine ⟨hA, ?_⟩
  filter_upwards [hs] with x hx
  exact hx.trans (congrArg (fun E : ℝ => v₂.val x +
    (energy C e F χ A₁ v₁ c hc p₁.vector - E) / N) hE)

theorem hohenberg_kohn
    (hreg : Nonempty (RegularityOn A₁ v₁ Set.univ) ∨
      Nonempty (RegularityOn A₂ v₂ Set.univ)) :
    A₁.val =ᵐ[volume] A₂.val ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (energy C e F χ A₁ v₁ c hc p₁.vector -
          energy C e F χ A₂ v₂ c hc p₂.vector) / N :=
  hohenberg_kohn_on_open C e F χ hN U A₁ A₂ v₁ v₂ c hc p₁ p₂ h₁ h₂ hd he hχ hcutoff
    isOpen_univ isPreconnected_univ (ae_of_all _ fun _ => Set.mem_univ _) hreg

end PfHk.PauliHohenbergKohn

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
