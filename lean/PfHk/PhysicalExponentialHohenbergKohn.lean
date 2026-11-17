import PfHk.PhysicalHohenbergKohn
import PfHk.VectorUniquenessExponential

/-! The physical Hohenberg--Kohn conclusion with a nonzero cutoff class
and an exponential moment of the common density. The final theorem joins
this with the nonvanishing-cutoff alternative. -/

noncomputable section
namespace PfHk.PhysicalHohenbergKohn

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms GptLean.Representability
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PhysicalFermionicCoefficients PfHk.PhysicalDiamagneticPotential

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  IsExternalWeakEigenstate PhysicalGroundStateWeak.stateReference

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ) (i : Fin N)

/-- Hohenberg--Kohn under the exponential-moment alternative. The cutoff
need only be nonzero as an almost-everywhere class. Only one potential pair
needs the additional local regularity, and density positivity and the full
weak eigenvalue equations are derived from the variational ground states. -/
theorem hohenberg_kohn_exponential_moment
    (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p₁ p₂ : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p₁)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p₂)
    (hd : (model i F χ C B S e).density p₁ = (model i F χ C B S e).density p₂)
    (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
    {α : ℝ} (hα : 0 < α)
    (hmoment : Integrable (fun x => Real.exp (α * ‖x‖) *
      PhysicalPairSpace.densityL1 ((model i F χ C B S e).density p₁) x) volume)
    (hreg : Nonempty (Regularity A₁ v₁) ∨ Nonempty (Regularity A₂ v₂)) :
    A₁.val =ᵐ[volume] A₂.val ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ -
          shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂) / N := by
  have hcommon : IsGroundState i F χ C B S e (shifted v₂ A₂) p₁ :=
    (PfHk.common_ground_state i F χ C B S e
      (a₁ := shifted v₁ A₁) (a₂ := shifted v₂ A₂) (p₁ := p₁) (p₂ := p₂) h₁ h₂ hd).2.1
  have hpositive : (∀ᵐ X ∂volume, p₁.val X ≠ 0) ∧
      ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
        ((model i F χ C B S e).density p₁) x := by
    rcases hreg with hleft | hright
    · rcases hleft with ⟨hr⟩
      exact ⟨PhysicalGroundStateUCP.ae_nonzero (N := N) F χ C B S e i
        A₁ v₁ p₁ h₁ U hr,
        PhysicalGroundStateUCP.model_density_pos (N := N) F χ C B S e i
          A₁ v₁ p₁ h₁ U hr⟩
    · rcases hright with ⟨hr⟩
      exact ⟨PhysicalGroundStateUCP.ae_nonzero (N := N) F χ C B S e i
        A₂ v₂ p₁ hcommon U hr,
        PhysicalGroundStateUCP.model_density_pos (N := N) F χ C B S e i
          A₂ v₂ p₁ hcommon U hr⟩
  have hA : A₁.val =ᵐ[volume] A₂.val :=
    PfHk.vector_potential_eq_of_density_positive_exponential_moment i F χ C B S e U.weyl
      (a₁ := shifted v₁ A₁) (a₂ := shifted v₂ A₂) (p₁ := p₁) (p₂ := p₂)
      h₁ h₂ hd he hχ hα hmoment hpositive.2
  have hscalar := scalar_of_common_ground_state F χ C B S e i
    A₁ A₂ v₁ v₂ p₁ h₁ hcommon hA hpositive.1
  have henergy : shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₁ =
      shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂ :=
    le_antisymm (hcommon p₂) (h₂ p₁)
  refine ⟨hA, ?_⟩
  filter_upwards [hscalar] with x hx
  exact hx.trans (congrArg (fun r : ℝ => v₂.val x +
    (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ - r) / N) henergy)

/-- The physical Hohenberg--Kohn theorem with either cutoff alternative
from the article. All assumptions refer to the actual potentials, states,
cutoff and common density. The scalar constant is exactly the difference
of ground-state energies divided by particle number. -/
theorem hohenberg_kohn
    (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p₁ p₂ : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p₁)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p₂)
    (hd : (model i F χ C B S e).density p₁ = (model i F χ C B S e).density p₂)
    (he : e ≠ 0) (hχ : ¬ (χ.value =ᵐ[volume] 0))
    (hcutoff : (∀ᵐ k ∂volume, χ.value k ≠ 0) ∨
      ∃ α : ℝ, 0 < α ∧ Integrable (fun x => Real.exp (α * ‖x‖) *
        PhysicalPairSpace.densityL1 ((model i F χ C B S e).density p₁) x) volume)
    (hreg : Nonempty (Regularity A₁ v₁) ∨ Nonempty (Regularity A₂ v₂)) :
    A₁.val =ᵐ[volume] A₂.val ∧
      ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
        (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ -
          shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂) / N := by
  rcases hcutoff with hn | hm
  · exact hohenberg_kohn_nonvanishing_cutoff F χ C B S e i U
      A₁ A₂ v₁ v₂ p₁ p₂ h₁ h₂ hd he hn hreg
  · rcases hm with ⟨α, hα, hmoment⟩
    exact hohenberg_kohn_exponential_moment F χ C B S e i U
      A₁ A₂ v₁ v₂ p₁ p₂ h₁ h₂ hd he hχ hα hmoment hreg

end PfHk.PhysicalHohenbergKohn
