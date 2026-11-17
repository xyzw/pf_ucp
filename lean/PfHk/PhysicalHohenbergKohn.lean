import PfHk.PhysicalGroundStateEquation
import PfHk.PhysicalScalarWeakUniqueness
import PfHk.VectorUniqueness

/-! The physical Hohenberg--Kohn conclusion for a cutoff which is nonzero
almost everywhere. Equality of the actual density-current pairs makes one
state a common minimizer. The regular pair supplies nonvanishing and density
positivity, photon variations fix the vector potential, and the two full
weak equations fix the scalar potential with the exact energy constant. -/

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

/-- Two physical Hamiltonians with the same vector potential and a common
nonvanishing variational ground state have scalar potentials differing by
the exact difference of their ground-state energies divided by particle
number. The full weak equations are derived from minimization. -/
theorem scalar_of_common_ground_state
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p)
    (hA : A₁.val =ᵐ[volume] A₂.val)
    (hn : ∀ᵐ X ∂volume, p.val X ≠ 0) :
    ∀ᵐ x ∂volume, v₁.val x = v₂.val x +
      (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p -
        shiftedEnergy i F χ C B S e (shifted v₂ A₂) p) / N := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S e p
  have hvalue : inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val :=
    PhysicalGroundStateWeak.stateReference_value F χ C B S e p
  have hu : ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X ≠ 0 :=
    (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) => ∀ᵐ X ∂volume, ψ X ≠ 0) hvalue).mpr hn
  have hw₁ := PhysicalGroundStateEquation.full_weak_equation
    (N := N) F χ C B S e i A₁ v₁ p h₁ u hvalue
  have hw₂ := PhysicalGroundStateEquation.full_weak_equation
    (N := N) F χ C B S e i A₂ v₂ p h₂ u hvalue
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  exact PhysicalScalarWeakUniqueness.potential_difference_constant (N := N)
    C (CenteredPhysicalReference.profile (N := N) F χ 0)
    (CenteredPhysicalReference.profile_measurable (N := N) F χ 0)
    (CenteredPhysicalReference.profileBound F χ)
    (CenteredPhysicalReference.profile_bound (N := N) F χ 0) e A₁ A₂ v₁ v₂ 1 zero_le_one hN
    (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p)
    (shiftedEnergy i F χ C B S e (shifted v₂ A₂) p) u hA hw₁ hw₂ hu

/-- The Hohenberg--Kohn theorem under the nonvanishing-cutoff alternative.
Only one potential pair needs the additional local UCP regularity. Density
positivity, nonvanishing and equality of vector potentials are conclusions. -/
theorem hohenberg_kohn_nonvanishing_cutoff
    (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e)
    (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (p₁ p₂ : State F χ C B S e (N := N))
    (h₁ : IsGroundState i F χ C B S e (shifted v₁ A₁) p₁)
    (h₂ : IsGroundState i F χ C B S e (shifted v₂ A₂) p₂)
    (hd : (model i F χ C B S e).density p₁ = (model i F χ C B S e).density p₂)
    (he : e ≠ 0) (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0)
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
    PfHk.vector_potential_eq_of_density_positive i F χ C B S e U.weyl
      (a₁ := shifted v₁ A₁) (a₂ := shifted v₂ A₂) (p₁ := p₁) (p₂ := p₂)
      h₁ h₂ hd he hχ hpositive.2
  have hscalar := scalar_of_common_ground_state F χ C B S e i
    A₁ A₂ v₁ v₂ p₁ h₁ hcommon hA hpositive.1
  have henergy : shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₁ =
      shiftedEnergy i F χ C B S e (shifted v₂ A₂) p₂ :=
    le_antisymm (hcommon p₂) (h₂ p₁)
  refine ⟨hA, ?_⟩
  filter_upwards [hscalar] with x hx
  exact hx.trans (congrArg (fun r : ℝ => v₂.val x +
    (shiftedEnergy i F χ C B S e (shifted v₁ A₁) p₁ - r) / N) henergy)

end PfHk.PhysicalHohenbergKohn
