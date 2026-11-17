import PfHk.PhysicalLocalEnergyRough

noncomputable section
namespace PfHk.PhysicalLocalEnergy
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply roughMultiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  externalCovariant externalForm externalEnergy
variable {I : Type} [Fintype I] [DecidableEq I]

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem externalCovariant_singleCutoff (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (a : DifferentiableMultiplier I) (i : I) :
    ‖externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) i‖ ^ 2 =
    (⟪externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u))
      ((hu.localize V a).localize V a) i,
      externalCovariant V C κ hκ M hbound e A positive negative u hu i⟫_ℂ).re +
      ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2 := by
  have h₁ := externalCovariant_localize V C κ hκ M hbound e A positive negative u hu a i
  have h₂ := externalCovariant_localize V C κ hκ M hbound e A positive negative
    (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) a i
  have hv := PhysicalPFScalarMultiplier.value_multiply V a u
  have hc := multiplier_derivative_commute a i (inclusion I V u)
  let L : WaveSpace I →L[ℂ] WaveSpace I := a.multiplier
  let B : WaveSpace I →L[ℂ] WaveSpace I := a.derivativeMultiplier i
  let d₁ := externalCovariant V C κ hκ M hbound e A positive negative
    (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) i
  let b := (-Complex.I) • B (inclusion I V u)
  have hprod : externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u))
      ((hu.localize V a).localize V a) i = L (d₁ + b) :=
    h₂.trans ((congrArg (fun z : WaveSpace I => L d₁ + (-Complex.I) • B z) hv).trans
      ((congrArg (fun z : WaveSpace I => L d₁ + (-Complex.I) • z) hc).trans
        ((congrArg (fun z : WaveSpace I => L d₁ + z)
          (L.map_smul (-Complex.I) (B (inclusion I V u))).symm).trans
            (L.map_add d₁ b).symm)))
  have h := singleCutoff_of_product (H := WaveSpace I) L
    (a.multiplier_symmetric (H := PhotonFock))
    (externalCovariant V C κ hκ M hbound e A positive negative u hu i) d₁ _ b h₁ hprod
  exact h.trans (congrArg (fun r : ℝ =>
    (⟪externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a (PhysicalPFScalarMultiplier.multiply V a u))
      ((hu.localize V a).localize V a) i,
      externalCovariant V C κ hκ M hbound e A positive negative u hu i⟫_ℂ).re + r ^ 2)
    (norm_negI_smul (B (inclusion I V u))))

theorem roughMultiply_singleCutoff (a : DifferentiableMultiplier I)
    (f : Position I → ℝ) (u : Reference I V)
    (h : HasMultiplier f (inclusion I V u))
    (h' : HasMultiplier f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u)))
    (h'' : HasMultiplier f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a
      (PhysicalPFScalarMultiplier.multiply V a u)))) :
    ‖roughMultiply f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u)) h'‖ ^ 2 =
    (⟪roughMultiply f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a
      (PhysicalPFScalarMultiplier.multiply V a u))) h'',
      roughMultiply f (inclusion I V u) h⟫_ℂ).re := by
  exact commuting_singleCutoff (H := WaveSpace I) (a.multiplier (H := PhotonFock))
    (a.multiplier_symmetric (H := PhotonFock)) _ _ _
    (roughMultiply_reference_localize V a f u h h')
    (roughMultiply_reference_localize V a f (PhysicalPFScalarMultiplier.multiply V a u) h' h'')

end PfHk.PhysicalLocalEnergy
