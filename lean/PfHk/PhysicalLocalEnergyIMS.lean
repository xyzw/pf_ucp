import PfHk.PhysicalLocalEnergy

noncomputable section
namespace PfHk.PhysicalLocalEnergy
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false

theorem commuting_singleCutoff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : H →L[ℂ] H) (hL : ∀ u v, ⟪u, L v⟫_ℂ = ⟪L u, v⟫_ℂ)
    (d d₁ d₂ : H) (h₁ : d₁ = L d) (h₂ : d₂ = L d₁) :
    ‖d₁‖ ^ 2 = (⟪d₂, d⟫_ℂ).re := by
  rw [h₂, h₁, ← hL, re_inner_self]

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
attribute [local irreducible] DifferentiableMultiplier.multiplier
  DifferentiableMultiplier.derivativeMultiplier
variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

theorem radiation_singleCutoff (a : DifferentiableMultiplier I)
    (u : Reference I V) :
    ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a u)‖ ^ 2 =
      (⟪radiation I V (PhysicalPFScalarMultiplier.multiply V a
        (PhysicalPFScalarMultiplier.multiply V a u)), radiation I V u⟫_ℂ).re := by
  exact commuting_singleCutoff (H := WaveSpace I) (a.multiplier (H := PhotonFock))
    (a.multiplier_symmetric (H := PhotonFock)) _ _ _
    (PhysicalPFScalarMultiplier.radiation_multiply V a u)
    (PhysicalPFScalarMultiplier.radiation_multiply V a (PhysicalPFScalarMultiplier.multiply V a u))

theorem potential_singleCutoff (a : DifferentiableMultiplier I)
    (u : Reference I V) :
    ‖potential I V (PhysicalPFScalarMultiplier.multiply V a u)‖ ^ 2 =
      (⟪potential I V (PhysicalPFScalarMultiplier.multiply V a
        (PhysicalPFScalarMultiplier.multiply V a u)), potential I V u⟫_ℂ).re := by
  exact commuting_singleCutoff (H := WaveSpace I) (a.multiplier (H := PhotonFock))
    (a.multiplier_symmetric (H := PhotonFock)) _ _ _
    (PhysicalPFScalarMultiplier.potential_multiply V a u)
    (PhysicalPFScalarMultiplier.potential_multiply V a (PhysicalPFScalarMultiplier.multiply V a u))

end PfHk.PhysicalLocalEnergy
