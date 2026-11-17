import PfHk.PhysicalDensityInfiniteOrder
import PfHk.DensityFlatPoint

noncomputable section
namespace PfHk.PhysicalInfiniteOrder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 10000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : Position I → ℝ)
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- A positive-measure zero set of an actual weak PF eigenstate contains an
infinite-order zero in every full-measure region. The dimension relation
`2q = d` identifies the Sobolev support exponent with Lebesgue density. -/
theorem exists_physical_flat_point {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {p q S L : ℝ} (hpq : p.HolderConjugate q) (hd : (Fintype.card I : ℝ) = 2 * q) (hS : 0 ≤ S)
    (hSob : ScalarSobolevBound (I := I) p S)
    (hcutoff : ∀ x₀ : Position I, ∀ r : ℝ, 0 < r → r ≤ 1 →
      Nonempty (BallCutoff x₀ r L))
    {U : Set (Position I)} (hU : ∀ᵐ x ∂volume, x ∈ U)
    (hpositive : 0 < volume {x | inclusion I V u x = 0}) :
    ∃ x₀ ∈ U, inclusion I V u x₀ = 0 ∧
      InfiniteOrder.FlatAtZero (localMass (μ := volume) (inclusion I V u) x₀) := by
  exact exists_flat_point_of_density (ψ := inclusion I V u) hd
    (Lp.stronglyMeasurable (inclusion I V u)).norm.measurable hU hpositive
    (fun x₀ hdensity => physical_flat_at_zero_density V C κ hκ M hbound e A positive negative
      heigen C₀ hnegative hpq hS hSob x₀
        (fun r => Classical.choice (hcutoff x₀ r r.property.1 r.property.2)) hdensity)

end PfHk.PhysicalInfiniteOrder
