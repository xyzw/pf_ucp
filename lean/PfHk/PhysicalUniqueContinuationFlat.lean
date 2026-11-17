import PfHk.PhysicalUniqueContinuation
import PfHk.UniqueContinuationFlatSeed

/-! A physical weak eigenstate with one infinite-order zero vanishes
throughout a connected full-measure region. This transfer is separated
from the subsequent construction of its Carleman and multiplier inputs. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy PfHk.UniqueContinuationDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion PhysicalPFScalarMultiplier.multiply
  ordinary radiation externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem zero_of_infinite_order {E α : ℝ} {U : Set (Position I)}
    (hCarleman : UniformLocalOperatorCarleman V C κ hκ M hbound e A positive negative E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ x ∂volume, x ∈ U)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {x₀ : Position I} (hx₀ : x₀ ∈ U)
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (inclusion I V u) x₀)) :
    ∀ᵐ x ∂volume, inclusion I V u x = 0 := by
  exact UniqueContinuation.ae_zero_of_uniform_flat_seed
    (X := Position I) (H := PhotonFock) (μ := volume) (ψ := inclusion I V u)
    (fun x R τ K => OperatorCarlemanAt V C κ hκ M hbound e A positive negative E x R α τ K)
    hα hU hfull hCarleman
    (fun x R τ K hCar hR hRsmall hK hcoef hxflat =>
      flat_implies_zero_ball V C κ hκ M hbound e A positive negative hCar
        hα hR hRsmall hK hcoef heigen C₀ hnegative hxflat)
    ⟨x₀, hx₀, hflat⟩

end PfHk.PhysicalCarlemanInput
