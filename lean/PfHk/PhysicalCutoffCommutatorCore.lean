import PfHk.PhysicalCutoffCommutatorAlgebraLp
import PfHk.PhysicalLocalEnergyRough
import GptLean.PhysicalPFCovariantSymmetry

/-! The actual L2 scalar-cutoff commutator vector and covariant symmetry. -/

noncomputable section
namespace PfHk.PhysicalCutoffCommutator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 10000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply

variable {I : Type} [Fintype I] [DecidableEq I]

attribute [local irreducible] roughMultiply externalCovariant
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

theorem roughMultiply_symmetric (f : Position I → ℝ) (u v : WaveSpace I)
    (hu : HasMultiplier f u) (hv : HasMultiplier f v) :
    ⟪u, roughMultiply f v hv⟫_ℂ = ⟪roughMultiply f u hu, v⟫_ℂ := by
  exact l2_real_multiplier_pair (H := PhotonFock) f u v
    (roughMultiply f u hu) (roughMultiply f v hv)
    (roughMultiply_ae f u hu) (roughMultiply_ae f v hv)

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem externalCovariant_symmetric (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) (i : I) :
    ⟪inclusion I V u, externalCovariant V C κ hκ M hbound e A positive negative v hv i⟫_ℂ =
      ⟪externalCovariant V C κ hκ M hbound e A positive negative u hu i, inclusion I V v⟫_ℂ := by
  simp only [externalCovariant, inner_add_left, inner_add_right]
  exact congrArg₂ (fun z w : ℂ => z + w)
    (covariant_symmetric I V C κ hκ M hbound e i u v)
    (roughMultiply_symmetric (A i) (inclusion I V u) (inclusion I V v)
      (hu.vector i) (hv.vector i))

/-- The first-order differential expression `-i ∇η·π - (Δη)/2`, as an
actual L2 vector. No pointwise operator-domain representative is assumed. -/
def commutator (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) : WaveSpace I :=
  scalarCommutator (H := PhotonFock) a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)


end PfHk.PhysicalCutoffCommutator
