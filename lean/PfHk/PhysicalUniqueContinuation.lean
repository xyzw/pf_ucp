import PfHk.PhysicalLocalUniqueContinuation
import PfHk.PhysicalLocalEnergyBumps
import PfHk.ConfigurationGeometry
import PfHk.UniqueContinuationTransfer

/-! Conditional physical UCP transfer. The remaining Carleman input is
stated for the actual operator graph at arbitrary centers. All continuation
steps, from positive-measure zeros through propagation, are conclusions. -/

noncomputable section
namespace PfHk.PhysicalCarlemanInput

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy PfHk.PhysicalInfiniteOrder PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem zero_of_positive_zero_measure {E α : ℝ} {U : Set (Position I)}
    (hCarleman : UniformLocalOperatorCarleman V C κ hκ M hbound e A positive negative E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ x ∂volume, x ∈ U)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {p q S : ℝ} (hpq : p.HolderConjugate q) (hd : (Fintype.card I : ℝ) = 2 * q)
    (hS : 0 ≤ S) (hSob : ScalarSobolevBound (I := I) p S)
    (hpositive : 0 < volume {x | inclusion I V u x = 0}) :
    ∀ᵐ x ∂volume, inclusion I V u x = 0 := by
  exact UniqueContinuation.ae_zero_of_uniform_flat_vanishing
    (X := Position I) (H := PhotonFock) (μ := volume) (ψ := inclusion I V u)
    (fun x R τ K => OperatorCarlemanAt V C κ hκ M hbound e A positive negative E x R α τ K)
    hα hU hfull hCarleman
    (fun x R τ K hCar hR hRsmall hK hcoef hflat =>
      flat_implies_zero_ball V C κ hκ M hbound e A positive negative hCar
        hα hR hRsmall hK hcoef heigen C₀ hnegative hflat)
    (exists_physical_flat_point V C κ hκ M hbound e A positive negative
      heigen C₀ hnegative hpq hd hS hSob
      (L := ballCutoffConstant (I := I))
      (fun x r hr _ => ⟨ballCutoff x r hr⟩) hfull hpositive)

/-- A nonzero full-space weak PF eigenvector is nonzero almost everywhere
once the actual uniform physical operator Carleman estimate is supplied.
The full-space weak equation remains explicit until the fermionic reducing
subspace argument supplies it. -/
theorem ae_nonzero_of_uniform_operatorCarleman {E α : ℝ} {U : Set (Position I)}
    (hCarleman : UniformLocalOperatorCarleman V C κ hκ M hbound e A positive negative E α U)
    (hα : 0 < α) (hU : IsPreconnected U)
    (hfull : ∀ᵐ x ∂volume, x ∈ U)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {p q S : ℝ} (hpq : p.HolderConjugate q) (hd : (Fintype.card I : ℝ) = 2 * q)
    (hS : 0 ≤ S) (hSob : ScalarSobolevBound (I := I) p S)
    (hu_ne : inclusion I V u ≠ 0) :
    ∀ᵐ x ∂volume, inclusion I V u x ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  by_contra hzero
  have hpositive : 0 < volume {x | inclusion I V u x = 0} := bot_lt_iff_ne_bot.mpr hzero
  have hz := zero_of_positive_zero_measure V C κ hκ M hbound e A positive negative
    hCarleman hα hU hfull heigen C₀ hnegative hpq hd hS hSob hpositive
  apply hu_ne
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))] with x hx hzero
  exact hx.trans hzero.symm

end PfHk.PhysicalCarlemanInput
