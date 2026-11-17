import PfHk.PhysicalCutoffLocality

/-! Transfer of a local weak equation to coefficients truncated outside
the vector support. The proof tests the original equation with an actual
scalar-localized form vector and computes the cutoff commutator. -/

noncomputable section
namespace PfHk.PhysicalLocalTruncation

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
  PfHk.PhysicalCoefficientLocality PfHk.PhysicalCutoffLocality
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  externalCovariant externalForm IsOperatorPair IsLocalOperatorPair
  PhysicalPFScalarMultiplier.multiply PhysicalPFReference.referenceSubspace
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  PfHk.PhysicalCutoffCommutator.commutator

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
  (A A' : I → Position I → ℝ) (positive negative positive' negative' : Position I → ℝ)

theorem operatorPair_of_local
    (a : TwiceDifferentiableMultiplier I) {s : Set (Position I)}
    (hs : ∀ x, x ∉ s → a.scalar.weight x = 0)
    (hA : ∀ i x, a.scalar.weight x ≠ 0 → A i x = A' i x)
    (hp : ∀ x, a.scalar.weight x ≠ 0 → positive x = positive' x)
    (hn : ∀ x, a.scalar.weight x ≠ 0 → negative x = negative' x)
    (u : Reference I V) (hu : ExternalDomain V A positive negative u)
    (hu' : ExternalDomain V A' positive' negative' u)
    (hU : Agreement A A' positive negative positive' negative' (inclusion I V u))
    (hfix : a.scalar.multiplier (inclusion I V u) = inclusion I V u)
    (hfirst : ∀ i, (a.derivative i).multiplier (inclusion I V u) = 0)
    (hsecond : ∀ i, (a.derivative i).derivativeMultiplier i (inclusion I V u) = 0)
    (f : WaveSpace I)
    (hf : IsLocalOperatorPair V C κ hκ M hbound e A positive negative s u hu f) :
    IsOperatorPair V C κ hκ M hbound e A' positive' negative' u hu' (a.scalar.multiplier f) := by
  unfold IsOperatorPair
  unfold IsLocalOperatorPair at hf
  intro v hv
  let av := PhysicalPFScalarMultiplier.multiply V a.scalar v
  have hav := agreement_localize V A A' positive negative positive' negative' a.scalar v hA hp hn
  have hv' : ExternalDomain V A positive negative av :=
    domain_congr V A' A positive' negative' positive negative av (hv.localize V a.scalar)
      (Agreement.symm A A' positive negative positive' negative' hav)
  have htest := hf av hv' (localized_supported V a.scalar hs v)
  have hform := form_congr V A A' positive negative positive' negative' C κ hκ M hbound e
    av u hv' hu (hv.localize V a.scalar) hu' hav hU
  have hzero := commutator_zero V C κ hκ M hbound e A' positive' negative' a u hu' hfirst hsecond
  have hproduct := form_commutator V C κ hκ M hbound e A' positive' negative' a u v hu' hv
  have hfixed : (⟨PhysicalPFScalarMultiplier.multiply V a.scalar u, hu'.localize V a.scalar⟩ :
      {w : Reference I V // ExternalDomain V A' positive' negative' w}) = ⟨u, hu'⟩ :=
    Subtype.ext (reference_multiply_eq_of_value V a.scalar u u hfix)
  have hleft := congrArg (fun z : {w : Reference I V // ExternalDomain V A' positive' negative' w} =>
    externalForm V C κ hκ M hbound e A' positive' negative' v z.val hv z.property) hfixed
  have herr : ⟪inclusion I V v, PfHk.PhysicalCutoffCommutator.commutator V C κ hκ M hbound e
      A' positive' negative' a u hu'⟫_ℂ = 0 :=
    (congrArg (fun z : WaveSpace I => ⟪inclusion I V v, z⟫_ℂ) hzero).trans (inner_zero_right _)
  have hcut : externalForm V C κ hκ M hbound e A' positive' negative' v u hv hu' =
      externalForm V C κ hκ M hbound e A' positive' negative' av u (hv.localize V a.scalar) hu' :=
    (hleft.symm.trans hproduct).trans
      ((congrArg (fun z : ℂ => externalForm V C κ hκ M hbound e A' positive' negative'
        av u (hv.localize V a.scalar) hu' + z) herr).trans (add_zero _))
  have hpair : ⟪inclusion I V av, f⟫_ℂ = ⟪inclusion I V v, a.scalar.multiplier f⟫_ℂ :=
    (congrArg (fun z : WaveSpace I => ⟪z, f⟫_ℂ)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar v)).trans
      (a.scalar.multiplier_symmetric (H := PhotonFock) (inclusion I V v) f).symm
  exact hcut.trans (hform.symm.trans (htest.trans hpair))

end PfHk.PhysicalLocalTruncation
