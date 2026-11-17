import GptLean.PhysicalFockSoftGaussianGraph
import GptLean.PhysicalFockSplitFlip
import GptLean.PhysicalFockHardOperators
import GptLean.PhysicalPhotonGaussian
import GptLean.PhysicalGaussianGraphTransport

/-!
The hard kernel acts through the actual hard fiber operator under the
same photon Gaussian unitary. Complementary split symmetry, zero channel
residual and closed-graph tensor transport supply the matching identity.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory TensorCoordinates PhotonLocalizationFockChannel PhysicalGaussianCoordinates
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

local instance hardGeneratedComplete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    CompleteSpace (generatedSubspace μ V) := by
  unfold generatedSubspace
  infer_instance

local instance hardGeneratedInnerProduct {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    InnerProductSpace ℂ (generatedSubspace μ V) :=
  Submodule.innerProductSpace (generatedSubspace μ V)

attribute [local irreducible] coefficients supportedFockEquivalence supportedTensorEmbedding
  flippedSupportedTensorEmbedding tensorContraction generatedSubspace
  photonGaussianUnitary tensorLift

private theorem tensorContraction_flipped_embedding
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (s : Set Ω) (hs : MeasurableSet s) {ι : Type*}
    (b : HilbertBasis ι ℂ (generatedSubspace μ (MomentumSplit.supported μ s hs)))
    (z : FlippedSupportedFockTensor μ s hs) (i : ι) :
    tensorContraction (b i).val (flippedSupportedTensorEmbedding μ s hs z) =
      (coefficients b z i).val :=
  tensorContraction_submodule_embedding (H := Fock μ) (K := Fock μ)
    (generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
    (generatedSubspace μ (MomentumSplit.supported μ s hs))
    (flippedSupportedTensorEmbedding μ s hs)
    (flippedSupportedTensorEmbedding_tensor μ s hs) b z i

variable (κ : ℝ) {ι : Type*} (bS : HilbertBasis ι ℂ (SoftPhotonFock κ))
  (BF : StandardSymmetricFockExponential)

theorem tensorContraction_hardSplit_eq_coefficient (u : PhotonFock) (i : ι) :
    tensorContraction (bS i).val
      ((photonExponential BF).split photonMeasure
        (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
          (softMomentumSet_measurable κ).compl) u) =
      (coefficients bS (tensorFlip (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) u)) i).val :=
  (congrArg (tensorContraction (bS i).val)
    (flippedSupportedTensorEmbedding_split photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) u).symm).trans
    (tensorContraction_flipped_embedding photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) bS _ i)

omit bS BF in
theorem retained_hard_adjoint_fixed (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ hardOnePhoton κ) :
    (retainedMap (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl)).adjoint k.val.1 = k.val.1 := by
  change (MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl).adjoint k.val.1 = k.val.1
  rw [MomentumSplit.projection_adjoint]
  exact MomentumSplit.projection_of_supported _ _ _ ⟨k.val.1, hk⟩

variable (C : CanonicalSectorCCR photonMeasure)

theorem supportedFockEquivalence_hard_segalGraph
    (k : WeightedPhotonKernel) (hk : k.val.1 ∈ hardOnePhoton κ)
    (q : RadiationGraphSpace) (i : ι) :
    SegalGraph photonMeasure k.val.1
      (coefficients bS (tensorFlip (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) (radiationGraphInclusion q))) i).val
      (coefficients bS (tensorFlip (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) (kernelField C k q))) i).val := by
  let j := MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl
  have hadj := retained_hard_adjoint_fixed κ k hk
  have hfield := channelField_eq_factor_of_sameKernel BF C j k hadj q
  have hgraph (a : ℕ) : SegalGraph photonMeasure k.val.1
      ((photonFactorization BF).factor j (radiationGraphInclusion q) a)
      ((photonFactorization BF).factor j (kernelField C k q) a) :=
    (congrArg (fun v => SegalGraph photonMeasure k.val.1
      ((photonFactorization BF).factor j (radiationGraphInclusion q) a) (v a)) hfield).mp
        (channelField_segalGraph BF C j k.val.1 k hadj q a)
  have h := tensorContraction_segalGraph k.val.1
    ((photonExponential BF).split photonMeasure j (radiationGraphInclusion q))
    ((photonExponential BF).split photonMeasure j (kernelField C k q)) hgraph (bS i).val
  exact (congrArg₂ (SegalGraph photonMeasure k.val.1)
    (tensorContraction_hardSplit_eq_coefficient κ bS BF (radiationGraphInclusion q) i)
    (tensorContraction_hardSplit_eq_coefficient κ bS BF (kernelField C k q) i)).mp h

omit bS in
/-- Almost-everywhere matching of the actual hard field graph. -/
theorem photonGaussianUnitary_hard_field_graph
    {J : RealStructure (softOnePhoton κ)}
    (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)
    (k : WeightedPhotonKernel) (hk : k.val.1 ∈ hardOnePhoton κ) (q : RadiationGraphSpace) :
    ∀ᵐ ω ∂W.space.measure,
      (photonGaussianUnitary BF κ W (radiationGraphInclusion q) ω,
        photonGaussianUnitary BF κ W (kernelField C k q) ω) ∈
          (hardFieldOperator κ k.val.1).graph := by
  have hclosed : IsClosed ((hardFieldOperator κ k.val.1).graph :
      Set (HardPhotonFock κ × HardPhotonFock κ)) := hardFieldOperator_closed κ k.val.1
  have h := tensorLift_mem_graph (H := HardPhotonFock κ) (K := HardPhotonFock κ)
    (softBasis κ) W.unitary (hardFieldOperator κ k.val.1).graph hclosed
    (supportedFockEquivalence photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) (radiationGraphInclusion q))
    (supportedFockEquivalence photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) (kernelField C k q))
    (fun i => (hardFieldOperator_graph_iff κ k.val.1 _ _).mpr
      (supportedFockEquivalence_hard_segalGraph κ (softBasis κ) BF C k hk q i))
  exact (congrArg₂ (fun u v : Lp (HardPhotonFock κ) 2 W.space.measure =>
      ∀ᵐ ω ∂W.space.measure, (u ω, v ω) ∈ (hardFieldOperator κ k.val.1).graph)
    (photonGaussianUnitary_apply BF κ W (radiationGraphInclusion q))
    (photonGaussianUnitary_apply BF κ W (kernelField C k q))).mpr h

end GptLean.PhysicalFock
