import GptLean.PhysicalGaussianTensorForms
import GptLean.PhysicalFockSplitFlip
import GptLean.PhysicalPhotonGaussian

/-!
Bounded observables of the actual hard Gaussian fibers agree with the
complementary Fock channel. The equality follows from the same tensor
isometries used to construct the Gaussian unitary.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalFock.TensorCoordinates
open scoped ENNReal InnerProductSpace TensorProduct

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Tensor

variable {Q S H E F ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace H] [CompleteSpace E] in
theorem target_embedding (I : H →ₗᵢ[ℂ] E) (J : S →ₗᵢ[ℂ] F)
    (M : TensorSpace H S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ v s, M (tensor v s) = tensor (I v) (J s))
    (z : TensorSpace H S) :
    M z = tensorTargetEmbedding J (fiberTensorMap I.toContinuousLinearMap z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq M.continuous
        ((tensorTargetEmbedding J).continuous.comp (fiberTensorMap I.toContinuousLinearMap).continuous)
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
    | tmul v s =>
      change M (tensor v s) = tensorTargetEmbedding J
        (fiberTensorMap I.toContinuousLinearMap (tensor v s))
      rw [hM, fiberTensorMap_tensor, tensorTargetEmbedding_tensor]
      rfl
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw

variable (bS : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)

private theorem tensorLift_flip_apply (z : TensorSpace S H) :
    tensorLift bS U z = tensorToL2 bS U (tensorFlip z) := rfl

/-- The integrated bounded quadratic observable is the retained tensor observable. -/
theorem tensorToL2_observable (I : H →ₗᵢ[ℂ] E) (J : S →ₗᵢ[ℂ] F)
    (M : TensorSpace H S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ v s, M (tensor v s) = tensor (I v) (J s))
    (A : E →L[ℂ] E) (z : TensorSpace H S) :
    (∫ q, ⟪I (tensorToL2 bS U z q), A (I (tensorToL2 bS U z q))⟫_ℂ ∂μ) =
      ⟪M z, retainedOperator A (M z)⟫_ℂ := by
  let L := I.toContinuousLinearMap
  let D := A.comp L
  have hI := tensorToL2_fiberTensorMap bS U L z
  have hA := tensorToL2_fiberTensorMap bS U D z
  calc
    _ = ⟪L.compLpL 2 μ (tensorToL2 bS U z),
        D.compLpL 2 μ (tensorToL2 bS U z)⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL (tensorToL2 bS U z),
        D.coeFn_compLpL (tensorToL2 bS U z)] with q hL hD
      rw [hL, hD]
      rfl
    _ = ⟪fiberTensorMap L z, fiberTensorMap D z⟫_ℂ :=
      (congrArg₂ (fun f g : Lp E 2 μ => ⟪f, g⟫_ℂ) hI.symm hA.symm).trans
        ((tensorToL2 (H := E) bS U).inner_map_map
          (fiberTensorMap L z) (fiberTensorMap D z))
    _ = ⟪tensorTargetEmbedding J (fiberTensorMap L z),
        tensorTargetEmbedding J (fiberTensorMap D z)⟫_ℂ :=
      ((tensorTargetEmbedding J).inner_map_map _ _).symm
    _ = _ := by
      rw [← target_embedding I J M hM z, ← retained_embedding I J M hM A z]

end Tensor

theorem tensorToL2_submodule_observable
    {Q E F ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (P : Submodule ℂ E) (S : Submodule ℂ F) [CompleteSpace P]
    (b : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (M : TensorSpace P S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ (v : P) (s : S), M (tensor v s) = tensor v.val s.val)
    (A : E →L[ℂ] E) (z : TensorSpace P S) :
    (∫ q, ⟪(tensorToL2 b U z q).val,
      A (tensorToL2 b U z q).val⟫_ℂ ∂μ) =
      ⟪M z, retainedOperator A (M z)⟫_ℂ :=
  tensorToL2_observable b U P.subtypeₗᵢ S.subtypeₗᵢ M hM A z

end GptLean.PhysicalGaussianCoordinates

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel TensorCoordinates PhysicalGaussianCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

local instance observableGeneratedComplete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    CompleteSpace (generatedSubspace μ V) := by
  unfold generatedSubspace
  infer_instance

attribute [local irreducible] coefficients supportedFockEquivalence supportedTensorEmbedding
  flippedSupportedTensorEmbedding photonGaussianUnitary tensorLift tensorToL2

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

/-- Every actual bounded photon observable has the complementary-channel value. -/
theorem photonGaussianUnitary_observable (A : PhotonFock →L[ℂ] PhotonFock)
    (u : PhotonFock) :
    (∫ q, ⟪(photonGaussianUnitary BF κ W u q).val,
      A (photonGaussianUnitary BF κ W u q).val⟫_ℂ ∂W.space.measure) =
    ∑' n, ⟪(photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
          (softMomentumSet_measurable κ).compl) u n,
      A ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
          (softMomentumSet_measurable κ).compl) u n)⟫_ℂ := by
  let z := tensorFlip (supportedFockEquivalence photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (photonExponential BF) u)
  let M := flippedSupportedTensorEmbedding photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ)
  have hU := (photonGaussianUnitary_apply BF κ W u).trans
    (tensorLift_flip_apply (softBasis κ) W.unitary _)
  calc
    _ = ∫ q, ⟪(tensorToL2 (softBasis κ) W.unitary z q).val,
        A (tensorToL2 (softBasis κ) W.unitary z q).val⟫_ℂ ∂W.space.measure :=
      congrArg (fun v : Lp (HardPhotonFock κ) 2 W.space.measure =>
        ∫ q, ⟪(v q).val, A (v q).val⟫_ℂ ∂W.space.measure) hU
    _ = ⟪M z, retainedOperator A (M z)⟫_ℂ :=
      tensorToL2_submodule_observable
        (generatedFockSubspace (hardOnePhoton κ)) (generatedFockSubspace (softOnePhoton κ))
        (softBasis κ) W.unitary M
        (flippedSupportedTensorEmbedding_tensor photonMeasure (softMomentumSet κ)
          (softMomentumSet_measurable κ)) A z
    _ = ∑' n, ⟪environmentalCoordinates PhotonFock (M z) n,
        A (environmentalCoordinates PhotonFock (M z) n)⟫_ℂ :=
      (environmentalCoordinates_observable_hasSum A (M z)).tsum_eq.symm
    _ = _ := congrArg (fun t : TensorSpace PhotonFock PhotonFock =>
        ∑' n, ⟪environmentalCoordinates PhotonFock t n,
          A (environmentalCoordinates PhotonFock t n)⟫_ℂ)
      (flippedSupportedTensorEmbedding_split photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) u)

end GptLean.PhysicalFock
