import GptLean.PhysicalGaussianGraphTransport

/-!
Scalar realization preserves a countable sum of squared bounded fiber
operators, including infinite form values. The tensor embeddings are the
actual isometries, characterized on pure tensors.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalFock.TensorCoordinates
open scoped ENNReal InnerProductSpace TensorProduct

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {Q S H E F ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace H] [CompleteSpace E] in
private theorem tensor_clm_ext {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (L R : TensorSpace H S →L[ℂ] Z)
    (h : ∀ v s, L (tensor v s) = R (tensor v s)) : L = R := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq L.continuous R.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
    | tmul v s => exact h v s
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw

def tensorTargetEmbedding (J : S →ₗᵢ[ℂ] F) :
    TensorSpace E S →ₗᵢ[ℂ] TensorSpace E F :=
  (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) J).completion

omit [CompleteSpace H] [CompleteSpace E] in
theorem tensorTargetEmbedding_tensor (J : S →ₗᵢ[ℂ] F) (v : E) (s : S) :
    tensorTargetEmbedding J (tensor v s) = tensor v (J s) := by
  rw [tensor_apply, tensorTargetEmbedding, LinearIsometry.completion_apply_coe]
  rfl

omit [CompleteSpace H] [CompleteSpace E] in
theorem retained_embedding (I : H →ₗᵢ[ℂ] E) (J : S →ₗᵢ[ℂ] F)
    (M : TensorSpace H S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ v s, M (tensor v s) = tensor (I v) (J s))
    (A : E →L[ℂ] E) (z : TensorSpace H S) :
    retainedOperator A (M z) =
      tensorTargetEmbedding J (fiberTensorMap (A.comp I.toContinuousLinearMap) z) := by
  let L := (retainedOperator A).comp M.toContinuousLinearMap
  let R := (tensorTargetEmbedding J).toContinuousLinearMap.comp
    (fiberTensorMap (A.comp I.toContinuousLinearMap))
  have he : L = R := tensor_clm_ext L R (by
    intro v s
    change retainedOperator A (M (tensor v s)) =
      tensorTargetEmbedding J (fiberTensorMap (A.comp I.toContinuousLinearMap) (tensor v s))
    rw [hM, retainedOperator_tensor, fiberTensorMap_tensor, tensorTargetEmbedding_tensor]
    rfl)
  exact congrArg (fun T : TensorSpace H S →L[ℂ] TensorSpace E F => T z) he

omit [CompleteSpace H] [CompleteSpace E] in
theorem lp_square_lintegral (v : Lp E 2 μ) :
    (∫⁻ q, ENNReal.ofReal (‖v q‖ ^ 2) ∂μ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v))
    (ae_of_all _ fun _ => sq_nonneg _), ← PhotonKernelLocalization.l2_norm_sq_eq_integral]

variable (bS : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)

theorem tensorToL2_operator_form (I : H →ₗᵢ[ℂ] E) (J : S →ₗᵢ[ℂ] F)
    (M : TensorSpace H S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ v s, M (tensor v s) = tensor (I v) (J s))
    (A : E →L[ℂ] E) (z : TensorSpace H S) :
    (∫⁻ q, ENNReal.ofReal (‖A (I (tensorToL2 bS U z q))‖ ^ 2) ∂μ) =
      ENNReal.ofReal (‖retainedOperator A (M z)‖ ^ 2) := by
  let L := A.comp I.toContinuousLinearMap
  have hpoint := L.coeFn_compLpL (tensorToL2 bS U z)
  have hnorm : ‖L.compLpL 2 μ (tensorToL2 bS U z)‖ =
      ‖retainedOperator A (M z)‖ := by
    have ht := tensorToL2_fiberTensorMap bS U L z
    have he := retained_embedding I J M hM A z
    exact (congrArg norm ht).symm.trans
      (((tensorToL2 bS U).norm_map (fiberTensorMap L z)).trans
        (((tensorTargetEmbedding J).norm_map (fiberTensorMap L z)).symm.trans
          (congrArg norm he).symm))
  calc
    _ = ∫⁻ q, ENNReal.ofReal (‖L.compLpL 2 μ (tensorToL2 bS U z) q‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with q hq
      exact congrArg (fun v : E => ENNReal.ofReal (‖v‖ ^ 2)) hq.symm
    _ = ENNReal.ofReal (‖L.compLpL 2 μ (tensorToL2 bS U z)‖ ^ 2) := lp_square_lintegral _
    _ = _ := congrArg (fun r : ℝ => ENNReal.ofReal (r ^ 2)) hnorm

/-- Nonnegative Tonelli retains the full extended quadratic form. -/
theorem tensorToL2_squareSeries (I : H →ₗᵢ[ℂ] E) (J : S →ₗᵢ[ℂ] F)
    (M : TensorSpace H S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ v s, M (tensor v s) = tensor (I v) (J s))
    (A : ℕ → E →L[ℂ] E) (z : TensorSpace H S) :
    (∫⁻ q, ∑' n, ENNReal.ofReal (‖A n (I (tensorToL2 bS U z q))‖ ^ 2) ∂μ) =
      ∑' n, ENNReal.ofReal (‖retainedOperator (A n) (M z)‖ ^ 2) := by
  rw [lintegral_tsum]
  · exact tsum_congr (fun n => tensorToL2_operator_form bS U I J M hM (A n) z)
  · intro n
    exact (((((A n).comp I.toContinuousLinearMap).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (tensorToL2 bS U z))).norm.pow 2).aemeasurable).ennreal_ofReal

end GptLean.PhysicalGaussianCoordinates
