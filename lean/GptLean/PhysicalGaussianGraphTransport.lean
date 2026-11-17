import GptLean.PhysicalGaussianTensorFields
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
A scalar Hilbert-space realization preserves every closed linear relation
in the other tensor factor. Bounded fiber maps commute with realization.
Orthogonal projection then transfers a coefficientwise closed graph to
the actual almost-everywhere graph of the Bochner functions.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalFock.TensorCoordinates
open scoped ENNReal InnerProductSpace TensorProduct

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {Q S H K ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded map acts on the retained Hilbert factor of the completed tensor. -/
def fiberTensorMap (A : H →L[ℂ] K) : TensorSpace H S →L[ℂ] TensorSpace K S :=
  (A.rTensor S).completion

omit [CompleteSpace H] [CompleteSpace K] in
theorem fiberTensorMap_tensor (A : H →L[ℂ] K) (v : H) (s : S) :
    fiberTensorMap A (tensor v s) = tensor (A v) s := by
  rw [tensor_apply, fiberTensorMap, ContinuousLinearMap.completion_apply_coe]
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
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

variable (bS : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)

theorem coefficients_fiberTensorMap (A : H →L[ℂ] K) (z : TensorSpace H S) (i : ι) :
    coefficients bS (fiberTensorMap A z) i = A (coefficients bS z i) := by
  let L := ((lp.evalCLM ℂ (fun _ : ι => K) 2 i).comp
    (coefficients bS).toContinuousLinearEquiv.toContinuousLinearMap).comp (fiberTensorMap A)
  let R := A.comp ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).comp
    (coefficients bS).toContinuousLinearEquiv.toContinuousLinearMap)
  have he : L = R := tensor_clm_ext L R (by
    intro v s
    change coefficients bS (fiberTensorMap A (tensor v s)) i =
      A (coefficients bS (tensor v s) i)
    rw [fiberTensorMap_tensor, coefficients_tensor, coefficients_tensor, map_smul])
  exact congrArg (fun F : TensorSpace H S →L[ℂ] K => F z) he

/-- Naturality uses the actual scalar realization and the same bounded fiber map. -/
theorem tensorToL2_fiberTensorMap (A : H →L[ℂ] K) (z : TensorSpace H S) :
    tensorToL2 bS U (fiberTensorMap A z) = A.compLpL 2 μ (tensorToL2 bS U z) := by
  let L := (tensorToL2 bS U).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fiberTensorMap A)
  let R := (A.compLpL 2 μ).comp
    (tensorToL2 bS U).toContinuousLinearEquiv.toContinuousLinearMap
  have he : L = R := tensor_clm_ext L R (by
    intro v s
    change tensorToL2 bS U (fiberTensorMap A (tensor v s)) =
      A.compLpL 2 μ (tensorToL2 bS U (tensor v s))
    rw [fiberTensorMap_tensor]
    apply Lp.ext
    filter_upwards [tensorToL2_tensor_ae bS U (A v) s,
      A.coeFn_compLpL (tensorToL2 bS U (tensor v s)), tensorToL2_tensor_ae bS U v s]
      with q hL hR hT
    exact hL.trans ((map_smul A (U s q) v).symm.trans
      ((congrArg A hT.symm).trans hR.symm)))
  exact congrArg (fun F : TensorSpace H S →L[ℂ] Lp K 2 μ => F z) he

theorem tensorToL2_mem_submodule (W : Submodule ℂ H) (hW : IsClosed (W : Set H))
    (z : TensorSpace H S) (hz : ∀ i, coefficients bS z i ∈ W) :
    ∀ᵐ q ∂μ, tensorToL2 bS U z q ∈ W := by
  let : CompleteSpace W := hW.completeSpace_coe
  have hfix : fiberTensorMap W.starProjection z = z := by
    apply (coefficients bS).injective
    apply lp.ext
    funext i
    exact (coefficients_fiberTensorMap bS W.starProjection z i).trans
      (W.starProjection_eq_self_iff.mpr (hz i))
  have hfixL : W.starProjection.compLpL 2 μ (tensorToL2 bS U z) = tensorToL2 bS U z :=
    (tensorToL2_fiberTensorMap bS U W.starProjection z).symm.trans
      (congrArg (tensorToL2 bS U) hfix)
  have h := W.starProjection.coeFn_compLpL (tensorToL2 bS U z)
  rw [hfixL] at h
  filter_upwards [h] with q hq
  exact W.starProjection_eq_self_iff.mp hq.symm

private def graphLeft : H →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H K)

private def graphRight : K →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H K)

/-- Closed graph transport requires no boundedness of the graph operator. -/
theorem tensorToL2_mem_graph (M : Submodule ℂ (H × K))
    (hM : IsClosed (M : Set (H × K)))
    (u : TensorSpace H S) (v : TensorSpace K S)
    (hgraph : ∀ i, (coefficients bS u i, coefficients bS v i) ∈ M) :
    ∀ᵐ q ∂μ, (tensorToL2 bS U u q, tensorToL2 bS U v q) ∈ M := by
  let W : Submodule ℂ (WithLp 2 (H × K)) :=
    M.comap (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toLinearMap
  have hW : IsClosed (W : Set (WithLp 2 (H × K))) :=
    hM.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H K).continuous
  let L := graphLeft (H := H) (K := K)
  let R := graphRight (H := H) (K := K)
  let z := fiberTensorMap L u + fiberTensorMap R v
  have hz : ∀ i, coefficients bS z i ∈ W := by
    intro i
    change WithLp.ofLp (coefficients bS (fiberTensorMap L u + fiberTensorMap R v) i) ∈ M
    rw [map_add, lp.coeFn_add, Pi.add_apply, coefficients_fiberTensorMap,
      coefficients_fiberTensorMap]
    change (coefficients bS u i + 0, 0 + coefficients bS v i) ∈ M
    simpa only [add_zero, zero_add] using hgraph i
  have h := tensorToL2_mem_submodule bS U W hW z hz
  have he : tensorToL2 bS U z =
      L.compLpL 2 μ (tensorToL2 bS U u) + R.compLpL 2 μ (tensorToL2 bS U v) := by
    change tensorToL2 bS U (fiberTensorMap L u + fiberTensorMap R v) = _
    rw [map_add, tensorToL2_fiberTensorMap, tensorToL2_fiberTensorMap]
  rw [he] at h
  filter_upwards [h, L.coeFn_compLpL (tensorToL2 bS U u),
    R.coeFn_compLpL (tensorToL2 bS U v),
    Lp.coeFn_add (L.compLpL 2 μ (tensorToL2 bS U u))
      (R.compLpL 2 μ (tensorToL2 bS U v))] with q hq hL hR hadd
  change WithLp.ofLp ((_ + _ : Lp (WithLp 2 (H × K)) 2 μ) q) ∈ M at hq
  rw [hadd, Pi.add_apply, hL, hR] at hq
  change (tensorToL2 bS U u q + 0, 0 + tensorToL2 bS U v q) ∈ M at hq
  simpa only [add_zero, zero_add] using hq

/-- The same closed graph theorem in soft-first tensor coordinates. -/
theorem tensorLift_mem_graph (M : Submodule ℂ (H × K))
    (hM : IsClosed (M : Set (H × K)))
    (u : TensorSpace S H) (v : TensorSpace S K)
    (hgraph : ∀ i, (coefficients bS (tensorFlip u) i,
      coefficients bS (tensorFlip v) i) ∈ M) :
    ∀ᵐ q ∂μ, (tensorLift bS U u q, tensorLift bS U v q) ∈ M :=
  tensorToL2_mem_graph bS U M hM (tensorFlip u) (tensorFlip v) hgraph

end GptLean.PhysicalGaussianCoordinates
