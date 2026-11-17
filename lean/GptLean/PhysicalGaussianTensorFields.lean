import GptLean.PhysicalGaussianCoordinates

/-!
Scalar multiplication intertwining extends to an arbitrary separable
Hilbert tensor factor. The proof compares actual Hilbert coefficients,
uses their simultaneous almost-everywhere representatives, and recovers
the fiber vector by completeness of the Hilbert basis.
-/

noncomputable section

namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Topology PhysicalFock.TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {Q S H ι η : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (bS : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)

/-- Scalar realization in the first tensor factor, with the second factor
retained as the Bochner fiber. -/
def tensorLift : TensorSpace S H ≃ₗᵢ[ℂ] Lp H 2 μ :=
  tensorFlip.trans (tensorToL2 bS U)

omit [CompleteSpace S] in
theorem tensorLift_tensor (s : S) (h : H) :
    tensorLift bS U (tensor s h) = PhysicalL2HilbertSum.tensor (U s) h := by
  change tensorToL2 bS U (tensorFlip (tensor s h)) = _
  rw [tensorFlip_tensor, tensorToL2_tensor]

omit [CompleteSpace S] in
theorem tensorLift_tensor_ae (s : S) (h : H) :
    tensorLift bS U (tensor s h) =ᵐ[μ] fun q => U s q • h := by
  rw [tensorLift_tensor]
  exact PhysicalL2HilbertSum.tensor_ae (U s) h

omit [CompleteSpace S] [CompleteSpace H] in
private theorem tensor_ext {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (L R : TensorSpace S H →L[ℂ] Z)
    (h : ∀ s v, L (tensor s v) = R (tensor s v)) : L = R := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq L.continuous R.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
    | tmul s v => exact h s v
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw

variable (bH : HilbertBasis η ℂ H)

/-- Hilbert coefficients of the vector-valued realization are the scalar
realizations of the same tensor coefficients. -/
theorem tensorLift_coefficient (z : TensorSpace S H) (i : η) :
    (innerSL ℂ (bH i)).compLpL 2 μ (tensorLift bS U z) =
      U (coefficients bH z i) := by
  let L : TensorSpace S H →L[ℂ] Lp ℂ 2 μ :=
    ((innerSL ℂ (bH i)).compLpL 2 μ).comp (tensorLift bS U).toContinuousLinearEquiv.toContinuousLinearMap
  let R : TensorSpace S H →L[ℂ] Lp ℂ 2 μ :=
    U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((lp.evalCLM ℂ (fun _ : η => S) 2 i).comp
        (coefficients bH).toContinuousLinearEquiv.toContinuousLinearMap)
  have he : L = R := tensor_ext L R (by
    intro s h
    change (innerSL ℂ (bH i)).compLpL 2 μ (tensorLift bS U (tensor s h)) =
      U (coefficients bH (tensor s h) i)
    rw [coefficients_tensor, map_smul]
    apply Lp.ext
    filter_upwards [(innerSL ℂ (bH i)).coeFn_compLpL (tensorLift bS U (tensor s h)),
      tensorLift_tensor_ae bS U s h, Lp.coeFn_smul ⟪bH i, h⟫_ℂ (U s)] with q hL hT hR
    rw [hL, hT, hR]
    change ⟪bH i, U s q • h⟫_ℂ = ⟪bH i, h⟫_ℂ * U s q
    rw [inner_smul_right]
    exact mul_comm _ _)
  exact congrArg (fun A : TensorSpace S H →L[ℂ] Lp ℂ 2 μ => A z) he

theorem tensorLift_coefficient_ae (z : TensorSpace S H) (i : η) :
    (fun q => ⟪bH i, tensorLift bS U z q⟫_ℂ) =ᵐ[μ]
      fun q => U (coefficients bH z i) q := by
  have h := (innerSL ℂ (bH i)).coeFn_compLpL (tensorLift bS U z)
  rw [tensorLift_coefficient bS U bH z i] at h
  exact h.symm

/-- Scalar identities for every hard coefficient imply the full Bochner
field identity, with one common exceptional null set. -/
theorem tensorLift_intertwining [Countable η] (a : Q → ℂ)
    (u v : TensorSpace S H)
    (h : ∀ i, U (coefficients bH v i) =ᵐ[μ]
      fun q => a q * U (coefficients bH u i) q) :
    tensorLift bS U v =ᵐ[μ] fun q => a q • tensorLift bS U u q := by
  filter_upwards [ae_all_iff.mpr (tensorLift_coefficient_ae bS U bH u),
    ae_all_iff.mpr (tensorLift_coefficient_ae bS U bH v), ae_all_iff.mpr h]
    with q hu hv hq
  apply bH.repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_smul_right,
    hu i, hv i, hq i]

end GptLean.PhysicalGaussianCoordinates
