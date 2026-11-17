import GptLean.PhysicalFockVacuumOperator

/-!
The physical partial trace is split by the tensor vacuum projection.
The environmental coordinates may use any orthonormal basis. Orthogonality
eliminates the cross terms in every retained observable and identifies
the residual trace norm with the nonvacuum mass.
-/

noncomputable section
namespace GptLean.PhysicalFock.TensorGentle

open MeasureTheory UniformSpace TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

section Hilbert
variable {H Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (U : H →ₗᵢ[ℂ] Z)

private def projectionResidual : Z →L[ℂ] Z :=
  ContinuousLinearMap.id ℂ Z - U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint

private theorem isometry_adjoint (u : H) : U.toContinuousLinearMap.adjoint (U u) = u := by
  apply ext_inner_left ℂ
  intro v
  exact (U.toContinuousLinearMap.adjoint_inner_right v (U u)).trans (U.inner_map_map v u)

private theorem projection_contraction (z : Z) :
    U.toContinuousLinearMap.adjoint (projectionResidual U z) = 0 := by
  change U.toContinuousLinearMap.adjoint (z - U (U.toContinuousLinearMap.adjoint z)) = 0
  rw [map_sub, isometry_adjoint, sub_self]

private theorem projection_inner (z : Z) (u : H) :
    ⟪projectionResidual U z, U u⟫_ℂ = 0 := by
  exact (U.toContinuousLinearMap.adjoint_inner_left u (projectionResidual U z)).symm.trans
    ((congrArg (fun v : H => ⟪v, u⟫_ℂ) (projection_contraction U z)).trans (inner_zero_left _))

private theorem inner_projection (u : H) (z : Z) :
    ⟪U u, projectionResidual U z⟫_ℂ = 0 := by
  simpa only [inner_conj_symm, map_zero] using
    congrArg (starRingEnd ℂ) (projection_inner U z u)

private theorem projection_decomposition (z : Z) :
    z = U (U.toContinuousLinearMap.adjoint z) + projectionResidual U z := by
  change z = U (U.toContinuousLinearMap.adjoint z) + (z - U (U.toContinuousLinearMap.adjoint z))
  abel

private theorem projection_norm_sq (z : Z) :
    ‖projectionResidual U z‖ ^ 2 = ‖z‖ ^ 2 - ‖U.toContinuousLinearMap.adjoint z‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (U (U.toContinuousLinearMap.adjoint z)) (projectionResidual U z)
  rw [← projection_decomposition, U.norm_map, inner_projection] at h
  simp only [map_zero, mul_zero, add_zero] at h
  linarith only [h]

private theorem projection_commutes (A : H →L[ℂ] H) (R : Z →L[ℂ] Z)
    (hU : ∀ u, R (U u) = U (A u))
    (hK : ∀ z, U.toContinuousLinearMap.adjoint (R z) = A (U.toContinuousLinearMap.adjoint z))
    (z : Z) : projectionResidual U (R z) = R (projectionResidual U z) := by
  change R z - U (U.toContinuousLinearMap.adjoint (R z)) =
    R (z - U (U.toContinuousLinearMap.adjoint z))
  rw [hK, map_sub, hU]

private theorem projection_observable (A : H →L[ℂ] H) (R : Z →L[ℂ] Z)
    (hU : ∀ u, R (U u) = U (A u))
    (hK : ∀ z, U.toContinuousLinearMap.adjoint (R z) = A (U.toContinuousLinearMap.adjoint z))
    (z : Z) : ⟪z, R z⟫_ℂ =
      ⟪U.toContinuousLinearMap.adjoint z, A (U.toContinuousLinearMap.adjoint z)⟫_ℂ +
        ⟪projectionResidual U z, R (projectionResidual U z)⟫_ℂ := by
  have he := projection_decomposition U z
  conv_lhs => rw [he, map_add, inner_add_left, inner_add_right, inner_add_right]
  rw [hU, U.inner_map_map, projection_inner,
    ← projection_commutes U A R hU hK, inner_projection]
  simp
end Hilbert

private theorem tensor_contraction_commutes {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (K : TensorSpace H E →L[ℂ] H) (v : E)
    (hK : ∀ u w, K (tensor u w) = ⟪v, w⟫_ℂ • u)
    (A : H →L[ℂ] H) (z : TensorSpace H E) :
    K (retainedOperator A z) = A (K z) := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [Completion.coe_zero, map_zero]
    | tmul u w =>
      change K (retainedOperator A (tensor u w)) = A (K (tensor u w))
      rw [retainedOperator_tensor, hK, hK, map_smul]
    | add z z' hz hz' => simpa only [Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hz'

local notation "V" => VacuumOperator.insertion photonMeasure
local notation "K" => VacuumOperator.contraction photonMeasure
local notation "TensorFock" => TensorSpace PhotonFock PhotonFock

theorem contraction_insertion (u : PhotonFock) : K (V u) = u :=
  isometry_adjoint V u

def residual : TensorFock →L[ℂ] TensorFock := projectionResidual V

theorem contraction_residual (z : TensorFock) : K (residual z) = 0 :=
  projection_contraction V z

theorem residual_inner_insertion (z : TensorFock) (u : PhotonFock) :
    ⟪residual z, V u⟫_ℂ = 0 := projection_inner V z u

theorem insertion_inner_residual (u : PhotonFock) (z : TensorFock) :
    ⟪V u, residual z⟫_ℂ = 0 := inner_projection V u z

theorem tensor_decomposition (z : TensorFock) : z = V (K z) + residual z :=
  projection_decomposition V z

theorem residual_norm_sq (z : TensorFock) : ‖residual z‖ ^ 2 = ‖z‖ ^ 2 - ‖K z‖ ^ 2 :=
  projection_norm_sq V z

theorem retained_insertion (A : PhotonFock →L[ℂ] PhotonFock) (u : PhotonFock) :
    retainedOperator A (V u) = V (A u) :=
  retainedOperator_tensor A u (creationWord photonMeasure [])

theorem contraction_retained (A : PhotonFock →L[ℂ] PhotonFock) (z : TensorFock) :
    K (retainedOperator A z) = A (K z) :=
  tensor_contraction_commutes K (creationWord photonMeasure [])
    (VacuumOperator.contraction_tensor photonMeasure) A z

theorem residual_retained (A : PhotonFock →L[ℂ] PhotonFock) (z : TensorFock) :
    residual (retainedOperator A z) = retainedOperator A (residual z) :=
  projection_commutes V A (retainedOperator A) (retained_insertion A) (contraction_retained A) z

theorem observable_decomposition (A : PhotonFock →L[ℂ] PhotonFock) (z : TensorFock) :
    ⟪z, retainedOperator A z⟫_ℂ =
      ⟪K z, A (K z)⟫_ℂ + ⟪residual z, retainedOperator A (residual z)⟫_ℂ :=
  projection_observable V A (retainedOperator A) (retained_insertion A) (contraction_retained A) z

end GptLean.PhysicalFock.TensorGentle
