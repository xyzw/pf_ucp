import GptLean.PhysicalFockOrthogonalSplit

/-!
Vacuum insertion for the constructed orthogonal momentum factorization.
The inverse split applied to soft vacuum and a hard-supported Fock vector
is exactly that same vector in the ambient Fock space. Thus insertion is
an actual isometry on the same photon model, with no factorization or
vacuum-identification premise.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel Filter Topology TensorCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section TensorHelpers

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private def tensorUnitIsometry (u : H) (hu : ‖u‖ = 1) : K →ₗᵢ[ℂ] TensorSpace H K :=
  (tensor u).toLinearMap.isometryOfInner (fun v w => by
    change ⟪tensor u v, tensor u w⟫_ℂ = _
    rw [tensor_inner, inner_self_eq_one_of_norm_eq_one hu, one_mul])

private theorem tensorUnitIsometry_apply (u : H) (hu : ‖u‖ = 1) (v : K) :
    tensorUnitIsometry u hu v = tensor u v := rfl

end TensorHelpers

section IsometryHelpers

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

private theorem inverse_eq_of_image_eq (U : H ≃ₗᵢ[ℂ] K)
    (u : H) (v : K) (h : U u = v) : U.symm v = u :=
  (congrArg U.symm h.symm).trans (U.symm_apply_apply u)

private theorem eq_of_embedding_chain {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (I : K →ₗᵢ[ℂ] Z) (x y : K) (z w : Z)
    (hx : I x = z) (hz : z = w) (hy : I y = w) : x = y :=
  I.injective (hx.trans (hz.trans hy.symm))

private def inverseComposition {J : Type*}
    [NormedAddCommGroup J] [NormedSpace ℂ J]
    (U : H ≃ₗᵢ[ℂ] K) (V : J →ₗᵢ[ℂ] K) : J →ₗᵢ[ℂ] H :=
  U.symm.toLinearIsometry.comp V

private theorem inverse_comp_apply_of_image_eq {J : Type*}
    [NormedAddCommGroup J] [NormedSpace ℂ J]
    (U : H ≃ₗᵢ[ℂ] K) (V : J →ₗᵢ[ℂ] K)
    (j : J) (u : H) (h : U u = V j) :
    inverseComposition U V j = u :=
  inverse_eq_of_image_eq U u (V j) h

end IsometryHelpers

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (s : Set Ω) (hs : MeasurableSet s) (B : ConcreteExponentialLaw μ)

/-- The vacuum belongs to every generated Fock subspace. -/
def generatedVacuum (V : Submodule ℂ (Lp ℂ 2 μ)) : generatedSubspace μ V :=
  ⟨creationWord μ [], creationWord_mem_generated μ V [] (by simp)⟩

@[simp] theorem generatedVacuum_norm (V : Submodule ℂ (Lp ℂ 2 μ)) :
    ‖generatedVacuum μ V‖ = 1 := vacuum_norm μ

/-- Hard-supported vectors split with an actual vacuum in the soft factor. -/
theorem split_hard_supported
    (v : generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl)) :
    B.split μ (MomentumSplit.split μ s hs) v.val =
      tensor (creationWord μ []) v.val := by
  let D := (B.split μ (MomentumSplit.split μ s hs)).toContinuousLinearMap -
    tensor (creationWord μ [])
  have hspan : Submodule.span ℂ {z | ∃ w : List (Lp ℂ 2 μ),
      (∀ f ∈ w, f ∈ MomentumSplit.supported μ sᶜ hs.compl) ∧
      z = creationWord μ w} ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change B.split μ (MomentumSplit.split μ s hs) (creationWord μ w) -
      tensor (creationWord μ []) (creationWord μ w) = 0
    apply sub_eq_zero.mpr
    exact (B.split_word μ (MomentumSplit.split μ s hs) w).trans
      (by simpa only [List.nil_append] using
        splitCreationTensor_append_supported μ s hs [] w (by simp) hw)
  have hv := (closure_minimal hspan D.isClosed_ker) v.property
  exact sub_eq_zero.mp (show D v.val = 0 from hv)

/-- The supported tensor product uses the same vacuum and hard vector. -/
theorem supportedFockEquivalence_hard
    (v : generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl)) :
    supportedFockEquivalence μ s hs B v.val =
      tensor (generatedVacuum μ (MomentumSplit.supported μ s hs)) v := by
  exact eq_of_embedding_chain (supportedTensorEmbedding μ s hs) _ _ _ _
    (supportedFockEquivalence_embedding μ s hs B v.val)
    (split_hard_supported μ s hs B v)
    (supportedTensorEmbedding_tensor μ s hs
      (generatedVacuum μ (MomentumSplit.supported μ s hs)) v)

/-- Tensoring with the unit soft vacuum is an isometry. -/
def softVacuumTensor :
    generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl) →ₗᵢ[ℂ]
      SupportedFockTensor μ s hs :=
  tensorUnitIsometry (generatedVacuum μ (MomentumSplit.supported μ s hs)) (generatedVacuum_norm μ _)

private theorem softVacuumTensor_apply
    (v : generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl)) :
    softVacuumTensor μ s hs v =
      tensor (generatedVacuum μ (MomentumSplit.supported μ s hs)) v :=
  tensorUnitIsometry_apply _ _ v

attribute [local irreducible] supportedFockEquivalence softVacuumTensor

/-- Vacuum insertion is constructed through the inverse orthogonal split. -/
def hardVacuumEmbedding :
    generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl) →ₗᵢ[ℂ] Fock μ :=
  inverseComposition (H := Fock μ) (K := SupportedFockTensor μ s hs)
    (J := generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
    (supportedFockEquivalence μ s hs B) (softVacuumTensor μ s hs)

/-- In the original Fock space insertion is exactly the support inclusion. -/
@[simp] theorem hardVacuumEmbedding_apply
    (v : generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl)) :
    hardVacuumEmbedding μ s hs B v = v.val :=
  inverse_comp_apply_of_image_eq (H := Fock μ) (K := SupportedFockTensor μ s hs)
    (J := generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
    (supportedFockEquivalence μ s hs B)
    (softVacuumTensor μ s hs) v v.val
    ((supportedFockEquivalence_hard μ s hs B v).trans (softVacuumTensor_apply μ s hs v).symm)

/-- Soft-vacuum insertion at a physical frequency cutoff. -/
def hardPhotonVacuumEmbedding (BF : StandardSymmetricFockExponential) (κ : ℝ) :
    generatedFockSubspace (hardOnePhoton κ) →ₗᵢ[ℂ] PhotonFock :=
  hardVacuumEmbedding photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)
    (photonExponential BF)

@[simp] theorem hardPhotonVacuumEmbedding_apply
    (BF : StandardSymmetricFockExponential) (κ : ℝ)
    (v : generatedFockSubspace (hardOnePhoton κ)) :
    hardPhotonVacuumEmbedding BF κ v = v.val :=
  hardVacuumEmbedding_apply photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (photonExponential BF) v

end GptLean.PhysicalFock
