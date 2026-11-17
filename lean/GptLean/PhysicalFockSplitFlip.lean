import GptLean.PhysicalGaussianCoordinates

/-!
Interchanging the complementary one-photon projections interchanges the
two factors of the same Fock exponential map. The proof uses the defining
creation-word polynomial and its dense span.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel TensorCoordinates PhysicalGaussianCoordinates
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem tensorFlip_apply_apply {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (z : TensorSpace H K) :
    tensorFlip (tensorFlip z) = z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (tensorFlip.continuous.comp tensorFlip.continuous) continuous_id
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
    | tmul u v => exact (congrArg tensorFlip (tensorFlip_tensor u v)).trans (tensorFlip_tensor v u)
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw

private theorem list_sum_map {I A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (L : A →+ B) (w : List I) (f : I → A) (g : I → B)
    (h : ∀ i, g i = L (f i)) : (w.map g).sum = L ((w.map f).sum) := by
  rw [map_list_sum, List.map_map]
  apply congrArg List.sum
  exact List.map_congr_left fun i _ => h i

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (j j' : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
  (hret : ∀ f, retainedMap j' f = discardedMap μ j f)
  (hdisc : ∀ f, discardedMap μ j' f = retainedMap j f)

include hret hdisc in
private theorem split_sum_swap {E : Type*} [AddCommMonoid E]
    (w : List (Lp ℂ 2 μ)) (T : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    ((splitAssignments μ j' w).map T).sum =
      ((splitAssignments μ j w).map (fun p => T (p.2, p.1))).sum := by
  induction w generalizing T with
  | nil => simp only [splitAssignments, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  | cons f w ih =>
    simp only [splitAssignments, List.map_append, List.sum_append, List.map_map,
      Function.comp_def]
    rw [ih, ih]
    simp only [hret, hdisc]
    exact add_comm _ _

variable [SigmaFinite μ]

include hret hdisc in
theorem splitCreationTensor_swap (w : List (Lp ℂ 2 μ)) :
    splitCreationTensor μ j' w = tensorFlip (splitCreationTensor μ j w) := by
  have h := split_sum_swap μ j j' hret hdisc w
    (fun p => tensor (creationWord μ p.1) (creationWord μ p.2))
  exact h.trans (list_sum_map tensorFlip.toLinearEquiv.toLinearMap.toAddMonoidHom
    (splitAssignments μ j w)
    (fun p => tensor (creationWord μ p.1) (creationWord μ p.2))
    (fun p => tensor (creationWord μ p.2) (creationWord μ p.1))
    (fun p => (tensorFlip_tensor (creationWord μ p.1) (creationWord μ p.2)).symm))

include hret hdisc in
theorem split_swap (B : ConcreteExponentialLaw μ) (u : Fock μ) :
    B.split μ j' u = tensorFlip (B.split μ j u) := by
  have he := B.split_unique μ j'
    (tensorFlip.toLinearIsometry.comp (B.split μ j)) (fun w =>
      (congrArg tensorFlip (B.split_word μ j w)).trans
        (splitCreationTensor_swap μ j j' hret hdisc w).symm)
  exact (congrArg (fun A : Fock μ →ₗᵢ[ℂ] TensorSpace (Fock μ) (Fock μ) => A u) he).symm

theorem split_complement_flip (s : Set Ω) (hs : MeasurableSet s)
    (B : ConcreteExponentialLaw μ) (u : Fock μ) :
    B.split μ (MomentumSplit.split μ sᶜ hs.compl) u =
      tensorFlip (B.split μ (MomentumSplit.split μ s hs) u) := by
  apply split_swap μ (MomentumSplit.split μ s hs)
    (MomentumSplit.split μ sᶜ hs.compl) _ _ B u
  · intro f
    rfl
  · intro f
    change MomentumSplit.projection μ sᶜᶜ hs.compl.compl f =
      MomentumSplit.projection μ s hs f
    simp only [compl_compl]

section Supported

variable (s : Set Ω) (hs : MeasurableSet s)

abbrev FlippedSupportedFockTensor := TensorSpace
  (generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
  (generatedSubspace μ (MomentumSplit.supported μ s hs))

def flippedSupportedTensorEmbedding : FlippedSupportedFockTensor μ s hs →ₗᵢ[ℂ]
    TensorSpace (Fock μ) (Fock μ) :=
  tensorFlip.toLinearIsometry.comp
    ((supportedTensorEmbedding μ s hs).comp tensorFlip.toLinearIsometry)

theorem flippedSupportedTensorEmbedding_tensor
    (u : generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
    (v : generatedSubspace μ (MomentumSplit.supported μ s hs)) :
    flippedSupportedTensorEmbedding μ s hs (tensor u v) = tensor u.val v.val :=
  (congrArg (fun z => tensorFlip (supportedTensorEmbedding μ s hs z))
    (tensorFlip_tensor u v)).trans
      ((congrArg tensorFlip (supportedTensorEmbedding_tensor μ s hs v u)).trans
        (tensorFlip_tensor v.val u.val))

theorem flippedSupportedTensorEmbedding_split (B : ConcreteExponentialLaw μ) (u : Fock μ) :
    flippedSupportedTensorEmbedding μ s hs
      (tensorFlip (supportedFockEquivalence μ s hs B u)) =
        B.split μ (MomentumSplit.split μ sᶜ hs.compl) u :=
  (congrArg (fun z => tensorFlip (supportedTensorEmbedding μ s hs z))
    (tensorFlip_apply_apply (supportedFockEquivalence μ s hs B u))).trans
      ((congrArg tensorFlip (supportedFockEquivalence_embedding μ s hs B u)).trans
        (split_complement_flip μ s hs B u).symm)

end Supported

end GptLean.PhysicalFock
