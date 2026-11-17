import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalFockChannelVacuum
import GptLean.PhysicalFockOrthogonalSplit
import GptLean.PhysicalFockSupportLift

/-!
The soft field acts on exactly the soft coefficients of the constructed
orthogonal Fock split. The channel vacuum residual vanishes for the
orthogonal soft projection. Bounded tensor contractions then transfer the
actual sector graph from environmental coordinates to arbitrary hard
Hilbert coefficients.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology TensorCoordinates PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section TensorContraction

variable {H K Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

private theorem tensor_clm_ext (L R : TensorSpace H K →L[ℂ] Z)
    (h : ∀ u v, L (tensor u v) = R (tensor u v)) : L = R := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq L.continuous R.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [UniformSpace.Completion.coe_zero, map_zero]
    | tmul u v => exact h u v
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw

variable [CompleteSpace H]

def tensorContraction (h : K) : TensorSpace H K →L[ℂ] H :=
  (tensor.flip h).adjoint

theorem tensorContraction_tensor (h : K) (u : H) (v : K) :
    tensorContraction h (tensor u v) = ⟪h, v⟫_ℂ • u := by
  apply ext_inner_left ℂ
  intro z
  rw [tensorContraction, ContinuousLinearMap.adjoint_inner_right]
  change ⟪tensor z h, tensor u v⟫_ℂ = _
  rw [tensor_inner, inner_smul_right]
  ring

theorem tensorContraction_retainedOperator (h : K) (A : H →L[ℂ] H)
    (z : TensorSpace H K) :
    tensorContraction h (retainedOperator A z) = A (tensorContraction h z) := by
  have he : (tensorContraction h).comp (retainedOperator A) =
      A.comp (tensorContraction h) := tensor_clm_ext _ _ (by
    intro u v
    change tensorContraction h (retainedOperator A (tensor u v)) =
      A (tensorContraction h (tensor u v))
    rw [retainedOperator_tensor, tensorContraction_tensor, tensorContraction_tensor, map_smul])
  exact congrArg (fun L : TensorSpace H K →L[ℂ] H => L z) he

private theorem tensorContraction_coordinate_relation
    (W : TensorSpace H K →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2)
    (hW : ∀ (A : H →L[ℂ] H) z a, W (retainedOperator A z) a = A (W z a))
    (A B : H →L[ℂ] H) (u v : TensorSpace H K)
    (h : ∀ a, A (W v a) = B (W u a)) (w : K) :
    A (tensorContraction w v) = B (tensorContraction w u) := by
  have he : retainedOperator A v = retainedOperator B u := by
    apply W.injective
    apply lp.ext
    funext a
    exact (hW A v a).trans ((h a).trans (hW B u a).symm)
  exact (tensorContraction_retainedOperator w A v).symm.trans
    ((congrArg (tensorContraction w) he).trans (tensorContraction_retainedOperator w B u))

variable {H' K' ι : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [CompleteSpace H'] [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

theorem tensorContraction_embedding (I : H →ₗᵢ[ℂ] H') (J : K →ₗᵢ[ℂ] K')
    (E : TensorSpace H K →ₗᵢ[ℂ] TensorSpace H' K')
    (hE : ∀ u v, E (tensor u v) = tensor (I u) (J v))
    (b : HilbertBasis ι ℂ K) (z : TensorSpace H K) (i : ι) :
    tensorContraction (J (b i)) (E z) = I (coefficients b z i) := by
  let L := (tensorContraction (J (b i))).comp E.toContinuousLinearMap
  let R := I.toContinuousLinearMap.comp
    ((lp.evalCLM ℂ (fun _ : ι => H) 2 i).comp
      (coefficients b).toContinuousLinearEquiv.toContinuousLinearMap)
  have he : L = R := tensor_clm_ext L R (by
    intro u v
    change tensorContraction (J (b i)) (E (tensor u v)) = I (coefficients b (tensor u v) i)
    rw [hE, tensorContraction_tensor, coefficients_tensor, J.inner_map_map, map_smul])
  exact congrArg (fun F : TensorSpace H K →L[ℂ] H' => F z) he

end TensorContraction

/-- Tensor contraction commutes with an embedding of two closed subspaces,
stated directly in terms of their ambient values. -/
theorem tensorContraction_submodule_embedding
    {H K ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (S : Submodule ℂ H) (T : Submodule ℂ K) [CompleteSpace S]
    (E : TensorSpace S T →ₗᵢ[ℂ] TensorSpace H K)
    (hE : ∀ (u : S) (v : T), E (tensor u v) = tensor u.val v.val)
    (b : HilbertBasis ι ℂ T) (z : TensorSpace S T) (i : ι) :
    tensorContraction (b i).val (E z) = (coefficients b z i).val :=
  tensorContraction_embedding S.subtypeₗᵢ T.subtypeₗᵢ E hE b z i

private theorem eq_add_of_zero {H : Type*} [AddZeroClass H]
    {x y z : H} (h : x = y + z) (hz : z = 0) : x = y :=
  h.trans ((congrArg (fun w => y + w) hz).trans (add_zero y))

section Channel

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
  (f : Lp ℂ 2 photonMeasure) (k : WeightedPhotonKernel)
  (hk : (retainedMap j).adjoint f = k.val.1)

theorem channelField_segalGraph (q : RadiationGraphSpace) (a : ℕ) :
    SegalGraph photonMeasure f
      ((photonFactorization BF).factor j (radiationGraphInclusion q) a)
      (channelField BF C j f k hk q a) := by
  intro n
  cases n with
  | zero =>
    change annihilationSector photonMeasure 0 f
      ((photonFactorization BF).factor j (radiationGraphInclusion q) a 1) + 0 = _
    exact add_zero _
  | succ n => rfl

omit f hk in
theorem channelField_eq_factor_of_sameKernel
    (hk : (retainedMap j).adjoint k.val.1 = k.val.1) (q : RadiationGraphSpace) :
    channelField BF C j k.val.1 k hk q =
      (photonFactorization BF).factor j (kernelField C k q) := by
  have hn := channelVacuum_norm_sq BF C j k.val.1 k hk q
  rw [sub_self, zero_mul] at hn
  have hz : channelVacuum BF C j k.val.1 k hk q = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  exact eq_add_of_zero (channelField_eq_factor_add_vacuum BF C j k.val.1 k hk q) hz

end Channel

/-- The sector graph is independent of the environmental Hilbert basis. -/
theorem tensorContraction_segalGraph (f : Lp ℂ 2 photonMeasure)
    (u v : TensorSpace PhotonFock PhotonFock)
    (h : ∀ a, SegalGraph photonMeasure f
      (environmentalCoordinates PhotonFock u a) (environmentalCoordinates PhotonFock v a))
    (w : PhotonFock) :
    SegalGraph photonMeasure f (tensorContraction w u) (tensorContraction w v) := by
  intro n
  let A := photonSector photonMeasure n
  let B := (lp.singleContinuousLinearMap ℂ (Sector photonMeasure) 2 n).comp
    (segalCoordinate photonMeasure f n)
  have hc := tensorContraction_coordinate_relation (environmentalCoordinates PhotonFock)
    environmentalCoordinates_retainedOperator A B u v
    (fun a => congrArg (lp.single 2 n) (h a n)) w
  have hn := congrArg (fun x : PhotonFock => x n) hc
  change (lp.single 2 n (tensorContraction w v n)) n =
    (lp.single 2 n (segalCoordinate photonMeasure f n (tensorContraction w u))) n at hn
  simpa only [lp.single_apply_self] using hn

section Supported

local instance supportedGeneratedComplete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    CompleteSpace (generatedSubspace μ V) := by
  unfold generatedSubspace
  infer_instance

attribute [local irreducible] coefficients supportedFockEquivalence supportedTensorEmbedding
  tensorContraction generatedSubspace

private theorem tensorContraction_supportedTensorEmbedding_general
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (s : Set Ω) (hs : MeasurableSet s) {ι : Type*}
    (b : HilbertBasis ι ℂ (generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl)))
    (z : SupportedFockTensor μ s hs) (i : ι) :
    tensorContraction (b i).val (supportedTensorEmbedding μ s hs z) =
      (coefficients b z i).val :=
  tensorContraction_submodule_embedding (H := Fock μ) (K := Fock μ)
    (generatedSubspace μ (MomentumSplit.supported μ s hs))
    (generatedSubspace μ (MomentumSplit.supported μ sᶜ hs.compl))
    (supportedTensorEmbedding μ s hs) (supportedTensorEmbedding_tensor μ s hs) b z i

variable (κ : ℝ) {ι : Type*}
  (bH : HilbertBasis ι ℂ (generatedFockSubspace (hardOnePhoton κ)))

theorem tensorContraction_supportedTensorEmbedding
    (z : SupportedFockTensor photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
    (i : ι) :
    tensorContraction (bH i).val
      (supportedTensorEmbedding photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ) z) =
        (coefficients bH z i).val :=
  tensorContraction_supportedTensorEmbedding_general photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) bH z i

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

omit C in
theorem tensorContraction_split_eq_coefficient (u : PhotonFock) (i : ι) :
    tensorContraction (bH i).val
      ((photonExponential BF).split photonMeasure
        (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)) u) =
      (coefficients bH (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) u) i).val :=
  (congrArg (tensorContraction (bH i).val)
    (supportedFockEquivalence_embedding photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (photonExponential BF) u).symm).trans
    (tensorContraction_supportedTensorEmbedding κ bH _ i)

/-- The soft kernel is fixed by the actual adjoint retained momentum projection. -/
theorem retained_soft_adjoint_fixed (k : WeightedPhotonKernel)
    (hk : k.val.1 ∈ softOnePhoton κ) :
    (retainedMap (MomentumSplit.split photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ))).adjoint k.val.1 = k.val.1 := by
  change (MomentumSplit.projection photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ)).adjoint k.val.1 = k.val.1
  rw [MomentumSplit.projection_adjoint]
  exact MomentumSplit.projection_of_supported _ _ _ ⟨k.val.1, hk⟩

/-- Exact soft Segal graph on every hard coefficient of the same
constructed orthogonal Fock equivalence. -/
theorem supportedFockEquivalence_soft_segalGraph
    (k : WeightedPhotonKernel) (hk : k.val.1 ∈ softOnePhoton κ)
    (q : RadiationGraphSpace) (i : ι) :
    SegalGraph photonMeasure k.val.1
      (coefficients bH (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) (radiationGraphInclusion q)) i).val
      (coefficients bH (supportedFockEquivalence photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) (kernelField C k q)) i).val := by
  have hadj := retained_soft_adjoint_fixed κ k hk
  have hfield := channelField_eq_factor_of_sameKernel BF C
    (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ)) k hadj q
  have hgraph (a : ℕ) := channelField_segalGraph BF C
    (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
    k.val.1 k hadj q a
  have hgraph' (a : ℕ) : SegalGraph photonMeasure k.val.1
      ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
        (radiationGraphInclusion q) a)
      ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
        (kernelField C k q) a) :=
    (congrArg (fun v => SegalGraph photonMeasure k.val.1
      ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
        (radiationGraphInclusion q) a) (v a)) hfield).mp (hgraph a)
  have h := tensorContraction_segalGraph k.val.1
    ((photonExponential BF).split photonMeasure
      (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
      (radiationGraphInclusion q))
    ((photonExponential BF).split photonMeasure
      (MomentumSplit.split photonMeasure (softMomentumSet κ) (softMomentumSet_measurable κ))
      (kernelField C k q)) hgraph' (bH i).val
  exact (congrArg₂ (SegalGraph photonMeasure k.val.1)
    (tensorContraction_split_eq_coefficient κ bH BF (radiationGraphInclusion q) i)
    (tensorContraction_split_eq_coefficient κ bH BF (kernelField C k q) i)).mp h

end Supported

end GptLean.PhysicalFock
