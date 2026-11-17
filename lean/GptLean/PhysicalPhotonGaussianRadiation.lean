import GptLean.PhysicalGaussianTensorForms
import GptLean.PhysicalFockSplitFlip
import GptLean.PhysicalFockHardRadiationBound
import GptLean.PhysicalPhotonGaussian

/-!
The actual Gaussian hard fiber has exactly the hard radiation energy of
the source. A countable bounded-block representation of the radiation
form supplies the equality, including its domain and integrability content.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel PhotonLocalizationFockChannel
open TensorCoordinates PhysicalGaussianCoordinates
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

local instance radiationGeneratedComplete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (V : Submodule ℂ (Lp ℂ 2 μ)) :
    CompleteSpace (generatedSubspace μ V) := by
  unfold generatedSubspace
  infer_instance

private theorem tensorLift_apply_eq
    {Q S H ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
    [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (z : TensorSpace S H) :
    tensorLift b U z = tensorToL2 b U (tensorFlip z) := rfl

private theorem tensorToL2_submodule_squareSeries
    {Q E F ι : Type*} [MeasurableSpace Q] {μ : Measure Q}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (P : Submodule ℂ E) (S : Submodule ℂ F) [CompleteSpace P]
    (b : HilbertBasis ι ℂ S) (U : S ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (M : TensorSpace P S →ₗᵢ[ℂ] TensorSpace E F)
    (hM : ∀ (v : P) (s : S), M (tensor v s) = tensor v.val s.val)
    (A : ℕ → E →L[ℂ] E) (z : TensorSpace P S) :
    (∫⁻ q, ∑' n, ENNReal.ofReal (‖A n (tensorToL2 b U z q).val‖ ^ 2) ∂μ) =
      ∑' n, ENNReal.ofReal (‖retainedOperator (A n) (M z)‖ ^ 2) :=
  tensorToL2_squareSeries b U P.subtypeₗᵢ S.subtypeₗᵢ M hM A z

attribute [local irreducible] photonGaussianUnitary tensorLift tensorToL2

private theorem pair_tsum_eq (t : ℕ → ℕ → ℝ≥0∞) :
    (∑' n : ℕ, t n.unpair.1 n.unpair.2) = ∑' i, ∑' j, t i j :=
  (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => t p.1 p.2)).trans ENNReal.tsum_prod'

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)

include normal F in
theorem radiationForm_eq_familyBlocks (u : PhotonFock) :
    radiationForm u = ∑' n, ENNReal.ofReal (‖familyBlock radiationFamily n u‖ ^ 2) :=
  (radiationObservable_rankOne normal F u).symm.trans
    (squareSeriesForm_rankOne normal F (familyBlock radiationFamily) u)

include normal F in
private theorem radiationForm_eq_annihilation (u : PhotonFock) :
    radiationForm u = ∑' i, annihilationForm photonMeasure (radiationFamily i) u :=
  (radiationObservable_rankOne normal F u).symm.trans
    (familyObservable_rankOne normal F radiationFamily u)

include normal F in
theorem tensor_radiationFamily_coordinates (z : TensorSpace PhotonFock PhotonFock) :
    (∑' n, ENNReal.ofReal (‖retainedOperator (familyBlock radiationFamily n) z‖ ^ 2)) =
      ∑' a, radiationForm (environmentalCoordinates PhotonFock z a) := by
  have he := pair_tsum_eq (fun i n =>
    ENNReal.ofReal (‖retainedOperator (annihilationBlock photonMeasure n (radiationFamily i)) z‖ ^ 2))
  refine he.trans ?_
  change (∑' i, tensorAnnihilationForm photonMeasure (radiationFamily i) z) = _
  calc
    _ = ∑' i, ∑' a, annihilationForm photonMeasure (radiationFamily i)
        (environmentalCoordinates PhotonFock z a) :=
      tsum_congr (fun i => (tensorAnnihilationForm_coordinates photonMeasure
        (environmentalCoordinates PhotonFock) environmentalCoordinates_retainedOperator
          (radiationFamily i) z).symm)
    _ = ∑' a, ∑' i, annihilationForm photonMeasure (radiationFamily i)
        (environmentalCoordinates PhotonFock z a) := ENNReal.tsum_comm
    _ = _ := tsum_congr (fun a => (radiationForm_eq_annihilation normal F _).symm)

attribute [local irreducible] coefficients supportedFockEquivalence supportedTensorEmbedding
  flippedSupportedTensorEmbedding generatedSubspace

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (κ : ℝ) {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

include normal F in
theorem photonGaussianUnitary_radiation_integral (u : PhotonFock) :
    (∫⁻ ω, radiationForm ((photonGaussianUnitary BF κ W u ω).val) ∂W.space.measure) =
      ∑' a, radiationForm ((photonFactorization BF).factor
        (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
          (softMomentumSet_measurable κ).compl) u a) := by
  let z := tensorFlip (supportedFockEquivalence photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) (photonExponential BF) u)
  let M := flippedSupportedTensorEmbedding photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ)
  have hU := (photonGaussianUnitary_apply BF κ W u).trans
    (tensorLift_apply_eq (softBasis κ) W.unitary _)
  calc
    _ = ∫⁻ ω, radiationForm ((tensorToL2 (softBasis κ) W.unitary z ω).val) ∂W.space.measure :=
      congrArg (fun v : Lp (HardPhotonFock κ) 2 W.space.measure =>
        ∫⁻ ω, radiationForm ((v ω).val) ∂W.space.measure) hU
    _ = ∫⁻ ω, ∑' n, ENNReal.ofReal
        (‖familyBlock radiationFamily n (tensorToL2 (softBasis κ) W.unitary z ω).val‖ ^ 2)
          ∂W.space.measure := lintegral_congr (fun _ => radiationForm_eq_familyBlocks normal F _)
    _ = ∑' n, ENNReal.ofReal (‖retainedOperator (familyBlock radiationFamily n) (M z)‖ ^ 2) :=
      tensorToL2_submodule_squareSeries
        (generatedFockSubspace (hardOnePhoton κ)) (generatedFockSubspace (softOnePhoton κ))
        (softBasis κ) W.unitary M
        (flippedSupportedTensorEmbedding_tensor photonMeasure (softMomentumSet κ)
          (softMomentumSet_measurable κ)) (familyBlock radiationFamily) z
    _ = ∑' a, radiationForm (environmentalCoordinates PhotonFock (M z) a) :=
      tensor_radiationFamily_coordinates normal F (M z)
    _ = _ := congrArg (fun t : TensorSpace PhotonFock PhotonFock =>
        ∑' a, radiationForm (environmentalCoordinates PhotonFock t a))
      (flippedSupportedTensorEmbedding_split photonMeasure (softMomentumSet κ)
        (softMomentumSet_measurable κ) (photonExponential BF) u)

include normal F C in
/-- Exact scalar form identity for the actual hard Gaussian fiber. -/
theorem photonGaussianUnitary_hard_radiation (q : RadiationGraphSpace) :
    (∫⁻ ω, radiationForm ((photonGaussianUnitary BF κ W (radiationGraphInclusion q) ω).val)
      ∂W.space.measure) = ENNReal.ofReal (‖hardRadiationRoot κ q‖ ^ 2) :=
  (photonGaussianUnitary_radiation_integral normal F BF κ W (radiationGraphInclusion q)).trans
    (hardSplit_radiation_sum normal F BF C κ q)

include normal F C in
theorem photonGaussianUnitary_hard_radiation_finite (q : RadiationGraphSpace) :
    (∫⁻ ω, radiationForm ((photonGaussianUnitary BF κ W (radiationGraphInclusion q) ω).val)
      ∂W.space.measure) < ⊤ := by
  rw [photonGaussianUnitary_hard_radiation normal F BF C κ W]
  exact ENNReal.ofReal_lt_top

end GptLean.PhysicalFock
