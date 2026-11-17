import GptLean.PhysicalGaussianObservables
import GptLean.PhysicalPhotonMarginal

/-!
Bounded observable equality identifies the actual complementary photon
channel with the Gaussian source on every positive normal state.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhysicalNormalTrace PhysicalPhotonMarginal
  PhotonLocalizationChannel PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] observableGeneratedComplete

private def submoduleCompression {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : Submodule ℂ E) [CompleteSpace P]
    (A : E →L[ℂ] E) : P →L[ℂ] P :=
  P.subtypeₗᵢ.toContinuousLinearMap.adjoint.comp (A.comp P.subtypeₗᵢ.toContinuousLinearMap)

private theorem submoduleCompression_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : Submodule ℂ E) [CompleteSpace P]
    (A : E →L[ℂ] E) (v : P) :
    ⟪v, submoduleCompression P A v⟫_ℂ = ⟪v.val, A v.val⟫_ℂ :=
  P.subtypeₗᵢ.toContinuousLinearMap.adjoint_inner_right v (A v.val)

private theorem unitarySubmoduleCompression_inner {Q H E : Type*} [MeasurableSpace Q]
    {μ : Measure Q} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Submodule ℂ E) [CompleteSpace P] (U : H ≃ₗᵢ[ℂ] Lp P 2 μ)
    (A : E →L[ℂ] E) (u : H) :
    ⟪u, unitaryTest U (submoduleCompression P A) u⟫_ℂ =
      ∫ q, ⟪(U u q).val, A (U u q).val⟫_ℂ ∂μ := by
  have h := (unitary_tested_current U (submoduleCompression P A) u u).2
  exact h.trans (integral_congr_ae (Filter.Eventually.of_forall
    fun _ => submoduleCompression_inner P A _))

attribute [local irreducible] photonGaussianUnitary unitaryTest

variable (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

set_option backward.isDefEq.respectTransparency.types true in
/-- Compression of an actual full photon observable to the hard photon space. -/
def hardCompression (A : PhotonFock →L[ℂ] PhotonFock) : HardPhotonFock κ →L[ℂ] HardPhotonFock κ :=
  submoduleCompression (HardPhotonFock κ) A

set_option backward.isDefEq.respectTransparency.types true in
theorem hardCompression_inner (A : PhotonFock →L[ℂ] PhotonFock) (v : HardPhotonFock κ) :
    ⟪v, hardCompression κ A v⟫_ℂ = ⟪v.val, A v.val⟫_ℂ :=
  submoduleCompression_inner (HardPhotonFock κ) A v

set_option backward.isDefEq.respectTransparency.types true in
/-- The source observable is conjugation through the same Gaussian unitary. -/
def gaussianObservable (A : PhotonFock →L[ℂ] PhotonFock) : PhotonFock →L[ℂ] PhotonFock :=
  unitaryTest (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
    (μ := W.space.measure) (photonGaussianUnitary BF κ W) (hardCompression κ A)

set_option backward.isDefEq.respectTransparency.types true in
theorem gaussianObservable_inner (A : PhotonFock →L[ℂ] PhotonFock) (u : PhotonFock) :
    ⟪u, gaussianObservable BF κ W A u⟫_ℂ =
      ∫ q, ⟪(photonGaussianUnitary BF κ W u q).val,
        A (photonGaussianUnitary BF κ W u q).val⟫_ℂ ∂W.space.measure :=
  unitarySubmoduleCompression_inner (Q := W.space.Q) (H := PhotonFock)
    (E := PhotonFock) (μ := W.space.measure) (HardPhotonFock κ)
    (photonGaussianUnitary BF κ W) A u

def hardChannelIsometry : KrausIsometry PhotonFock :=
  (photonFactorization BF).factor (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl)

variable (B : StandardNormalTraceBackground)

/-- The equality uses the actual normal extension of the Fock factorization. -/
theorem gaussianObservable_channel (A : PhotonFock →L[ℂ] PhotonFock)
    {x : B.Trace PhotonFock} (hx : x ∈ (B.realization PhotonFock).rank.positive) :
    (B.realization PhotonFock).functional.repr
      (B.normal.extend (hardChannelIsometry BF κ) x) A =
        (B.realization PhotonFock).functional.repr x (gaussianObservable BF κ W A) := by
  apply partialTrace_evaluation B (hardChannelIsometry BF κ) A
    (gaussianObservable BF κ W A) _ hx
  intro u
  have hs := (B.realization PhotonFock).functional.observable_hasSum
    (pure_hasSum (B.realization PhotonFock).rank (hardChannelIsometry BF κ) u) A
  rw [gaussianObservable_inner BF κ W A u, photonGaussianUnitary_observable BF κ W A u]
  exact hs.summable.hasSum

variable {X : Type} [MeasurableSpace X] (ν : Measure X) [IsSeparable ν]

/-- The target is the actual hard channel applied to the original photon marginal. -/
def hardTargetTrace : B.Trace (Lp PhotonFock 2 ν) →L[ℝ] B.Trace PhotonFock :=
  (B.normal.extend (hardChannelIsometry BF κ)).comp (marginal B ν)

theorem hardTargetTrace_positive {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive) :
    hardTargetTrace BF κ B ν x ∈ (B.realization PhotonFock).rank.positive :=
  B.normal.positive (hardChannelIsometry BF κ) (marginal_positive B ν hx)

theorem hardTargetTrace_evaluation (A : PhotonFock →L[ℂ] PhotonFock)
    {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive) :
    (B.realization PhotonFock).functional.repr (hardTargetTrace BF κ B ν x) A =
      (B.realization (Lp PhotonFock 2 ν)).functional.repr x
        ((gaussianObservable BF κ W A).compLpL 2 ν) :=
  (gaussianObservable_channel BF κ W B A (marginal_positive B ν hx)).trans
    (marginal_evaluation B ν (gaussianObservable BF κ W A) hx)

set_option backward.isDefEq.respectTransparency.types true in
theorem hardTargetTrace_source_hasSum (A : PhotonFock →L[ℂ] PhotonFock)
    {v : ℕ → Lp PhotonFock 2 ν} {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (hv : HasSum (fun n => (B.realization (Lp PhotonFock 2 ν)).rank.rankOne (v n)) x) :
    HasSum (fun n => ⟪v n, (gaussianObservable BF κ W A).compLpL 2 ν (v n)⟫_ℂ)
      ((B.realization PhotonFock).functional.repr (hardTargetTrace BF κ B ν x) A) := by
  have hs : HasSum (fun n => ⟪v n, (gaussianObservable BF κ W A).compLpL 2 ν (v n)⟫_ℂ)
      ((B.realization (Lp PhotonFock 2 ν)).functional.repr x
        ((gaussianObservable BF κ W A).compLpL 2 ν)) :=
    (B.realization (Lp PhotonFock 2 ν)).functional.observable_hasSum hv _
  exact (congrArg (fun z : ℂ =>
    HasSum (fun n => ⟪v n, (gaussianObservable BF κ W A).compLpL 2 ν (v n)⟫_ℂ) z)
      (hardTargetTrace_evaluation BF κ W B ν A hx)).mpr hs

end GptLean.PhysicalFock
