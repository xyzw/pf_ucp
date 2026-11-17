import GptLean.PhysicalRemovalHardTests

/-!
The real separating tests of the actual hard photon marginal. Their
source sums and rank-one formulas are derived from the normal trace
and the constructed Gaussian source.
-/

noncomputable section
namespace GptLean.PhysicalRemovalMarginal

open MeasureTheory Filter PhysicalFock PhysicalNormalTrace PhysicalGaussianCoordinates
  PhysicalPhotonMarginal RemovalSource
open scoped ENNReal InnerProductSpace BoundedContinuousFunction

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

private theorem compression_integral_congr {Y H K : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (μ : Measure Y) (J J' : H →L[ℂ] K) (hJ : ∀ u, J u = J' u)
    (A : K →L[ℂ] K) (v : Lp H 2 μ) :
    (∫ x, ⟪v x, (J.adjoint.comp (A.comp J)) (v x)⟫_ℂ ∂μ) =
      ∫ x, ⟪v x, (J'.adjoint.comp (A.comp J')) (v x)⟫_ℂ ∂μ := by
  have he : J = J' := ContinuousLinearMap.ext hJ
  rw [he]

variable (B : StandardNormalTraceBackground)

def realOperator (n : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  if (Nat.unpair n).2 = 0 then realOperatorPart (operators B (Nat.unpair n).1)
  else imaginaryOperatorPart (operators B (Nat.unpair n).1)

theorem realOperator_trace (n : ℕ) {x : B.Trace PhotonFock}
    (hx : x ∈ (B.realization PhotonFock).rank.positive) :
    (B.realization PhotonFock).functional.repr x (realOperator B n) =
      (realCoordinateTests n (photonCoordinates B x) : ℂ) := by
  have hcoordinate : photonCoordinates B x (Nat.unpair n).1 =
      (B.realization PhotonFock).functional.repr x (operators B (Nat.unpair n).1) :=
    photonCoordinates_apply B x (Nat.unpair n).1
  by_cases hn : (Nat.unpair n).2 = 0
  · simpa only [realOperator, realCoordinateTests, hn, ite_true,
      ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
      Complex.reCLM_apply, hcoordinate] using realOperatorPart_trace B.normal
        (B.realization PhotonFock).functional (operators B (Nat.unpair n).1) hx
  · simpa only [realOperator, realCoordinateTests, hn, ite_false,
      ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
      Complex.imCLM_apply, hcoordinate] using imaginaryOperatorPart_trace B.normal
        (B.realization PhotonFock).functional (operators B (Nat.unpair n).1) hx

variable {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [IsSeparable ν]
  (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

def gaussianHardTarget (x : B.Trace (Lp PhotonFock 2 ν)) : Marginal :=
  photonCoordinates B (hardTargetTrace BF κ B ν x)

section TestInstances

local instance realTestsPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance realTestsHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] productSource photonGaussianUnitary Gaussian.unitaryTest

set_option backward.isDefEq.respectTransparency.types true in
def gaussianRealPhotonTest (n : ℕ) (ψ : ℕ → Lp PhotonFock 2 ν)
    {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (hs : HasSum (fun j => (B.realization (Lp PhotonFock 2 ν)).rank.rankOne (ψ j)) x) :
    ProductTestData (productSource (X := X) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure (photonGaussianUnitary BF κ W)) ψ
      (realCoordinateTests n (gaussianHardTarget B ν BF κ x) : ℂ) := by
  have htarget : (B.realization PhotonFock).functional.repr
      (hardTargetTrace BF κ B ν x) (realOperator B n) =
      (realCoordinateTests n (gaussianHardTarget B ν BF κ x) : ℂ) :=
    realOperator_trace B n (hardTargetTrace_positive BF κ B ν hx)
  have hsum : HasSum (fun j =>
      ⟪ψ j, (gaussianObservable BF κ W (realOperator B n)).compLpL 2 ν (ψ j)⟫_ℂ)
      (realCoordinateTests n (gaussianHardTarget B ν BF κ x) : ℂ) :=
    (congrArg (fun target : ℂ => HasSum (fun j =>
      ⟪ψ j, (gaussianObservable BF κ W (realOperator B n)).compLpL 2 ν (ψ j)⟫_ℂ) target)
      htarget).mp (hardTargetTrace_source_hasSum BF κ W B ν (realOperator B n) hx hs)
  exact fiberOperatorTest (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
    ν W.space.measure (photonGaussianUnitary BF κ W)
    (hardCompression κ (realOperator B n)) ψ _ hsum

set_option backward.isDefEq.respectTransparency.types true in
omit [SFinite ν] in
theorem hardMarginal_real_rankOne (n : ℕ) (v : Lp (HardPhotonFock κ) 2 ν) :
    realCoordinateTests n (hardMarginal B ν BF κ
      ((B.realization (Lp (HardPhotonFock κ) 2 ν)).rank.rankOne v)) =
      (∫ x, ⟪v x, hardCompression κ (realOperator B n) (v x)⟫_ℂ ∂ν).re := by
  let z := B.push (H := HardPhotonFock κ) (K := PhotonFock)
    (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap
    (marginal B ν ((B.realization (Lp (HardPhotonFock κ) 2 ν)).rank.rankOne v))
  have hz : z ∈ (B.realization PhotonFock).rank.positive :=
    B.push_positive (H := HardPhotonFock κ) (K := PhotonFock) _ (marginal_positive B ν
      ((B.realization (Lp (HardPhotonFock κ) 2 ν)).rank.rankOne_positive v))
  have htrace := congrArg Complex.re (realOperator_trace B n hz)
  have he := hardMarginal_rankOne_observable B ν BF κ (realOperator B n) v
  have hi := compression_integral_congr (H := HardPhotonFock κ) (K := PhotonFock) ν
    (hardPhotonVacuumEmbedding BF κ).toContinuousLinearMap
    (generatedFockSubspace (hardOnePhoton κ)).subtypeL
    (hardPhotonVacuumEmbedding_apply BF κ) (realOperator B n) v
  exact htrace.symm.trans (congrArg Complex.re (he.trans hi))

end TestInstances

/-- The full original hard-test interface has no remaining physical matching field. -/
def gaussianOriginalHardTests (ψ : ℕ → Lp PhotonFock 2 ν)
    {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (hs : HasSum (fun j => (B.realization (Lp PhotonFock 2 ν)).rank.rankOne (ψ j)) x) :
    OriginalHardTests ν B BF κ W ψ (gaussianHardTarget B ν BF κ x) where
  hard n := gaussianRealPhotonTest B ν BF κ W n ψ hx hs
  separating := realCoordinateTests_separate
  hard_rankOne n _ v := hardMarginal_real_rankOne B ν BF κ n v

end GptLean.PhysicalRemovalMarginal
