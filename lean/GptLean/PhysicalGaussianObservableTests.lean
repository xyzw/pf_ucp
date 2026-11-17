import GptLean.PhysicalGaussianChannelObservables
import GptLean.PhysicalGaussianSource
import GptLean.RemovalSourceTests

/-!
Bounded photon tests for the original Gaussian spectral source. The
source multiplier is obtained by unitary conjugation and its spatial
locality is proved from the actual product-source construction.
-/

noncomputable section
namespace GptLean.PhysicalGaussianCoordinates

open MeasureTheory Filter Gaussian RemovalSource
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X Q H K : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  (ν : Measure X) (μ : Measure Q) [SFinite ν] [SFinite μ] [IsSeparable μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (D : K →L[ℂ] K)

theorem productSource_unitaryTest (v : Lp H 2 ν) :
    productSource ν μ U ((unitaryTest U D).compLpL 2 ν v) =
      D.compLpL 2 (μ.prod ν) (productSource ν μ U v) := by
  apply productSource_fiberOperator ν μ U (unitaryTest U D) D _ v
  intro u
  exact U.apply_symm_apply _

theorem conjugated_fiberOperator (v : Lp H 2 ν) :
    conjugatedOperator (productSource ν μ U) (D.compLpL 2 (μ.prod ν)) v =
      (unitaryTest U D).compLpL 2 ν v := by
  change (productSource ν μ U).symm
    (D.compLpL 2 (μ.prod ν) (productSource ν μ U v)) = _
  rw [← productSource_unitaryTest ν μ U D v, LinearIsometryEquiv.symm_apply_apply]

/-- Constant fiber observables provide the complete original-test interface. -/
def fiberOperatorTest (ψ : ℕ → Lp H 2 ν) (target : ℂ)
    (hs : HasSum (fun n => ⟪ψ n, (unitaryTest U D).compLpL 2 ν (ψ n)⟫_ℂ) target) :
    ProductTestData (productSource ν μ U) ψ target where
  operator := D.compLpL 2 (μ.prod ν)
  sourceMultiplier _ := unitaryTest U D
  targetMultiplier _ := D
  sourceBound := ‖unitaryTest U D‖
  targetBound := ‖D‖
  source_bounded := ae_of_all _ fun _ => le_rfl
  target_bounded := ae_of_all _ fun _ => le_rfl
  source_measurable n := (unitaryTest U D).continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable (ψ n))
  target_measurable v := D.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)
  source_rankOne v := by
    rw [conjugated_fiberOperator ν μ U D, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(unitaryTest U D).coeFn_compLpL v] with x hx
    rw [hx]
  target_rankOne v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [D.coeFn_compLpL v] with qx hqx
    rw [hqx]
  original := by
    simpa only [conjugated_fiberOperator ν μ U D] using hs

end GptLean.PhysicalGaussianCoordinates

namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhysicalGaussianCoordinates PhysicalNormalTrace
  PhotonLocalizationChannel RemovalSource
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] observableGeneratedComplete

variable {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [IsSeparable ν]
  (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)
  (B : StandardNormalTraceBackground)

section TestInstances

local instance observableTestsPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance observableTestsHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

attribute [local irreducible] productSource photonGaussianUnitary unitaryTest

set_option backward.isDefEq.respectTransparency.types true in
set_option diagnostics true in
/-- The hard target is evaluated on the same original positive normal source. -/
def gaussianPhotonTest (A : PhotonFock →L[ℂ] PhotonFock)
    (ψ : ℕ → Lp PhotonFock 2 ν) {x : B.Trace (Lp PhotonFock 2 ν)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 ν)).rank.positive)
    (hs : HasSum (fun n => (B.realization (Lp PhotonFock 2 ν)).rank.rankOne (ψ n)) x) :
    ProductTestData (productSource (X := X) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure (photonGaussianUnitary BF κ W)) ψ
      ((B.realization PhotonFock).functional.repr (hardTargetTrace BF κ B ν x) A) :=
  fiberOperatorTest (X := X) (Q := W.space.Q) (H := PhotonFock) (K := HardPhotonFock κ)
    ν W.space.measure (photonGaussianUnitary BF κ W) (hardCompression κ A)
    ψ _ (hardTargetTrace_source_hasSum BF κ W B ν A hx hs)

end TestInstances

end GptLean.PhysicalFock
