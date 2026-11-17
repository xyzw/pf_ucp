import GptLean.PhysicalRemovalMarginal
import GptLean.PhysicalRealObservableParts
import GptLean.PhysicalGaussianObservableTests
import GptLean.RemovalOriginalTests

/-! The hard-test component used to assemble the original physical tests. -/

noncomputable section

namespace GptLean.PhysicalRemovalMarginal

open MeasureTheory PhysicalFock PhysicalNormalTrace RemovalSource
open scoped ENNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [IsSeparable ν]
  (B : StandardNormalTraceBackground) (BF : StandardSymmetricFockExponential) (κ : ℝ)
  {J : RealStructure (softOnePhoton κ)}
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) J)

-- Use the direct normed-space parents of the constructed photon unitary.
local instance originalHardTestsPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance originalHardTestsHardDirectInner : InnerProductSpace ℂ (HardPhotonFock κ) :=
  { (inferInstance : InnerProductSpace ℂ (HardPhotonFock κ)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (HardPhotonFock κ)) }

/-- Only the actual hard photon tests remain separate from density and current. -/
structure OriginalHardTests (ψ : ℕ → Lp PhotonFock 2 ν) (target : Marginal) where
  hard : ∀ t, ProductTestData (X := X) (Q := W.space.Q)
    (H := PhotonFock) (K := HardPhotonFock κ)
    (PhysicalGaussianCoordinates.productSource (X := X) (Q := W.space.Q)
      (H := PhotonFock) (K := HardPhotonFock κ)
      ν W.space.measure (photonGaussianUnitary BF κ W))
    ψ (realCoordinateTests t target : ℂ)
  separating : ∀ a b : Marginal, (∀ t, realCoordinateTests t a = realCoordinateTests t b) → a = b
  hard_rankOne : ∀ t q (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2 ν),
    realCoordinateTests t (hardMarginal B ν BF κ
      ((B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2 ν)).rank.rankOne v)) =
        (∫ x, inner ℂ (v x) ((hard t).targetMultiplier (q, x) (v x)) ∂ν).re

end GptLean.PhysicalRemovalMarginal
