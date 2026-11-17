import GptLean.PhysicalPFStates
import GptLean.PhysicalPFSpatialObservables

/-! Actual normal operator mixtures preserve the physical pair affinely. -/

noncomputable section

namespace GptLean.PhysicalPFStates

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalNormalStates
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

abbrev SpatialPairTest := PhysicalPairSpace.SpatialTest ⊕
  (Fin 3 × PhysicalPairSpace.SpatialTest)

def spatialPairTest : SpatialPairTest → PhysicalPairSpace.Pair →ₗ[ℝ] ℝ
  | .inl t => (PhysicalPairSpace.spatialDensityTest t).toLinearMap
  | .inr (b, t) => (PhysicalPairSpace.spatialCurrentTest b t).toLinearMap

theorem spatialPairTest_separates (p q : PhysicalPairSpace.Pair)
    (h : ∀ t, spatialPairTest t p = spatialPairTest t q) : p = q :=
  PhysicalPairSpace.pair_eq_of_spatial_test_maps p q
    (fun t => h (.inl t)) (fun b t => h (.inr (b, t)))

variable {N : ℕ} (i : Fin N) (V : Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def spatialPairObservable : SpatialPairTest →
    RemovalState.FormObservable (energy V C κ hκ M hbound B S e)
  | .inl t => densityObservable i V C κ hκ M hbound B S e t
  | .inr (b, t) => currentObservable i V C κ hκ M hbound B S e b t

theorem spatialPairObservable_eq (t : SpatialPairTest)
    (m : MixedState V C κ hκ M hbound B S e) :
    (spatialPairObservable i V C κ hκ M hbound B S e t).value m.val.val =
      spatialPairTest t (mixedPair i V C κ hκ M hbound B S e m) := by
  cases t with
  | inl t =>
    exact (source V C κ hκ M hbound B S e m.val.val m.val.property.1
      m.val.property.2.2).densityTrace_eq i V C κ hκ M hbound S e m.val.property.2.2 t
  | inr t =>
    exact (source V C κ hκ M hbound B S e m.val.val m.val.property.1
      m.val.property.2.2).currentObservable_eq i V C κ hκ M hbound S e
        m.val.property.2.2 t.1 t.2

theorem mixedPair_mixture (m n : MixedState V C κ hκ M hbound B S e)
    (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hs : t + u = 1) :
    mixedPair i V C κ hκ M hbound B S e
      (mixture (energy V C κ hκ M hbound B S e) B.conjugation
        (PhysicalElectronicFermions.projection N PhotonFock) m n t u ht hu hs) =
      t • mixedPair i V C κ hκ M hbound B S e m +
        u • mixedPair i V C κ hκ M hbound B S e n :=
  mixture_pair_of_tests (energy V C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock)
    (mixedPair i V C κ hκ M hbound B S e) spatialPairTest
    (spatialPairObservable i V C κ hκ M hbound B S e) spatialPairTest_separates
    (spatialPairObservable_eq i V C κ hκ M hbound B S e) m n t u ht hu hs

theorem mixedModel_mixtureClosed :
    DFT.MixtureClosed (mixedModel i V C κ hκ M hbound B S e) :=
  mixtureClosed_of_tests (energy V C κ hκ M hbound B S e) B.conjugation
    (PhysicalElectronicFermions.projection N PhotonFock)
    (mixedPair i V C κ hκ M hbound B S e) spatialPairTest
    (spatialPairObservable i V C κ hκ M hbound B S e) spatialPairTest_separates
    (spatialPairObservable_eq i V C κ hκ M hbound B S e)

end GptLean.PhysicalPFStates
