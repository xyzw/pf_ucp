import GptLean.PhysicalPFCurrentPassage
import GptLean.PhysicalSmoothMultiplier
import GptLean.PhysicalPFStates
import GptLean.PhysicalPFSpatialObservables

/-! Separating physical pair tests and their bounded-energy normal-state passage. -/

noncomputable section

namespace GptLean.PhysicalPFStates

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalPairSpace Filter Topology
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

abbrev SmoothPairTest := SmoothSpatialTest ⊕ (Fin 3 × SmoothSpatialTest)

def smoothPairTest : SmoothPairTest → PhysicalPairSpace.Pair →L[ℝ] ℝ
  | .inl t => spatialDensityTest t.toBoundedSpatialTest
  | .inr (b, t) => spatialCurrentTest b t.toBoundedSpatialTest

theorem smoothPairTest_separates (p q : PhysicalPairSpace.Pair)
    (h : ∀ t, smoothPairTest t p = smoothPairTest t q) : p = q :=
  pair_eq_of_smooth_spatial_test_maps p q
    (fun t => h (.inl t)) (fun b t => h (.inr (b, t)))

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → PhysicalPFReference.Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def normalTest : SmoothPairTest → B.Trace (WaveSpace (Index N)) → ℝ
  | .inl t => densityTrace i B t.toBoundedSpatialTest
  | .inr (b, t) => (currentObservable i V C κ hκ M hbound B S e b t.toBoundedSpatialTest).value

theorem normalTest_statePair (t : SmoothPairTest)
    (x : (energy V C κ hκ M hbound B S e).State) :
    normalTest i V C κ hκ M hbound B S e t x.val =
      smoothPairTest t (statePair i V C κ hκ M hbound B S e x) := by
  cases t with
  | inl t =>
    exact (source V C κ hκ M hbound B S e x.val x.property.1 x.property.2.2).densityTrace_eq
      i V C κ hκ M hbound S e x.property.2.2 t.toBoundedSpatialTest
  | inr t =>
    exact (source V C κ hκ M hbound B S e x.val x.property.1 x.property.2.2).currentObservable_eq
      i V C κ hκ M hbound S e x.property.2.2 t.1 t.2.toBoundedSpatialTest

theorem normalTest_passage (t : SmoothPairTest)
    (u : ℕ → B.Trace (WaveSpace (Index N))) (x : B.Trace (WaveSpace (Index N)))
    (hu : ∀ n, u n ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (hlim : Tendsto u atTop (𝓝 x)) (energyBound massBound : ℝ)
    (henergy : ∀ n, (energy V C κ hκ M hbound B S e).expectation (u n) ≤
      ENNReal.ofReal energyBound)
    (hmass : ∀ n, (B.realization (WaveSpace (Index N))).rank.trace (u n) ≤ massBound) :
    Tendsto (fun n => normalTest i V C κ hκ M hbound B S e t (u n)) atTop
      (𝓝 (normalTest i V C κ hκ M hbound B S e t x)) := by
  cases t with
  | inl t => exact ((densityTrace i B t.toBoundedSpatialTest).continuous.tendsto x).comp hlim
  | inr t =>
    exact (current_passage (Index N) V C κ hκ M hbound B S e (t.2.configuration i) (i, t.1)
      u x hu hlim energyBound massBound henergy hmass).const_mul (N : ℝ)

end GptLean.PhysicalPFStates
