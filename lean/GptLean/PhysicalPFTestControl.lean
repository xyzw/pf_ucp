import GptLean.PhysicalPFCurrentControl
import GptLean.PhysicalPFSmoothTests
import GptLean.PhysicalRelativeObservables

/-!
The separating physical pair tests have bounded approximants controlled
by the actual Pauli–Fierz energy plus trace mass.
-/

noncomputable section

namespace GptLean.PhysicalPFStates

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalPairSpace PhotonLocalizationCurrent
  RemovalState
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → PhysicalPFReference.Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def testObservable : SmoothPairTest →
    FormObservable (currentControl (Index N) V C κ hκ M hbound B S e)
  | .inl t => boundedObservable (densityTrace i B t.toBoundedSpatialTest)
  | .inr (b, t) => scaleObservable (N : ℝ)
      (regularizedCurrentObservable (Index N) V C κ hκ M hbound B S e
        (t.configuration i) (i, b))

def testRelativeApproximation (t : SmoothPairTest) :
    RelativeApproximation (R := (B.realization (WaveSpace (Index N))).rank)
      (currentControl (Index N) V C κ hκ M hbound B S e)
      (testObservable i V C κ hκ M hbound B S e t) := by
  cases t with
  | inl t =>
    exact boundedRelativeApproximation (R := (B.realization (WaveSpace (Index N))).rank)
      (E := currentControl (Index N) V C κ hκ M hbound B S e)
      (densityTrace i B t.toBoundedSpatialTest)
  | inr t =>
    exact scaleRelativeApproximation
      (regularizedCurrentApproximation (Index N) V C κ hκ M hbound B S e
        (t.2.configuration i) (i, t.1)) (N : ℝ)

theorem testObservable_value (t : SmoothPairTest) (x : B.Trace (WaveSpace (Index N)))
    (hx : x ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (currentControl (Index N) V C κ hκ M hbound B S e).expectation x < ⊤) :
    (testObservable i V C κ hκ M hbound B S e t).value x =
      normalTest i V C κ hκ M hbound B S e t x := by
  cases t with
  | inl t => rfl
  | inr t =>
    exact congrArg (fun r : ℝ => (N : ℝ) * r)
      (regularizedCurrentObservable_eq (Index N) V C κ hκ M hbound B S e hx he
        (t.2.configuration i) (i, t.1))

theorem testControl_reference_bound (x : B.Trace (WaveSpace (Index N)))
    (hx : x ∈ (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (energy V C κ hκ M hbound B S e).expectation x < ⊤) :
    (currentControl (Index N) V C κ hκ M hbound B S e).expectation x ≤
      ENNReal.ofReal (((energy V C κ hκ M hbound B S e).expectation x).toReal +
        (B.realization (WaveSpace (Index N))).rank.trace x) :=
  (currentControl_expectation (Index N) V C κ hκ M hbound B S e hx he).le

end GptLean.PhysicalPFStates
