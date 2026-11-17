import GptLean.PhysicalPFStates
import GptLean.PhysicalPFPairSeries

/-! The normal pair of a rank-one state is its actual wave-function pair. -/

noncomputable section

namespace GptLean.PhysicalPFStates

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalPFSource PhysicalNormalStates PhysicalSourceCoordinates
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {N : ℕ} (i : Fin N) (V : Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def referencePair (u : Reference (Index N) V) : PhysicalPairSpace.Pair :=
  PhysicalSourcePair.ofWaveFunction i
    (ElectronicH1Complex.realEquiv (electronic (Index N) V u))
    (fun b => covariant (Index N) V C κ hκ M hbound e (i, b) u)

theorem pair_rankOne (u : Reference (Index N) V)
    (hx : (B.realization (WaveSpace (Index N))).rank.rankOne (inclusion (Index N) V u) ∈
      (B.realization (WaveSpace (Index N))).rank.positive)
    (he : (energy V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace (Index N))).rank.rankOne (inclusion (Index N) V u)) < ⊤) :
    pair i V C κ hκ M hbound B S e
      ((B.realization (WaveSpace (Index N))).rank.rankOne (inclusion (Index N) V u)) hx he =
        referencePair i V C κ hκ M hbound e u := by
  let v : ℕ → Reference (Index N) V := fun n => if n = 0 then u else 0
  let s : Source (Index N) V B
      ((B.realization (WaveSpace (Index N))).rank.rankOne (inclusion (Index N) V u)) :=
    { vector := v
      hasSum := by
        apply (hasSum_ite_eq 0
          ((B.realization (WaveSpace (Index N))).rank.rankOne
            (inclusion (Index N) V u))).congr_fun
        intro n
        by_cases hn : n = 0
        · simp only [v, ite_eq_left hn]
        · simp only [v, ite_eq_right hn, map_zero, PhysicalNormalSpectral.rankOne_zero] }
  have hzero : PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e 0 = 0 := by
    exact (PhysicalPFPairSeries.pairForm_diagonal i V C κ hκ M hbound e 0).symm.trans
      (by simp only [map_zero])
  have hsingle : HasSum
      (fun n => PhysicalPFPairSeries.vectorPair i V C κ hκ M hbound e (s.vector n))
      (referencePair i V C κ hκ M hbound e u) := by
    apply (hasSum_ite_eq 0 (referencePair i V C κ hκ M hbound e u)).congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      rfl
    · simp only [s, v, ite_eq_right hn, hzero]
  have hseries := PhysicalPFPairSeries.vectorPair_hasSum i V C κ hκ M hbound S e s he
  exact (pair_eq_source i V C κ hκ M hbound B S e _ hx he s).trans
    (hseries.unique hsingle)

end GptLean.PhysicalPFStates
