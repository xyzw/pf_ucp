import GptLean.PhysicalPFCurrentPassage
import GptLean.PhysicalGraphCurrentObservable

/-! The physical energy plus trace mass supplies the current control form and approximants. -/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGraphForms ElectronicH1Multiplier PhotonLocalizationCurrent
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

local instance controlReferenceModule : Module ℂ (Reference I V) :=
  (referenceNormedSpace I V).toModule

local instance controlReferenceSMul : SMul ℂ (Reference I V) :=
  (controlReferenceModule I V).toSMul

def currentControl := (massGraph I V C κ hκ M hbound e).normalForm B S

theorem currentControl_finite_iff {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive) :
    (currentControl I V C κ hκ M hbound B S e).expectation x < ⊤ ↔
      (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤ := by
  constructor
  · intro he
    obtain ⟨u, hu, hs⟩ := (massGraph I V C κ hκ M hbound e).normalForm_source_exists B S hx he
    have ho := CoerciveGraph.summable_norm_sq_map (energyOutput I V C κ hκ M hbound e) u hs
    have henergy : Summable (fun n => energy I V C κ hκ M hbound e (u n)) := by
      exact ho.congr (fun n => energyOutput_norm_sq I V C κ hκ M hbound e (u n))
    have hv := (normalEnergy_source I V C κ hκ M hbound B S e u x hu).trans
      (ENNReal.ofReal_tsum_of_nonneg
        (fun n => energy_nonneg I V C κ hκ M hbound e (u n)) henergy).symm
    exact hv.symm ▸ ENNReal.ofReal_lt_top
  · intro he
    obtain ⟨u, hu, hs⟩ := reference_source_summable I V C κ hκ M hbound B S e x hx he
    exact (massGraph I V C κ hκ M hbound e).normalForm_source_finite B S hu hs

theorem currentControl_expectation {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    (currentControl I V C κ hκ M hbound B S e).expectation x =
      ENNReal.ofReal (((normalEnergy I V C κ hκ M hbound B S e).expectation x).toReal +
        (B.realization (WaveSpace I)).rank.trace x) := by
  have hf := (currentControl_finite_iff I V C κ hκ M hbound B S e hx).mpr he
  have hex : Nonempty (Source I V B x) := source_exists I V C κ hκ M hbound B S e hx he
  obtain ⟨s⟩ := hex
  exact (ENNReal.ofReal_toReal hf.ne).symm.trans
    (congrArg ENNReal.ofReal (s.massGraph_expectation C κ hκ M hbound S e he))

def regularizedCurrentObservable (a : SmoothMultiplier I) (i : I) :=
  (coerciveGraph I V C κ hκ M hbound e).massCurrentObservable
    (testedCurrent I V C κ hκ M hbound e a i) B S
    (testedCurrent_symmetric I V C κ hκ M hbound e a i)

def regularizedCurrentApproximation (a : SmoothMultiplier I) (i : I) :
    RelativeApproximation (R := (B.realization (WaveSpace I)).rank)
      (currentControl I V C κ hκ M hbound B S e)
      (regularizedCurrentObservable I V C κ hκ M hbound B S e a i) :=
  (coerciveGraph I V C κ hκ M hbound e).massCurrentRelativeApproximation
    (testedCurrent I V C κ hκ M hbound e a i) B S
    (testedCurrent_symmetric I V C κ hκ M hbound e a i)

theorem regularizedCurrentObservable_eq {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive)
    (he : (currentControl I V C κ hκ M hbound B S e).expectation x < ⊤)
    (a : SmoothMultiplier I) (i : I) :
    (regularizedCurrentObservable I V C κ hκ M hbound B S e a i).value x =
      (coerciveGraph I V C κ hκ M hbound e).crossValue B S (inclusion I V)
        (a.multiplier.comp (covariant I V C κ hκ M hbound e i)) x := by
  have hf := (currentControl_finite_iff I V C κ hκ M hbound B S e hx).mp he
  have hex : Nonempty (Source I V B x) := source_exists I V C κ hκ M hbound B S e hx hf
  obtain ⟨s⟩ := hex
  exact s.current_crossValue C κ hκ M hbound S e hf a i

end GptLean.PhysicalPFSource
