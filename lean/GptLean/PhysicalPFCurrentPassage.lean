import GptLean.PhysicalPFSymmetricCurrent
import GptLean.PhysicalPFNormalObservables
import GptLean.PhysicalGraphCurrentMass

/-! Bounded physical PF energy and trace mass suffice for tested-current passage. -/

noncomputable section

namespace GptLean.PhysicalPFSource

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace
  PhysicalClosedForms PhysicalGraphForms ElectronicH1Multiplier Filter Topology
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

local instance referenceModule : Module ℂ (Reference I V) :=
  (referenceNormedSpace I V).toModule

local instance referenceSMul : SMul ℂ (Reference I V) :=
  (referenceModule I V).toSMul

def massGraph := (coerciveGraph I V C κ hκ M hbound e).append (inclusion I V)

variable {I V B}

theorem Source.massGraph_expectation {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤) :
    (((massGraph I V C κ hκ M hbound e).normalForm B S).expectation x).toReal =
      ((normalEnergy I V C κ hκ M hbound B S e).expectation x).toReal +
        (B.realization (WaveSpace I)).rank.trace x := by
  have hg := (massGraph I V C κ hκ M hbound e).normalForm_source_hasSum B S s.hasSum
    (s.operator_summable C κ hκ M hbound S e he (massGraph I V C κ hκ M hbound e).output)
  apply hg.unique
  apply ((s.energy_hasSum C κ hκ M hbound S e he).add s.mass_hasSum).congr_fun
  intro n
  exact ((coerciveGraph I V C κ hκ M hbound e).appendOutput_norm_sq
    (inclusion I V) (s.vector n)).trans
      (congrArg (fun r : ℝ => r + ‖inclusion I V (s.vector n)‖ ^ 2)
        (energyOutput_norm_sq I V C κ hκ M hbound e (s.vector n)))

theorem Source.current_crossValue {x : B.Trace (WaveSpace I)} (s : Source I V B x)
    (he : (normalEnergy I V C κ hκ M hbound B S e).expectation x < ⊤)
    (a : SmoothMultiplier I) (i : I) :
    (massGraph I V C κ hκ M hbound e).crossValue B S (inclusion I V)
      (testedCurrent I V C κ hκ M hbound e a i) x =
    (coerciveGraph I V C κ hκ M hbound e).crossValue B S (inclusion I V)
      (a.multiplier.comp (covariant I V C κ hκ M hbound e i)) x := by
  have hsym := (massGraph I V C κ hκ M hbound e).crossValue_source_hasSum B S
    (inclusion I V) (testedCurrent I V C κ hκ M hbound e a i)
    s.hasSum (s.reference_summable C κ hκ M hbound S e he)
  apply hsym.unique
  apply (s.inner_hasSum C κ hκ M hbound S e he (inclusion I V)
    (a.multiplier.comp (covariant I V C κ hκ M hbound e i))).congr_fun
  intro n
  exact testedCurrent_diagonal I V C κ hκ M hbound e a i (s.vector n)

variable (I V B)

theorem current_passage (a : SmoothMultiplier I) (i : I)
    (u : ℕ → B.Trace (WaveSpace I)) (x : B.Trace (WaveSpace I))
    (hu : ∀ n, u n ∈ (B.realization (WaveSpace I)).rank.positive)
    (hlim : Tendsto u atTop (𝓝 x)) (energyBound massBound : ℝ)
    (henergy : ∀ n, (normalEnergy I V C κ hκ M hbound B S e).expectation (u n) ≤
      ENNReal.ofReal energyBound)
    (hmass : ∀ n, (B.realization (WaveSpace I)).rank.trace (u n) ≤ massBound) :
    Tendsto (fun n => (coerciveGraph I V C κ hκ M hbound e).crossValue B S
      (inclusion I V) (a.multiplier.comp (covariant I V C κ hκ M hbound e i)) (u n)) atTop
      (𝓝 ((coerciveGraph I V C κ hκ M hbound e).crossValue B S
        (inclusion I V) (a.multiplier.comp (covariant I V C κ hκ M hbound e i)) x)) := by
  have hx := (B.realization (WaveSpace I)).rank.closed_positive.mem_of_tendsto hlim
    (Eventually.of_forall hu)
  have hxE := PhotonLoss.LocalizationData.observable_le_of_tendsto
    (PhotonLocalizationCurrent.expectation_lowerSemicontinuous
      (normalEnergy I V C κ hκ M hbound B S e)) hlim henergy
  have hxM : (B.realization (WaveSpace I)).rank.trace x ≤ massBound :=
    le_of_tendsto (((B.realization (WaveSpace I)).rank.trace.continuous.tendsto x).comp hlim)
      (Eventually.of_forall hmass)
  have hfinite (n : ℕ) := (henergy n).trans_lt ENNReal.ofReal_lt_top
  have hxfinite := hxE.trans_lt ENNReal.ofReal_lt_top
  let sources (n : ℕ) : Source I V B (u n) :=
    Classical.choice (source_exists I V C κ hκ M hbound B S e (hu n) (hfinite n))
  let sx : Source I V B x :=
    Classical.choice (source_exists I V C κ hκ M hbound B S e hx hxfinite)
  let J := testedCurrent I V C κ hκ M hbound e a i
  have hboundReal {y : B.Trace (WaveSpace I)}
      (hy : (normalEnergy I V C κ hκ M hbound B S e).expectation y ≤
        ENNReal.ofReal energyBound) :
      ((normalEnergy I V C κ hκ M hbound B S e).expectation y).toReal ≤
        max energyBound 0 := by
    simpa only [ENNReal.toReal_ofReal'] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  have hg := (coerciveGraph I V C κ hκ M hbound e).massCurrent_limit J B S
    (testedCurrent_symmetric I V C κ hκ M hbound e a i) u x hlim
    (fun n => ⟨(sources n).vector, (sources n).hasSum,
      (sources n).reference_summable C κ hκ M hbound S e (hfinite n)⟩)
    ⟨sx.vector, sx.hasSum, sx.reference_summable C κ hκ M hbound S e hxfinite⟩
    (max energyBound 0 + massBound)
    (fun n => ((sources n).massGraph_expectation C κ hκ M hbound S e (hfinite n)).le.trans
      (add_le_add (hboundReal (henergy n)) (hmass n)))
    ((sx.massGraph_expectation C κ hκ M hbound S e hxfinite).le.trans
      (add_le_add (hboundReal hxE) hxM))
  have hseq (n : ℕ) := (sources n).current_crossValue C κ hκ M hbound S e (hfinite n) a i
  have hend := sx.current_crossValue C κ hκ M hbound S e hxfinite a i
  exact (congrArg₂ (fun (f : ℕ → ℝ) (r : ℝ) => Tendsto f atTop (𝓝 r))
    (funext hseq) hend).mp hg

end GptLean.PhysicalPFSource
