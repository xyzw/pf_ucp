import GptLean.PhysicalPFDomain
import GptLean.PhysicalPhotonMarginalMoments
import GptLean.PhysicalNormalStates

/-!
The actual photon marginal of a positive normal Pauli--Fierz state has
radiation energy bounded by the same normal Pauli--Fierz form. The proof
uses the finite-domain characterization of the constructed closed form,
its reference-graph value, and ordinary positive spectral decomposition.
No marginal energy comparison is assumed.
-/

noncomputable section

namespace GptLean.PhysicalPFRadiation

open MeasureTheory PhotonLocalizationChannel RemovalState PhysicalNormalTrace
  PhysicalNormalTrace.StandardNormalTraceBackground PhysicalClosedForms
  PhysicalPhotonMarginal PhysicalFock PhysicalPFReference
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

section NormalComparison
variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)

/-- Positive spectral decomposition lifts every rank-one form inequality. -/
theorem expectation_le_of_rankOne
    (E G : PositiveForm (positiveTrace normal F))
    (h : ∀ v, E.expectation (R.rankOne v) ≤ G.expectation (R.rankOne v))
    {x : T} (hx : x ∈ R.positive) : E.expectation x ≤ G.expectation x := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  rw [← hv.tsum_eq, E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n)),
    G.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))]
  exact ENNReal.tsum_le_tsum (fun n => h (v n))
end NormalComparison

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

/-- The radiation form is pulled back by the constructed spatial marginal. -/
def normalRadiation : PositiveForm (B.traceData (H := WaveSpace I)) :=
  fullForm B (volume : Measure (Position I))
    (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)


theorem normalRadiation_reference (u : Reference I V) :
    (normalRadiation I B).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (inclusion I V u)) =
        ENNReal.ofReal (‖radiation I V u‖ ^ 2) :=
  fullRadiationForm_graph B (volume : Measure (Position I))
    (inclusion I V u) (radiation I V u) (radiation_graph I V u)

set_option backward.isDefEq.respectTransparency.types true in
theorem normalRadiation_rankOne_le (e : ℝ) (v : WaveSpace I) :
    (normalRadiation I B).expectation ((B.realization (WaveSpace I)).rank.rankOne v) ≤
      (normalEnergy I V C κ hκ M hbound B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne v) := by
  by_cases hf : (normalEnergy I V C κ hκ M hbound B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v) < ⊤
  · obtain ⟨u, rfl⟩ := (normalEnergy_rankOne_finite_iff I V C κ hκ M hbound B S e v).mp hf
    exact (normalRadiation_reference I V B u).le.trans
      ((ENNReal.ofReal_le_ofReal (radiation_le_energy I V C κ hκ M hbound e u)).trans_eq
        (normalEnergy_rankOne I V C κ hκ M hbound B S e u).symm)
  · exact le_top.trans (not_lt.mp hf)

/-- The mixed-state comparison is proved for every positive normal state. -/
theorem normalRadiation_le (e : ℝ) {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive) :
    (normalRadiation I B).expectation x ≤
      (normalEnergy I V C κ hκ M hbound B S e).expectation x :=
  expectation_le_of_rankOne B.normal (B.realization (WaveSpace I)).functional
    (normalRadiation I B) (normalEnergy I V C κ hκ M hbound B S e)
    (normalRadiation_rankOne_le I V C κ hκ M hbound B S e) hx

theorem normalRadiation_state_finite (e : ℝ)
    (s : (normalEnergy I V C κ hκ M hbound B S e).State) :
    (normalRadiation I B).expectation s.val < ⊤ :=
  (normalRadiation_le I V C κ hκ M hbound B S e s.property.1).trans_lt s.property.2.2

theorem normalRadiation_state_toReal_le (e : ℝ)
    (s : (normalEnergy I V C κ hκ M hbound B S e).State) :
    ((normalRadiation I B).expectation s.val).toReal ≤
      ((normalEnergy I V C κ hκ M hbound B S e).expectation s.val).toReal :=
  ENNReal.toReal_mono s.property.2.2.ne
    (normalRadiation_le I V C κ hκ M hbound B S e s.property.1)

/-- On any compression-fixed sector of the actual finite-energy normal
states, the infrared moment data now require only the article's infrared
cutoff integrability assumptions. -/
def infraredMoments (e : ℝ) (P : WaveSpace I →L[ℂ] WaveSpace I)
    {Pair : Type*}
    (pair : PhysicalNormalStates.Mixed (normalEnergy I V C κ hκ M hbound B S e)
      B.conjugation P → Pair)
    (w : PhotonMode → ℝ≥0∞) (hw : Measurable w)
    (hwFinite : ∫⁻ p, w p ∂photonMeasure < ⊤)
    (hwWeighted : ∫⁻ p, w p * ENNReal.ofReal (1 / NormalPhoton.frequency p)
      ∂photonMeasure < ⊤) :
    InfraredRepair.InfraredMoments
      (PhysicalNormalStates.mixedModel (normalEnergy I V C κ hκ M hbound B S e)
        B.conjugation P pair)
      (fun s => (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional).expectation
        (marginal B (volume : Measure (Position I)) s.val.val))
      photonMeasure NormalPhoton.frequency w :=
  NormalPhoton.infraredMoments B.normal (B.realization PhotonFock).functional
    (PhysicalNormalStates.mixedModel (normalEnergy I V C κ hκ M hbound B S e)
      B.conjugation P pair)
    (fun s => marginal B (volume : Measure (Position I)) s.val.val)
    (fun s => marginal_positive B _ s.val.property.1)
    (fun s => normalRadiation_state_finite I V C κ hκ M hbound B S e s.val)
    (fun s => normalRadiation_state_toReal_le I V C κ hκ M hbound B S e s.val)
    w hw hwFinite hwWeighted

end GptLean.PhysicalPFRadiation
