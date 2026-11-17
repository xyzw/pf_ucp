import GptLean.PhysicalFreeForm
import GptLean.PhysicalKineticForm
import GptLean.PhysicalSpatialRadiationDomain

/-!
The constructed free normal form is exactly trace mass plus ordinary
kinetic energy plus the actual full photon radiation form. The identity
includes infinite energies and all positive normal traces.
-/

noncomputable section

namespace GptLean.PhysicalFreeDecomposition

open MeasureTheory PhysicalFock PhysicalNormalTrace PhysicalPhotonMarginal PhotonLocalizationChannel
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true

private theorem decomposition_from_finite {V Q : Type*}
    (E K A M : V → ℝ≥0∞) (f : Q → V)
    (hf : ∀ v, E v < ⊤ → ∃ q, f q = v)
    (hcommon : ∀ v, K v < ⊤ → A v < ⊤ → E v < ⊤)
    (hgraph : ∀ q, E (f q) = M (f q) + K (f q) + A (f q)) (v : V) :
    E v = M v + K v + A v := by
  by_cases he : E v < ⊤
  · obtain ⟨q, rfl⟩ := hf v he
    exact hgraph q
  · have het : E v = ⊤ := top_unique (not_lt.mp he)
    by_cases hk : K v < ⊤
    · by_cases ha : A v < ⊤
      · exact (he (hcommon v hk ha)).elim
      · have hat : A v = ⊤ := top_unique (not_lt.mp ha)
        simp only [het, hat, add_top]
    · have hkt : K v = ⊤ := top_unique (not_lt.mp hk)
      simp only [het, hkt, add_top, top_add]

private theorem normal_eq_of_rankOne {H T : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    {R : Gaussian.RankOneData H T} (normal : NormalTraceData R) (F : NormalFunctionalData R)
    (E K A : RemovalState.PositiveForm (positiveTrace normal F))
    (h : ∀ v, E.expectation (R.rankOne v) = ENNReal.ofReal (‖v‖ ^ 2) +
      K.expectation (R.rankOne v) + A.expectation (R.rankOne v))
    {x : T} (hx : x ∈ R.positive) :
    E.expectation x = ENNReal.ofReal (R.trace x) + K.expectation x + A.expectation x := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  have hmass : ENNReal.ofReal (R.trace x) = ∑' n, ENNReal.ofReal (‖v n‖ ^ 2) := by
    have hs : HasSum (fun n => ‖v n‖ ^ 2) (R.trace x) := by
      simpa only [R.trace_rankOne] using R.trace.hasSum hv
    exact (congrArg ENNReal.ofReal hs.tsum_eq).symm.trans
      (ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs.summable)
  have he := E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))
  have hk := K.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))
  have ha := A.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))
  have hsource : (∑' n, E.expectation (R.rankOne (v n))) =
      (∑' n, ENNReal.ofReal (‖v n‖ ^ 2)) +
        (∑' n, K.expectation (R.rankOne (v n))) + (∑' n, A.expectation (R.rankOne (v n))) := by
    simp only [h, ENNReal.tsum_add]
  rw [hv.tsum_eq] at he hk ha
  exact he.trans (hsource.trans (by rw [← hmass, ← hk, ← ha]))

variable (I : Type) [Fintype I] [DecidableEq I]
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)

abbrev WaveSpace := PhysicalFreeForm.WaveSpace I

def kinetic : RemovalState.PositiveForm (B.traceData (H := WaveSpace I)) :=
  PhysicalKineticForm.normalEnergy PhotonFock I B S

def radiation : RemovalState.PositiveForm (B.traceData (H := WaveSpace I)) :=
  fullForm B (volume : Measure (EuclideanSpace ℝ I))
    (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)

private def ofMatched (e : ElectronicH1Complex.ComplexH1 PhotonFock I)
    (r : PhysicalFreeReferenceCore.RadiationSource I)
    (h : ElectronicH1Complex.value e = spatialRadiationInclusion volume r) :
    PhysicalFreeReferenceCore.FreeReference I :=
  ⟨(e, r), by
    change ElectronicH1Complex.value e - spatialRadiationInclusion volume r = 0
    exact sub_eq_zero.mpr h⟩

theorem kinetic_reference (u : PhysicalFreeForm.Reference I) :
    (kinetic I B S).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (PhysicalFreeForm.inclusion I u)) =
        ENNReal.ofReal (∑ i, ‖PhysicalFreeForm.ordinary I i u‖ ^ 2) :=
  PhysicalKineticForm.normalEnergy_rankOne PhotonFock I B S
    (PhysicalFreeReferenceCore.electronic I u)

theorem radiation_reference (u : PhysicalFreeForm.Reference I) :
    (radiation I B).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (PhysicalFreeForm.inclusion I u)) =
        ENNReal.ofReal (‖PhysicalFreeForm.radiation I u‖ ^ 2) := by
  apply fullRadiationForm_graph B volume
  have hg := PhysicalSpatialRadiationDomain.source_graph
    (PhysicalFreeReferenceCore.radiationSource I u)
  have hm := PhysicalFreeReferenceCore.value_matching I u
  exact (congrArg (fun v : WaveSpace I =>
    ∀ᵐ x ∂volume, (v x, PhysicalFreeForm.radiation I u x) ∈ radiationRoot.graph) hm).mpr hg

theorem rankOne_decomposition (v : WaveSpace I) :
    (PhysicalFreeForm.normalEnergy I B S).expectation
      ((B.realization (WaveSpace I)).rank.rankOne v) =
        ENNReal.ofReal (‖v‖ ^ 2) +
          (kinetic I B S).expectation ((B.realization (WaveSpace I)).rank.rankOne v) +
          (radiation I B).expectation ((B.realization (WaveSpace I)).rank.rankOne v) := by
  apply decomposition_from_finite
    (fun w => (PhysicalFreeForm.normalEnergy I B S).expectation
      ((B.realization (WaveSpace I)).rank.rankOne w))
    (fun w => (kinetic I B S).expectation ((B.realization (WaveSpace I)).rank.rankOne w))
    (fun w => (radiation I B).expectation ((B.realization (WaveSpace I)).rank.rankOne w))
    (fun w => ENNReal.ofReal (‖w‖ ^ 2)) (PhysicalFreeForm.inclusion I)
  · intro w hw
    apply (PhysicalFreeForm.normalEnergy_finite_iff I B S w).mp
    exact hw
  · intro w hk ha
    have hek : ∃ e : ElectronicH1Complex.ComplexH1 PhotonFock I,
        ElectronicH1Complex.value e = w := by
      apply (PhysicalKineticForm.normalEnergy_finite_iff PhotonFock I B S w).mp
      exact hk
    have her : ∃ r : SpatialRadiationGraph (volume : Measure (EuclideanSpace ℝ I)),
        spatialRadiationInclusion volume r = w := by
      apply (PhysicalSpatialRadiationDomain.fullRadiationForm_finite_iff volume B w).mp
      exact ha
    obtain ⟨e, he⟩ := hek
    obtain ⟨r, hr⟩ := her
    apply (PhysicalFreeForm.normalEnergy_finite_iff I B S w).mpr
    exact ⟨ofMatched I e r (he.trans hr.symm), he⟩
  · intro u
    have hk := kinetic_reference I B S u
    have ha := radiation_reference I B u
    have he := PhysicalFreeForm.normalEnergy_rankOne I B S u
    have hsum : ENNReal.ofReal (PhysicalFreeForm.energy I u) =
        ENNReal.ofReal (‖PhysicalFreeForm.inclusion I u‖ ^ 2) +
          ENNReal.ofReal (∑ i : I, ‖PhysicalFreeForm.ordinary I i u‖ ^ 2) +
          ENNReal.ofReal (‖PhysicalFreeForm.radiation I u‖ ^ 2) := (ENNReal.ofReal_add
      (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg ‖PhysicalFreeForm.ordinary I i u‖))
      (sq_nonneg ‖PhysicalFreeForm.radiation I u‖)).trans
      (congrArg (fun t => t + ENNReal.ofReal (‖PhysicalFreeForm.radiation I u‖ ^ 2))
        (ENNReal.ofReal_add (sq_nonneg ‖PhysicalFreeForm.inclusion I u‖)
          (Finset.sum_nonneg fun i _ => sq_nonneg ‖PhysicalFreeForm.ordinary I i u‖)))
    exact he.trans (hsum.trans (congrArg₂ (fun k a =>
      ENNReal.ofReal (‖PhysicalFreeForm.inclusion I u‖ ^ 2) + k + a) hk.symm ha.symm))

theorem normal_decomposition {x : B.Trace (WaveSpace I)}
    (hx : x ∈ (B.realization (WaveSpace I)).rank.positive) :
    (PhysicalFreeForm.normalEnergy I B S).expectation x =
      ENNReal.ofReal ((B.realization (WaveSpace I)).rank.trace x) +
        (kinetic I B S).expectation x + (radiation I B).expectation x :=
  normal_eq_of_rankOne B.normal (B.realization (WaveSpace I)).functional
    (PhysicalFreeForm.normalEnergy I B S) (kinetic I B S) (radiation I B)
    (rankOne_decomposition I B S) hx

end GptLean.PhysicalFreeDecomposition
