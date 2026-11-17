import GptLean.PhysicalPhotonMarginal
import GptLean.PhysicalFockRadiationGraph

/-!
Actual pure and mixed photon moments on electronic L². Bounded fiber
multipliers commute with the spatial partial trace. Monotone convergence
then identifies every nonnegative momentum form with its pointwise Fock
integral. The radiation graph gives exactly the squared L² output norm.
-/

noncomputable section
namespace GptLean.PhysicalPhotonMarginal

open MeasureTheory PhotonLocalizationChannel RemovalState PhysicalNormalTrace
  PhysicalNormalTrace.StandardNormalTraceBackground PhysicalFock
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

section Quadratic
variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem quadratic_integrable (A : H →L[ℂ] H) (u : Lp H 2 μ) :
    Integrable (fun x => (⟪u x, A (u x)⟫_ℂ).re) μ := by
  apply (Complex.reCLM.integrable_comp (L2.integrable_inner (𝕜 := ℂ) u (A.compLpL 2 μ u))).congr
  filter_upwards [A.coeFn_compLpL u] with x hx
  change (⟪u x, (A.compLpL 2 μ u) x⟫_ℂ).re = _
  rw [hx]

omit [CompleteSpace H] in
theorem quadratic_integral (A : H →L[ℂ] H) (u : Lp H 2 μ) :
    (⟪u, A.compLpL 2 μ u⟫_ℂ).re = ∫ x, (⟪u x, A (u x)⟫_ℂ).re ∂μ := by
  rw [L2.inner_def]
  rw [← show (∫ x, (⟪u x, (A.compLpL 2 μ u) x⟫_ℂ).re ∂μ) =
      (∫ x, ⟪u x, (A.compLpL 2 μ u) x⟫_ℂ ∂μ).re from
    Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) u (A.compLpL 2 μ u))]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL u] with x hx
  rw [hx]

omit [CompleteSpace H] in
theorem quadratic_lintegral (A : H →L[ℂ] H) (hA : ∀ v, 0 ≤ (⟪v, A v⟫_ℂ).re) (u : Lp H 2 μ) :
    ENNReal.ofReal (⟪u, A.compLpL 2 μ u⟫_ℂ).re =
      ∫⁻ x, ENNReal.ofReal (⟪u x, A (u x)⟫_ℂ).re ∂μ := by
  rw [quadratic_integral, ofReal_integral_eq_lintegral_ofReal (quadratic_integrable A u)
    (ae_of_all _ fun x => hA (u x))]
end Quadratic

variable (B : StandardNormalTraceBackground)
  {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]
  (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)

def fullMomentumForm : PositiveForm (B.traceData (H := Lp PhotonFock 2 μ)) :=
  fullForm B μ (secondQuantizedPositiveForm q hq B.normal (B.realization PhotonFock).functional)

theorem fullMomentumForm_truncation (M : ℕ) {x : B.Trace (Lp PhotonFock 2 μ)}
    (hx : x ∈ (B.realization (Lp PhotonFock 2 μ)).rank.positive) :
    (fullMomentumForm B μ q hq).truncation M x =
      ((B.realization (Lp PhotonFock 2 μ)).functional.repr x
        (((cappedWeight q hq M).operator (Nat.cast_nonneg M)).compLpL 2 μ)).re := by
  change ((B.realization PhotonFock).functional.repr (marginal B μ x)
    ((cappedWeight q hq M).operator (Nat.cast_nonneg M))).re = _
  exact congrArg Complex.re (marginal_evaluation B μ (H := PhotonFock)
    ((cappedWeight q hq M).operator (Nat.cast_nonneg M)) (x := x) hx)

/-- The full-state pure form is its actual pointwise photon energy integral. -/
theorem fullMomentumForm_rankOne (u : Lp PhotonFock 2 μ) :
    (fullMomentumForm B μ q hq).expectation ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
      ∫⁻ x, photonMoment q (u x) ∂μ := by
  change (⨆ M, ENNReal.ofReal ((fullMomentumForm B μ q hq).truncation M
    ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u))) = _
  simp_rw [fullMomentumForm_truncation B μ q hq _
    ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne_positive u),
    (B.realization (Lp PhotonFock 2 μ)).functional.rankOne,
    quadratic_lintegral _ ((cappedWeight q hq _).operator_inner_nonneg (Nat.cast_nonneg _)
      (cappedSectorWeight_nonneg q _))]
  have hm (M : ℕ) : Measurable (fun x => ENNReal.ofReal
      (⟪u x, (cappedWeight q hq M).operator (Nat.cast_nonneg M) (u x)⟫_ℂ).re) :=
    (Complex.continuous_re.comp_stronglyMeasurable ((Lp.stronglyMeasurable u).inner
      (((cappedWeight q hq M).operator (Nat.cast_nonneg M)).continuous.comp_stronglyMeasurable
        (Lp.stronglyMeasurable u)))).measurable.ennreal_ofReal
  rw [← lintegral_iSup hm (fun M L hML x => ENNReal.ofReal_le_ofReal
    ((cappedWeight q hq M).operator_inner_mono (cappedWeight q hq L)
      (Nat.cast_nonneg M) (Nat.cast_nonneg L) (fun n k => cappedSectorWeight_mono q n k hML) (u x)))]
  apply lintegral_congr
  intro x
  exact cappedWeight_recovery q hq (u x)

theorem fullMomentumForm_source {v : ℕ → Lp PhotonFock 2 μ}
    {x : B.Trace (Lp PhotonFock 2 μ)}
    (hv : HasSum (fun n => (B.realization (Lp PhotonFock 2 μ)).rank.rankOne (v n)) x) :
    (fullMomentumForm B μ q hq).expectation x =
      ∑' n, ∫⁻ y, photonMoment q (v n y) ∂μ := by
  rw [← hv.tsum_eq, (fullMomentumForm B μ q hq).expectation_tsum hv.summable
    (fun n => (B.realization (Lp PhotonFock 2 μ)).rank.rankOne_positive (v n))]
  exact tsum_congr fun n => fullMomentumForm_rankOne B μ q hq (v n)

theorem fullNumberForm_rankOne (u : Lp PhotonFock 2 μ) :
    (fullForm B μ (NormalPhoton.numberForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
        ∫⁻ x, photonNumberForm photonMeasure (u x) ∂μ := by
  simpa only [fullMomentumForm, NormalPhoton.numberForm, photonMoment_one] using fullMomentumForm_rankOne B μ (fun _ => 1) measurable_const u

theorem fullRadiationForm_rankOne (u : Lp PhotonFock 2 μ) :
    (fullForm B μ (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u) =
        ∫⁻ x, radiationForm (u x) ∂μ := by
  simpa only [fullMomentumForm, NormalPhoton.radiationForm, NormalPhoton.frequency, photonMoment_frequency] using fullMomentumForm_rankOne B μ
    (fun p => ENNReal.ofReal ‖p.1‖) measurable_fst.norm.ennreal_ofReal u

/-- A pointwise radiation-root graph identity gives the exact normal form
value, with no full-state radiation comparison supplied. -/
theorem fullRadiationForm_graph (u r : Lp PhotonFock 2 μ)
    (hgraph : ∀ᵐ x ∂μ, (u x, r x) ∈ radiationRoot.graph) :
    (fullForm B μ (NormalPhoton.radiationForm B.normal (B.realization PhotonFock).functional)).expectation
      ((B.realization (Lp PhotonFock 2 μ)).rank.rankOne u) = ENNReal.ofReal (‖r‖ ^ 2) := by
  rw [fullRadiationForm_rankOne]
  have he : (fun x => radiationForm (u x)) =ᵐ[μ] (fun x => ENNReal.ofReal (‖r x‖ ^ 2)) := by
    filter_upwards [hgraph] with x hx
    obtain ⟨v, hv, hr⟩ := radiationRoot.mem_graph_iff.mp hx
    change (v : PhotonFock) = u x at hv
    change radiationRoot v = r x at hr
    rw [← hv, ← hr]
    exact radiationRoot_energy v
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r))
    (ae_of_all _ fun x => sq_nonneg _)]
  let : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ PhotonFock
  rw [← PhotonKernelLocalization.l2_norm_sq_eq_integral]
end GptLean.PhysicalPhotonMarginal
