import GptLean.PhotonLocalizationFormBoundsLifting
import GptLean.PhotonLocalizationLocalForms

/-!
Finite normal form expectations supply the real source estimates used
by local compactness. The source is a fixed trace-class expansion, so
these results apply directly to the constructed channel's Kraus vectors.
No new spectral decomposition of the localized state is needed.
-/

namespace GptLean.PhotonLocalizationFormBounds

open scoped ENNReal

/-- A bounded nonnegative extended-real sum supplies both real
summability and the real numerical estimate. -/
theorem real_series_of_ennreal_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {B : ℝ} (hB : 0 ≤ B) (hbound : (∑' n, ENNReal.ofReal (f n)) ≤ ENNReal.ofReal B) :
    Summable f ∧ ∑' n, f n ≤ B := by
  have hfinite : (∑' n, ENNReal.ofReal (f n)) ≠ ⊤ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hs : Summable f := by
    simpa only [ENNReal.toReal_ofReal (hf _)] using ENNReal.summable_toReal hfinite
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hbound

section Trace

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}

omit [InnerProductSpace ℂ H] [CompleteSpace T] in
/-- The source form sum and its summability follow from the actual
bounded positive-form trace on the same trace-class state. -/
theorem source_form_bounds (E : RemovalState.PositiveForm Tr)
    (hpositive : R.positive ⊆ Tr.positive) {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hvalue : ∀ n, E.expectation (R.rankOne (v n)) = ENNReal.ofReal (f n))
    {B : ℝ} (hB : 0 ≤ B) (hbound : E.expectation x ≤ ENNReal.ofReal B) :
    Summable f ∧ ∑' n, f n ≤ B := by
  apply real_series_of_ennreal_bound hf hB
  rw [← hv.tsum_eq, E.expectation_tsum hv.summable
    (fun n => hpositive (R.rankOne_positive (v n)))] at hbound
  simpa only [hvalue] using hbound

omit [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T] in
/-- Number-sector spectral calculus now gives the first-moment hypotheses
of the explicit number cutoff. Only the universal spectral trace identity
is needed, together with the number bound already proved for the channel. -/
theorem number_moment_bounds (number : T → ℝ≥0∞) (weight : ℕ → ℝ)
    (hweight : ∀ n, 0 ≤ weight n) {x : T}
    (hnumber : number x = ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * weight n))
    {B : ℝ} (hB : 0 ≤ B) (hbound : number x ≤ ENNReal.ofReal B) :
    Summable (fun n : ℕ => (n : ℝ) * weight n) ∧
      (∑' n : ℕ, (n : ℝ) * weight n) ≤ B := by
  apply real_series_of_ennreal_bound (fun n => mul_nonneg (by positivity) (hweight n)) hB
  rwa [← hnumber]

end Trace

end GptLean.PhotonLocalizationFormBounds

namespace GptLean.PhotonLocalization

open MeasureTheory
open scoped ENNReal

variable {I K T : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : K →ₗ.[ℂ] K}
  {A : Gaussian.RankOneData (SpatialPhotonL2 I K) T}
  {Tr : RemovalState.PositiveTraceData T}

omit [CompleteSpace K] [CompleteSpace T] in
/-- The standard free-form domain characterization chooses spatial graph
representatives for every vector in an arbitrary positive source series.
Finite total form expectation proves that each vector is in the domain,
and supplies all source summability and uniform energy hypotheses of
`LocalFormData.ofSpatialSources`. -/
theorem spatial_sources_of_finite_form (E : RemovalState.PositiveForm Tr)
    (hpositive : A.positive ⊆ Tr.positive)
    (hgraph : ∀ v : SpatialPhotonL2 I K, E.expectation (A.rankOne v) < ⊤ →
      ∃ u : SpatialFreeVector (I := I) R, u.value = v ∧
        E.expectation (A.rankOne v) = ENNReal.ofReal u.form)
    {v : ℕ → SpatialPhotonL2 I K} {x : T}
    (hv : HasSum (fun n => A.rankOne (v n)) x)
    {B : ℝ} (hB : 0 ≤ B) (hbound : E.expectation x ≤ ENNReal.ofReal B) :
    ∃ u : ℕ → SpatialFreeVector (I := I) R,
      (∀ n, (u n).value = v n) ∧
      Summable (fun n => (u n).form) ∧ (∑' n, (u n).form) ≤ B := by
  have he : (∑' n, E.expectation (A.rankOne (v n))) ≤ ENNReal.ofReal B := by
    rwa [← hv.tsum_eq, E.expectation_tsum hv.summable
      (fun n => hpositive (A.rankOne_positive (v n)))] at hbound
  have hfinite (n : ℕ) : E.expectation (A.rankOne (v n)) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt (he.trans_lt ENNReal.ofReal_lt_top)
  choose u hu hform using fun n => hgraph (v n) (hfinite n)
  refine ⟨u, hu, ?_⟩
  exact PhotonLocalizationFormBounds.source_form_bounds E hpositive hv
    (fun n => (u n).form) (fun n => (u n).form_nonneg) hform hB hbound

end GptLean.PhotonLocalization
