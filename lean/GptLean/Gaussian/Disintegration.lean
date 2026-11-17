import GptLean.Gaussian.Series
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
The Gaussian appendix's disintegration lemma in a trace-class Banach interface.
`RankOneData` contains only standard trace-class facts, not a disintegration
theorem. The article-specific series is constructed below. Real functionals
include the real and imaginary parts of pairing with bounded operators.

The uniqueness result assumes integrability of the compared families. This
states explicitly the meaning of the manuscript's displayed integrals.
-/

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Q K T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup K] [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Standard facts about positive rank-one operators in trace norm. -/
structure RankOneData (K T : Type*) [NormedAddCommGroup K] [NormedAddCommGroup T]
    [NormedSpace ℝ T] where
  rankOne : K → T
  continuous_rankOne : Continuous rankOne
  norm_rankOne : ∀ v, ‖rankOne v‖ = ‖v‖ ^ 2
  trace : T →L[ℝ] ℝ
  trace_rankOne : ∀ v, trace (rankOne v) = ‖v‖ ^ 2
  positive : Set T
  closed_positive : IsClosed positive
  zero_positive : (0 : T) ∈ positive
  add_positive : ∀ {x y}, x ∈ positive → y ∈ positive → x + y ∈ positive
  rankOne_positive : ∀ v, rankOne v ∈ positive

variable (R : RankOneData K T)

namespace RankOneData

/-- The actual series used in `lem-soft-disintegration`. -/
noncomputable def density (v : ℕ → Q → K) (u : Q) : T :=
  ∑' n, R.rankOne (v n u)

omit [CompleteSpace T] in
theorem rankOne_aestronglyMeasurable {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ) (n : ℕ) :
    AEStronglyMeasurable (fun u => R.rankOne (v n u)) μ :=
  R.continuous_rankOne.comp_aestronglyMeasurable (hv n)

omit [CompleteSpace T] in
theorem rankOne_total_finite {v : ℕ → Q → K}
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∑' n, ∫⁻ u, ‖R.rankOne (v n u)‖ₑ ∂μ ≠ ⊤ := by
  simpa only [← ofReal_norm, R.norm_rankOne] using hfinite

theorem density_summable_ae {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∀ᵐ u ∂μ, Summable (fun n => R.rankOne (v n u)) :=
  ae_summable_of_finite_total (R.rankOne_aestronglyMeasurable hv)
    (R.rankOne_total_finite hfinite)

theorem density_integrable {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    Integrable (R.density v) μ :=
  integrable_series (R.rankOne_aestronglyMeasurable hv)
    (R.rankOne_total_finite hfinite)

theorem density_positive_ae {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∀ᵐ u ∂μ, R.density v u ∈ R.positive := by
  filter_upwards [R.density_summable_ae hv hfinite] with u hu
  apply R.closed_positive.mem_of_tendsto hu.hasSum
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert n s hn ih =>
    simpa only [Finset.sum_insert hn] using R.add_positive (R.rankOne_positive (v n u)) ih

theorem trace_density_ae {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∀ᵐ u ∂μ, R.trace (R.density v u) = ∑' n, ‖v n u‖ ^ 2 := by
  filter_upwards [R.density_summable_ae hv hfinite] with u hu
  simpa only [density, R.trace_rankOne] using R.trace.map_tsum hu

omit [CompleteSpace T] in
theorem integral_density {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∫ u, R.density v u ∂μ = ∑' n, ∫ u, R.rankOne (v n u) ∂μ :=
  bochner_series_integral (R.rankOne_aestronglyMeasurable hv)
    (R.rankOne_total_finite hfinite)

/-- Total trace is preserved, with the exceptional nonconvergent fibers
handled by almost-everywhere equality rather than a pointwise assertion. -/
theorem total_trace_density {v : ℕ → Q → K}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hfinite : ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ ≠ ⊤) :
    ∫⁻ u, ENNReal.ofReal (R.trace (R.density v u)) ∂μ =
      ∑' n, ∫⁻ u, ENNReal.ofReal (‖v n u‖ ^ 2) ∂μ := by
  rw [← lintegral_tsum (fun n => ((hv n).norm.aemeasurable.pow_const 2).ennreal_ofReal)]
  apply lintegral_congr_ae
  have hnorm := ae_summable_norm_of_finite_total
    (R.rankOne_aestronglyMeasurable hv) (R.rankOne_total_finite hfinite)
  filter_upwards [R.trace_density_ae hv hfinite, hnorm] with u hu hsum
  rw [hu]
  apply ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _)
  simpa only [R.norm_rankOne] using hsum

end RankOneData

omit [CompleteSpace T] in
/-- Testing countably many separating observables yields one common null set.
Only scalar integrability of the tested families is needed. -/
theorem ae_eq_of_countable_scalar_integrals
    (tests : ℕ → T →L[ℝ] ℝ)
    (separate : ∀ x y : T, (∀ n, tests n x = tests n y) → x = y)
    {θ θ' : Q → T} (hθ : ∀ n, Integrable (fun u => tests n (θ u)) μ)
    (hθ' : ∀ n, Integrable (fun u => tests n (θ' u)) μ)
    (htest : ∀ n (s : Set Q), MeasurableSet s →
      ∫ u in s, tests n (θ u) ∂μ = ∫ u in s, tests n (θ' u) ∂μ) :
    θ =ᵐ[μ] θ' := by
  have heach : ∀ n, (fun u => tests n (θ u)) =ᵐ[μ] (fun u => tests n (θ' u)) := by
    intro n
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (hθ n) (hθ' n)
    intro s hs _
    exact htest n s hs
  filter_upwards [ae_all_iff.mpr heach] with u hu
  exact separate (θ u) (θ' u) hu

omit [CompleteSpace T] in
theorem ae_eq_of_countable_observable_integrals
    (tests : ℕ → T →L[ℝ] ℝ)
    (separate : ∀ x y : T, (∀ n, tests n x = tests n y) → x = y)
    {θ θ' : Q → T} (hθ : Integrable θ μ) (hθ' : Integrable θ' μ)
    (htest : ∀ n (s : Set Q), MeasurableSet s →
      ∫ u in s, tests n (θ u) ∂μ = ∫ u in s, tests n (θ' u) ∂μ) :
    θ =ᵐ[μ] θ' :=
  ae_eq_of_countable_scalar_integrals tests separate
    (fun n => (tests n).integrable_comp hθ)
    (fun n => (tests n).integrable_comp hθ') htest

omit [CompleteSpace T] in
/-- All bounded measurable tests include indicator functions. Combined with
countable separation, this proves the appendix's uniqueness claim. -/
theorem ae_eq_of_all_bounded_tests
    (tests : ℕ → T →L[ℝ] ℝ)
    (separate : ∀ x y : T, (∀ n, tests n x = tests n y) → x = y)
    {θ θ' : Q → T} (hθ : ∀ n, Integrable (fun u => tests n (θ u)) μ)
    (hθ' : ∀ n, Integrable (fun u => tests n (θ' u)) μ)
    (htest : ∀ n (f : Q → ℝ), AEStronglyMeasurable f μ →
      (∀ u, ‖f u‖ ≤ 1) →
      ∫ u, f u * tests n (θ u) ∂μ = ∫ u, f u * tests n (θ' u) ∂μ) :
    θ =ᵐ[μ] θ' := by
  apply ae_eq_of_countable_scalar_integrals tests separate hθ hθ'
  intro n s hs
  have hmeas : AEStronglyMeasurable (s.indicator (fun _ : Q => (1 : ℝ))) μ :=
    (stronglyMeasurable_const.indicator hs).aestronglyMeasurable
  have hbound : ∀ u, ‖s.indicator (fun _ : Q => (1 : ℝ)) u‖ ≤ 1 := by
    intro u
    by_cases hu : u ∈ s <;> simp [hu]
  have heq := htest n _ hmeas hbound
  have hind (g : Q → ℝ) :
      (fun u => s.indicator (fun _ : Q => (1 : ℝ)) u * g u) = s.indicator g := by
    funext u
    by_cases hu : u ∈ s <;> simp [hu]
  rw [hind, hind] at heq
  simpa only [integral_indicator hs] using heq

/-- The Bochner integral is the partial trace whenever their bounded-observable
pairings agree. Only countably many separating observables are needed. -/
theorem integral_eq_of_countable_observables
    (tests : ℕ → T →L[ℝ] ℝ)
    (separate : ∀ x y : T, (∀ n, tests n x = tests n y) → x = y)
    {θ : Q → T} (hθ : Integrable θ μ) (partialTrace : T)
    (htest : ∀ n, ∫ u, tests n (θ u) ∂μ = tests n partialTrace) :
    ∫ u, θ u ∂μ = partialTrace := by
  apply separate
  intro n
  rw [← (tests n).integral_comp_comm hθ]
  exact htest n

end GptLean.Gaussian
