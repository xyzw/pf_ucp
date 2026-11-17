import GptLean.RemovalState
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Unbounded positive form expectations of the actual Bochner aggregate.
An expectation is defined by increasing bounded spectral truncations, as in
the standard trace of a nonnegative self-adjoint operator against a positive
trace-class operator. Only positivity and monotonicity of the bounded traces
are supplied. The sum/integral formula and finite-energy state construction
are proved, including initially infinite expectations.
-/

namespace GptLean.RemovalState

open MeasureTheory Filter
open scoped ENNReal

variable {Q T : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Bounded spectral truncations of a nonnegative form observable. -/
structure PositiveForm (R : PositiveTraceData T) where
  truncation : ℕ → T →L[ℝ] ℝ
  nonneg : ∀ n, ∀ x ∈ R.positive, 0 ≤ truncation n x
  monotone : ∀ x ∈ R.positive, Monotone (fun n => truncation n x)

namespace PositiveForm

variable {R : PositiveTraceData T} (E : PositiveForm R)

/-- The full unbounded expectation, with infinity retained. -/
noncomputable def expectation (x : T) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (E.truncation n x)

omit [CompleteSpace T] in
theorem measurable_expectation {G : Q → T} (hG : AEStronglyMeasurable G μ) :
    AEMeasurable (fun q => E.expectation (G q)) μ := by
  exact AEMeasurable.iSup (fun n =>
    ((E.truncation n).continuous.comp_aestronglyMeasurable hG).aemeasurable.ennreal_ofReal)

private theorem iSup_tsum_of_monotone (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n => f n a)) :
    (⨆ n, ∑' a, f n a) = ∑' a, ⨆ n, f n a := by
  simpa only [lintegral_count] using
    (lintegral_iSup (μ := Measure.count) (fun n => measurable_of_countable (f n))
      (fun n m hnm a => hf a hnm)).symm

omit [CompleteSpace T] in
/-- Spectral truncation commutes with a trace-norm convergent positive
series. This applies to the actual rank-one channel series. -/
theorem expectation_tsum {v : ℕ → T} (hs : Summable v)
    (hpos : ∀ a, v a ∈ R.positive) :
    E.expectation (∑' a, v a) = ∑' a, E.expectation (v a) := by
  unfold expectation
  have he (n : ℕ) : ENNReal.ofReal (E.truncation n (∑' a, v a)) =
      ∑' a, ENNReal.ofReal (E.truncation n (v a)) := by
    rw [(E.truncation n).map_tsum hs]
    exact ENNReal.ofReal_tsum_of_nonneg (fun a => E.nonneg n _ (hpos a))
      (((E.truncation n).hasSum hs.hasSum).summable)
  simp_rw [he]
  exact iSup_tsum_of_monotone _ (fun a n m hnm =>
    ENNReal.ofReal_le_ofReal (E.monotone _ (hpos a) hnm))

/-- The actual operator series converges in trace norm from the summable
integrated norms of its conditional terms. -/
theorem aggregate_hasSum_of_norm {G : ℕ → Q → T}
    (hs : Summable (fun a => ∫ q, ‖G a q‖ ∂μ)) :
    HasSum (fun a => ∫ q, G a q ∂μ) (aggregate G μ) := by
  exact (hs.of_norm_bounded (fun a => norm_integral_le_integral_norm (G a))).hasSum

/-- Monotone convergence proves the unbounded form identity for the
constructed aggregate. Finite output energy is not a hypothesis. -/
theorem expectation_aggregate {G : ℕ → Q → T}
    (hG : ∀ a, Integrable (G a) μ)
    (hpos : ∀ a, ∀ᵐ q ∂μ, G a q ∈ R.positive)
    (hs : Summable (fun a => ∫ q, ‖G a q‖ ∂μ)) :
    E.expectation (aggregate G μ) = ∑' a, ∫⁻ q, E.expectation (G a q) ∂μ := by
  have hagg := aggregate_hasSum_of_norm hs
  have htr (n : ℕ) : ENNReal.ofReal (E.truncation n (aggregate G μ)) =
      ∑' a, ∫⁻ q, ENNReal.ofReal (E.truncation n (G a q)) ∂μ := by
    have hi (a : ℕ) := (E.truncation n).integrable_comp (hG a)
    have he (a : ℕ) : (∫ q, E.truncation n (G a q) ∂μ) =
        E.truncation n (∫ q, G a q ∂μ) :=
      (E.truncation n).integral_comp_comm (hG a)
    have hsum : Summable (fun a => ∫ q, E.truncation n (G a q) ∂μ) := by
      simpa only [he] using ((E.truncation n).hasSum hagg).summable
    have hnonneg (a : ℕ) : 0 ≤ᵐ[μ] fun q => E.truncation n (G a q) :=
      (hpos a).mono (fun q hq => E.nonneg n _ hq)
    rw [show E.truncation n (aggregate G μ) =
      ∑' a, ∫ q, E.truncation n (G a q) ∂μ from by
        simp only [he]
        exact ((E.truncation n).hasSum hagg).tsum_eq.symm]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun a => integral_nonneg_of_ae (hnonneg a)) hsum]
    exact tsum_congr (fun a => ofReal_integral_eq_lintegral_ofReal (hi a) (hnonneg a))
  unfold expectation
  simp_rw [htr]
  rw [iSup_tsum_of_monotone]
  · apply tsum_congr
    intro a
    apply (lintegral_iSup' (fun n =>
      ((E.truncation n).continuous.comp_aestronglyMeasurable (hG a).1).aemeasurable.ennreal_ofReal)
      ((hpos a).mono (fun q hq n m hnm => ENNReal.ofReal_le_ofReal
        (E.monotone _ hq hnm)))).symm
  · intro a n m hnm
    apply lintegral_mono_ae
    exact (hpos a).mono (fun q hq => ENNReal.ofReal_le_ofReal (E.monotone _ hq hnm))

/-- Finite energy follows from an integrable summable conditional energy
majorant. The conditional bound need only hold almost everywhere. -/
theorem expectation_aggregate_le {G : ℕ → Q → T} {bound : ℕ → Q → ℝ}
    (hG : ∀ a, Integrable (G a) μ)
    (hpos : ∀ a, ∀ᵐ q ∂μ, G a q ∈ R.positive)
    (hs : Summable (fun a => ∫ q, ‖G a q‖ ∂μ))
    (hb : ∀ a, Integrable (bound a) μ)
    (hbpos : ∀ a, ∀ᵐ q ∂μ, 0 ≤ bound a q)
    (hbs : Summable (fun a => ∫ q, bound a q ∂μ))
    (hbound : ∀ a, ∀ᵐ q ∂μ, E.expectation (G a q) ≤ ENNReal.ofReal (bound a q)) :
    E.expectation (aggregate G μ) ≤ ENNReal.ofReal (∑' a, ∫ q, bound a q ∂μ) := by
  rw [E.expectation_aggregate hG hpos hs,
    ENNReal.ofReal_tsum_of_nonneg (fun a => integral_nonneg_of_ae (hbpos a)) hbs]
  apply ENNReal.tsum_le_tsum
  intro a
  rw [ofReal_integral_eq_lintegral_ofReal (hb a) (hbpos a)]
  exact lintegral_mono_ae (hbound a)

/-- Normalized positive finite-energy operators. The energy is not made
real-valued until after its finiteness has been established. -/
def State := {x : T // x ∈ R.positive ∧ R.trace x = 1 ∧ E.expectation x < ⊤}

/-- The output operator is the explicit Bochner aggregate. Its positivity,
normalization and form-domain finiteness follow from the conditional data. -/
noncomputable def stateOfConditional [IsProbabilityMeasure μ]
    {θ G : ℕ → Q → T} {B : ℝ}
    (hθ : ∀ a, Integrable (θ a) μ) (hG : ∀ a, AEStronglyMeasurable (G a) μ)
    (hθpos : ∀ a, ∀ᵐ q ∂μ, θ a q ∈ R.positive)
    (hGpos : ∀ a, ∀ᵐ q ∂μ, G a q ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ q ∂μ, R.trace (G a q) = R.trace (θ a q))
    (hmass : HasSum (fun a => ∫ q, R.trace (θ a q) ∂μ) 1)
    (henergy : (∑' a, ∫⁻ q, E.expectation (G a q) ∂μ) ≤ ENNReal.ofReal B) : E.State := by
  have hGi := fun a => R.repaired_integrable (hθ a) (hG a) (hθpos a) (hGpos a) (htrace a)
  have hs : Summable (fun a => ∫ q, ‖G a q‖ ∂μ) := by
    simpa only [R.repaired_norm_integral (hGpos _) (htrace _)] using hmass.summable
  obtain ⟨hp, ht⟩ := R.normalized_aggregate hθ hG hθpos hGpos htrace hmass
  refine ⟨aggregate G μ, hp, ht, ?_⟩
  rw [E.expectation_aggregate hGi hGpos hs]
  exact henergy.trans_lt ENNReal.ofReal_lt_top

end PositiveForm

end GptLean.RemovalState
