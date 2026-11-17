import GptLean.Gaussian.Series
import Mathlib.Analysis.Convex.Integral

/-!
The operator assembly in Step 5 of exact soft-photon removal.
The output is defined as the countable sum of Bochner integrals of the
conditional repaired operators. Positivity, convergence in trace norm,
normalization and bounded-observable identities are conclusions.

`PositiveTraceData` records standard facts of the trace-class Banach space.
Conditional channel measurability and pointwise preservation are inputs.
The physical multiplication channels and their unbounded energy/form-domain
identities are not constructed here.
-/

namespace GptLean.RemovalState

open MeasureTheory Filter

variable {Q T F : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Standard positivity and trace-norm facts, with no removal construction. -/
structure PositiveTraceData (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] where
  trace : T →L[ℝ] ℝ
  positive : Set T
  closed_positive : IsClosed positive
  convex_positive : Convex ℝ positive
  zero_positive : (0 : T) ∈ positive
  add_positive : ∀ {x y}, x ∈ positive → y ∈ positive → x + y ∈ positive
  norm_eq_trace : ∀ {x}, x ∈ positive → ‖x‖ = trace x

/-- The state is built from the conditional operators, rather than supplied. -/
noncomputable def aggregate (G : ℕ → Q → T) (μ : Measure Q) : T :=
  ∑' a, ∫ u, G a u ∂μ

namespace PositiveTraceData

variable (R : PositiveTraceData T)

omit [CompleteSpace T] in
/-- Trace preservation transfers integrability to a measurable positive output. -/
theorem repaired_integrable {θ η : Q → T}
    (hθ : Integrable θ μ) (hη : AEStronglyMeasurable η μ)
    (hθpos : ∀ᵐ u ∂μ, θ u ∈ R.positive) (hηpos : ∀ᵐ u ∂μ, η u ∈ R.positive)
    (htrace : ∀ᵐ u ∂μ, R.trace (η u) = R.trace (θ u)) : Integrable η μ := by
  apply hθ.norm.mono' hη
  filter_upwards [hθpos, hηpos, htrace] with u hu hv ht
  rw [R.norm_eq_trace hv, R.norm_eq_trace hu, ht]

omit [CompleteSpace T] in
theorem repaired_norm_integral {θ η : Q → T}
    (hηpos : ∀ᵐ u ∂μ, η u ∈ R.positive)
    (htrace : ∀ᵐ u ∂μ, R.trace (η u) = R.trace (θ u)) :
    (∫ u, ‖η u‖ ∂μ) = ∫ u, R.trace (θ u) ∂μ := by
  apply integral_congr_ae
  filter_upwards [hηpos, htrace] with u hu ht
  exact (R.norm_eq_trace hu).trans ht

/-- Summability of conditional input traces controls the actual output operators. -/
theorem aggregate_hasSum {θ η : ℕ → Q → T}
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hs : Summable (fun a => ∫ u, R.trace (θ a u) ∂μ)) :
    HasSum (fun a => ∫ u, η a u ∂μ) (aggregate η μ) := by
  have hs' : Summable (fun a => ∫ u, ‖η a u‖ ∂μ) := by
    simpa only [R.repaired_norm_integral (hηpos _) (htrace _)] using hs
  exact (hs'.of_norm_bounded (fun a => norm_integral_le_integral_norm (η a))).hasSum

omit [CompleteSpace T] in
theorem aggregate_eq_integral {θ η : ℕ → Q → T}
    (hθ : ∀ a, Integrable (θ a) μ) (hη : ∀ a, AEStronglyMeasurable (η a) μ)
    (hθpos : ∀ a, ∀ᵐ u ∂μ, θ a u ∈ R.positive)
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hs : Summable (fun a => ∫ u, R.trace (θ a u) ∂μ)) :
    aggregate η μ = ∫ u, ∑' a, η a u ∂μ := by
  apply integral_tsum_of_summable_integral_norm
  · exact fun a => R.repaired_integrable (hθ a) (hη a) (hθpos a) (hηpos a) (htrace a)
  · simpa only [R.repaired_norm_integral (hηpos _) (htrace _)] using hs

theorem aggregate_positive [IsProbabilityMeasure μ] {θ η : ℕ → Q → T}
    (hθ : ∀ a, Integrable (θ a) μ) (hη : ∀ a, AEStronglyMeasurable (η a) μ)
    (hθpos : ∀ a, ∀ᵐ u ∂μ, θ a u ∈ R.positive)
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hs : Summable (fun a => ∫ u, R.trace (θ a u) ∂μ)) :
    aggregate η μ ∈ R.positive := by
  apply R.closed_positive.mem_of_tendsto
    (R.aggregate_hasSum hηpos htrace hs)
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using R.zero_positive
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply R.add_positive _ ih
    exact R.convex_positive.integral_mem R.closed_positive (hηpos a)
      (R.repaired_integrable (hθ a) (hη a) (hθpos a) (hηpos a) (htrace a))

/-- Exact trace normalization follows from the input conditional masses. -/
theorem trace_aggregate {θ η : ℕ → Q → T}
    (hθ : ∀ a, Integrable (θ a) μ) (hη : ∀ a, AEStronglyMeasurable (η a) μ)
    (hθpos : ∀ a, ∀ᵐ u ∂μ, θ a u ∈ R.positive)
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hs : Summable (fun a => ∫ u, R.trace (θ a u) ∂μ)) :
    R.trace (aggregate η μ) = ∑' a, ∫ u, R.trace (θ a u) ∂μ := by
  rw [aggregate, R.trace.map_tsum (R.aggregate_hasSum hηpos htrace hs).summable]
  apply tsum_congr
  intro a
  rw [← R.trace.integral_comp_comm
    (R.repaired_integrable (hθ a) (hη a) (hθpos a) (hηpos a) (htrace a))]
  exact integral_congr_ae (htrace a)

/-- The constructed aggregate is a normalized positive state. -/
theorem normalized_aggregate [IsProbabilityMeasure μ] {θ η : ℕ → Q → T}
    (hθ : ∀ a, Integrable (θ a) μ) (hη : ∀ a, AEStronglyMeasurable (η a) μ)
    (hθpos : ∀ a, ∀ᵐ u ∂μ, θ a u ∈ R.positive)
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hmass : HasSum (fun a => ∫ u, R.trace (θ a u) ∂μ) 1) :
    aggregate η μ ∈ R.positive ∧ R.trace (aggregate η μ) = 1 := by
  refine ⟨R.aggregate_positive hθ hη hθpos hηpos htrace hmass.summable, ?_⟩
  rw [R.trace_aggregate hθ hη hθpos hηpos htrace hmass.summable, hmass.tsum_eq]

/-- Local preservation passes through both the Bochner integral and countable sum.
The codomain can itself be a trace-class Banach space, so this includes marginals. -/
theorem aggregate_preserves [CompleteSpace F] (B : T →L[ℝ] F) {θ η : ℕ → Q → T}
    (hθ : ∀ a, Integrable (θ a) μ) (hη : ∀ a, AEStronglyMeasurable (η a) μ)
    (hθpos : ∀ a, ∀ᵐ u ∂μ, θ a u ∈ R.positive)
    (hηpos : ∀ a, ∀ᵐ u ∂μ, η a u ∈ R.positive)
    (htrace : ∀ a, ∀ᵐ u ∂μ, R.trace (η a u) = R.trace (θ a u))
    (hs : Summable (fun a => ∫ u, R.trace (θ a u) ∂μ))
    (hB : ∀ a, ∀ᵐ u ∂μ, B (η a u) = B (θ a u)) :
    B (aggregate η μ) = B (aggregate θ μ) := by
  have hηs := (R.aggregate_hasSum hηpos htrace hs).summable
  have hθs := (R.aggregate_hasSum hθpos
    (fun _ => Eventually.of_forall (fun _ => rfl)) hs).summable
  rw [aggregate, aggregate, B.map_tsum hηs, B.map_tsum hθs]
  apply tsum_congr
  intro a
  rw [← B.integral_comp_comm
    (R.repaired_integrable (hθ a) (hη a) (hθpos a) (hηpos a) (htrace a)),
    ← B.integral_comp_comm (hθ a)]
  exact integral_congr_ae (hB a)

end PositiveTraceData

end GptLean.RemovalState
