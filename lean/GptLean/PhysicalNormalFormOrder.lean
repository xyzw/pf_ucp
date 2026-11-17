import GptLean.PhysicalNormalTrace
import GptLean.PositiveForm

/-!
Universal normal extensions of scaled positive form orders. The trace
mass term is identified with the sum of source norm squares, and all
expectations retain infinity throughout the argument.
-/

noncomputable section

namespace GptLean.PhysicalNormalFormOrder

open PhysicalNormalTrace PhotonLocalizationChannel RemovalState
open scoped ENNReal

variable {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData H T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)

private theorem source_expectation (E : PositiveForm (positiveTrace normal F))
    {v : ℕ → H} {x : T} (hv : HasSum (fun n => R.rankOne (v n)) x) :
    E.expectation x = ∑' n, E.expectation (R.rankOne (v n)) := by
  rw [← hv.tsum_eq]
  exact E.expectation_tsum hv.summable (fun n => R.rankOne_positive (v n))

omit [InnerProductSpace ℂ H] [CompleteSpace H] [CompleteSpace T] in
private theorem source_mass {v : ℕ → H} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    ENNReal.ofReal (R.trace x) = ∑' n, ENNReal.ofReal (‖v n‖ ^ 2) := by
  have hs : HasSum (fun n => ‖v n‖ ^ 2) (R.trace x) := by
    simpa only [R.trace_rankOne] using R.trace.hasSum hv
  rw [← hs.tsum_eq]
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs.summable

theorem expectation_le_mul_of_rankOne (E G : PositiveForm (positiveTrace normal F))
    (a : ℝ≥0∞) (h : ∀ v, E.expectation (R.rankOne v) ≤ a * G.expectation (R.rankOne v))
    {x : T} (hx : x ∈ R.positive) : E.expectation x ≤ a * G.expectation x := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  rw [source_expectation normal F E hv, source_expectation normal F G hv,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => h (v n)

theorem expectation_le_mul_add_mass_of_rankOne
    (E G : PositiveForm (positiveTrace normal F)) (a : ℝ≥0∞)
    (h : ∀ v, E.expectation (R.rankOne v) ≤
      a * (G.expectation (R.rankOne v) + ENNReal.ofReal (‖v‖ ^ 2)))
    {x : T} (hx : x ∈ R.positive) :
    E.expectation x ≤ a * (G.expectation x + ENNReal.ofReal (R.trace x)) := by
  obtain ⟨v, hv⟩ := normal.positive_decomposition x hx
  calc
    E.expectation x = ∑' n, E.expectation (R.rankOne (v n)) :=
      source_expectation normal F E hv
    _ ≤ ∑' n, a * (G.expectation (R.rankOne (v n)) + ENNReal.ofReal (‖v n‖ ^ 2)) :=
      ENNReal.tsum_le_tsum fun n => h (v n)
    _ = a * ((∑' n, G.expectation (R.rankOne (v n))) +
        ∑' n, ENNReal.ofReal (‖v n‖ ^ 2)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ = a * (G.expectation x + ENNReal.ofReal (R.trace x)) := by
      rw [← source_expectation normal F G hv, ← source_mass hv]

end GptLean.PhysicalNormalFormOrder
