import GptLean.PhysicalGraphCrossObservable
import GptLean.PhysicalNormalSpectral

/-! Finite normal energy on a closed coercive graph supplies square-summable graph sources. -/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalNormalTrace PhysicalClosedForms
open scoped ENNReal

private theorem domain_of_range {Q H K : Type*}
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
    (g : Q → H × K) (D : H →ₗ.[ℂ] K)
    (hD : (D.graph : Set (H × K)) = Set.range g) (v : H) :
    v ∈ D.domain ↔ ∃ q, (g q).1 = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := LinearPMap.mem_domain_iff.mp hv
    change (v, w) ∈ (D.graph : Set (H × K)) at hw
    rw [hD] at hw
    obtain ⟨q, hq⟩ := hw
    exact ⟨q, congrArg Prod.fst hq⟩
  · rintro ⟨q, hq⟩
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨(g q).2, ?_⟩
    change (v, (g q).2) ∈ (D.graph : Set (H × K))
    rw [hD]
    exact ⟨q, Prod.ext hq rfl⟩

private theorem norm_prod_sq_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (u : E) (v : F) :
    ‖(u, v)‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖u‖ ‖v‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

theorem normalForm_rankOne_finite_iff (v : H) :
    (G.normalForm B S).expectation ((B.realization H).rank.rankOne v) < ⊤ ↔
      ∃ u : E, G.value u = v := by
  have hg : (G.operator.graph : Set (H × K)) = Set.range G.graphMap :=
    congrArg (fun L : Submodule ℂ (H × K) => (L : Set (H × K))) G.operator_graph
  exact (positiveForm_finite_iff (S.resolve H K G.operator G.operator_closed)
    B.normal (B.realization H).functional v).trans
      (domain_of_range G.graphMap G.operator hg v)

theorem normalForm_source_exists {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive)
    (he : (G.normalForm B S).expectation x < ⊤) :
    ∃ u : ℕ → E, HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x ∧
      Summable (fun n => ‖u n‖ ^ 2) := by
  obtain ⟨v, hv⟩ := (B.realization H).spectral x hx
  have hd (n : ℕ) : ∃ u : E, G.value u = v n :=
    (G.normalForm_rankOne_finite_iff B S (v n)).mp
      (PhysicalNormalSpectral.source_form_finite (G.normalForm B S) hv he n)
  choose u hu using hd
  have hs : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x :=
    hv.congr_fun (fun n => congrArg (B.realization H).rank.rankOne (hu n))
  have hm : HasSum (fun n => ‖G.value (u n)‖ ^ 2) ((B.realization H).rank.trace x) := by
    simpa only [(B.realization H).rank.trace_rankOne] using
      (B.realization H).rank.trace.hasSum hs
  have ho : HasSum (fun n => ‖G.output (u n)‖ ^ 2) ((G.normalForm B S).expectation x).toReal := by
    apply (PhysicalNormalSpectral.source_form_hasSum (G.normalForm B S) hs he).congr_fun
    intro n
    exact ((congrArg ENNReal.toReal (G.normalForm_rankOne B S (u n))).trans
      (ENNReal.toReal_ofReal (sq_nonneg _))).symm
  refine ⟨u, hs, Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    ((hm.summable.add ho.summable).mul_left ((G.constant : ℝ) ^ 2))⟩
  intro n
  exact ((pow_le_pow_left₀ (norm_nonneg _) (G.bound (u n)) 2).trans_eq (mul_pow _ _ _)).trans
    (mul_le_mul_of_nonneg_left (norm_prod_sq_le _ _) (sq_nonneg _))

end GptLean.PhysicalGraphForms.CoerciveGraph
