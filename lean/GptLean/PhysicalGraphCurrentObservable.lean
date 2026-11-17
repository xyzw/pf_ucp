import GptLean.PhysicalGraphSources
import GptLean.PhysicalGraphCurrent

/-! The graph regularizer constructs the relative current approximation interface. -/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalNormalTrace PhysicalClosedForms RemovalState PhotonLocalizationCurrent Filter Topology
open scoped ENNReal InnerProductSpace

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K) (J : E →L[ℂ] H)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  (C : ℝ) (hC : 0 ≤ C)
  (hsym : ∀ u v, ⟪G.value u, J v⟫_ℂ = ⟪J u, G.value v⟫_ℂ)
  (hJ : ∀ u, ‖J u‖ ≤ C * ‖G.output u‖)

private theorem energyTail_pos (n : ℕ) : 0 < energyTail n := by
  unfold energyTail
  positivity

include hC hsym hJ in
theorem current_error (n : ℕ) {x : B.Trace H}
    (hx : x ∈ (B.realization H).rank.positive)
    (he : (G.normalForm B S).expectation x < ⊤) :
    |G.crossValue B S G.value J x -
      G.compressedCurrent J B (energyTail n) (energyTail_pos n).ne' x| ≤
        2 * C * energyTail n * ((G.normalForm B S).expectation x).toReal := by
  obtain ⟨u, hu, hs⟩ := G.normalForm_source_exists B S hx he
  exact G.compressedCurrent_error J B S C hC hsym hJ hu hs (energyTail n) (energyTail_pos n)

def currentObservable : FormObservable (G.normalForm B S) where
  approximation n := G.compressedCurrent J B (energyTail n) (energyTail_pos n).ne'
  value := G.crossValue B S G.value J
  converges x hx he := by
    have hr : Tendsto (fun n => 2 * C * energyTail n *
        ((G.normalForm B S).expectation x).toReal) atTop (𝓝 0) := by
      simpa using (energyTail_zero.const_mul (2 * C)).mul_const
        ((G.normalForm B S).expectation x).toReal
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds hε))
    refine ⟨n, fun m hm => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact (G.current_error J B S C hC hsym hJ m hx he).trans_lt (hn m hm)

def currentRelativeApproximation : RelativeApproximation (R := (B.realization H).rank)
    (G.normalForm B S) (G.currentObservable J B S C hC hsym hJ) where
  rate n := 4 * C * energyTail n
  nonneg n := mul_nonneg (mul_nonneg (by norm_num) hC) (energyTail_nonneg n)
  tends_zero := by simpa using energyTail_zero.const_mul (4 * C)
  pure_bound n m hnm v hv := by
    have hp := (B.realization H).rank.rankOne_positive v
    have hm := G.current_error J B S C hC hsym hJ m hp hv
    have hn := G.current_error J B S C hC hsym hJ n hp hv
    have hrate : 2 * C * energyTail m *
        ((G.normalForm B S).expectation ((B.realization H).rank.rankOne v)).toReal ≤
      2 * C * energyTail n *
        ((G.normalForm B S).expectation ((B.realization H).rank.rankOne v)).toReal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (energyTail_antitone hnm)
          (mul_nonneg (by norm_num) hC)) ENNReal.toReal_nonneg
    have ht := abs_sub_le
      (G.compressedCurrent J B (energyTail m) (energyTail_pos m).ne'
        ((B.realization H).rank.rankOne v))
      (G.crossValue B S G.value J ((B.realization H).rank.rankOne v))
      (G.compressedCurrent J B (energyTail n) (energyTail_pos n).ne'
        ((B.realization H).rank.rankOne v))
    rw [abs_sub_comm _ (G.crossValue B S G.value J _)] at ht
    exact ht.trans ((add_le_add (hm.trans hrate) hn).trans_eq (by ring))

end GptLean.PhysicalGraphForms.CoerciveGraph
