import GptLean.PhysicalGraphCurrent

/-! Uniform graph-energy control gives continuity of the normal current pairing. -/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalNormalTrace PhysicalClosedForms PhotonLocalizationCurrent Filter Topology
open scoped ENNReal InnerProductSpace

private theorem tendsto_of_bounded_approximations
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (value : T → ℝ) (approximation : ℕ → T →L[ℝ] ℝ)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (u : ℕ → T) (x : T) (hlim : Tendsto u atTop (𝓝 x))
    (hu : ∀ n k, |value (u n) - approximation k (u n)| ≤ error k)
    (hx : ∀ k, |value x - approximation k x| ≤ error k) :
    Tendsto (fun n => value (u n)) atTop (𝓝 (value x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := (herror.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  have hkconv := ((approximation k).continuous.tendsto x).comp hlim
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hkconv (ε / 3) (by positivity)
  refine ⟨n, fun m hm => ?_⟩
  have h1 := hu m k
  have h3 := hx k
  have h2 := hn m hm
  simp only [Function.comp_def, Real.dist_eq] at h2 ⊢
  have ht := abs_add_three (value (u m) - approximation k (u m))
    (approximation k (u m) - approximation k x) (approximation k x - value x)
  rw [abs_sub_comm (approximation k x)] at ht
  have heq : (value (u m) - approximation k (u m)) +
      (approximation k (u m) - approximation k x) +
      (approximation k x - value x) = value (u m) - value x := by ring
  rw [heq] at ht
  linarith

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K) (J : E →L[ℂ] H)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

theorem current_limit (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ u v, ⟪G.value u, J v⟫_ℂ = ⟪J u, G.value v⟫_ℂ)
    (hJ : ∀ u, ‖J u‖ ≤ C * ‖G.output u‖)
    (u : ℕ → B.Trace H) (x : B.Trace H)
    (hlim : Tendsto u atTop (𝓝 x))
    (source : ∀ n, ∃ v : ℕ → E,
      HasSum (fun k => (B.realization H).rank.rankOne (G.value (v k))) (u n) ∧
        Summable (fun k => ‖v k‖ ^ 2))
    (limitSource : ∃ v : ℕ → E,
      HasSum (fun k => (B.realization H).rank.rankOne (G.value (v k))) x ∧
        Summable (fun k => ‖v k‖ ^ 2))
    (bound : ℝ)
    (hu : ∀ n, ((G.normalForm B S).expectation (u n)).toReal ≤ bound)
    (hx : ((G.normalForm B S).expectation x).toReal ≤ bound) :
    Tendsto (fun n => G.crossValue B S G.value J (u n)) atTop
      (𝓝 (G.crossValue B S G.value J x)) := by
  have hp (k : ℕ) : 0 < energyTail k := by
    unfold energyTail
    positivity
  apply tendsto_of_bounded_approximations (G.crossValue B S G.value J)
    (fun k => G.compressedCurrent J B (energyTail k) (hp k).ne')
    (fun k => 2 * C * energyTail k * bound)
    (by simpa using (energyTail_zero.const_mul (2 * C)).mul_const bound) u x hlim
  · intro n k
    obtain ⟨v, hv, hs⟩ := source n
    exact (G.compressedCurrent_error J B S C hC hsym hJ hv hs (energyTail k) (hp k)).trans
      (mul_le_mul_of_nonneg_left (hu n)
        (mul_nonneg (mul_nonneg (by norm_num) hC) (hp k).le))
  · intro k
    obtain ⟨v, hv, hs⟩ := limitSource
    exact (G.compressedCurrent_error J B S C hC hsym hJ hv hs (energyTail k) (hp k)).trans
      (mul_le_mul_of_nonneg_left hx
        (mul_nonneg (mul_nonneg (by norm_num) hC) (hp k).le))

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] in
theorem append_value_bound (u : E) :
    ‖u‖ ≤ G.constant * ‖(G.append G.value).output u‖ := by
  apply (G.bound u).trans
  apply mul_le_mul_of_nonneg_left _ G.constant.coe_nonneg
  change max ‖G.value u‖ ‖G.output u‖ ≤ ‖G.appendOutput G.value u‖
  have he := G.appendOutput_norm_sq G.value u
  apply max_le
  · nlinarith [sq_nonneg ‖G.output u‖, norm_nonneg (G.value u),
      norm_nonneg (G.appendOutput G.value u)]
  · nlinarith [sq_nonneg ‖G.value u‖, norm_nonneg (G.output u),
      norm_nonneg (G.appendOutput G.value u)]

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] in
theorem operator_append_value_bound (u : E) :
    ‖J u‖ ≤ (‖J‖ * G.constant) * ‖(G.append G.value).output u‖ :=
  (J.le_opNorm u).trans ((mul_le_mul_of_nonneg_left (G.append_value_bound u)
    (ContinuousLinearMap.opNorm_nonneg J)).trans_eq (mul_assoc _ _ _).symm)

end GptLean.PhysicalGraphForms.CoerciveGraph
