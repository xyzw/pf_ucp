import GptLean.PhotonLocalizationSpectralTrace

/-!
Finite-rank approximation follows directly from a compact graph inclusion.
The construction uses finite nets and their orthogonal spans, so the local
Hilbert space may depend on the cutoffs and need not have a basis indexed
by the natural numbers.
-/

noncomputable section
namespace GptLean.PhotonLocalization

open Filter Topology PhotonTrace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compactness of the graph unit ball constructs an actual finite-rank
orthogonal projection with uniform error measured by the graph norm. -/
theorem exists_finite_projection_of_compact_graph
    (J : V →L[ℂ] H) (hcompact : TotallyBounded (J '' Metric.closedBall (0 : V) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : H →L[ℂ] H, IsFiniteRankProj P ∧
      ∀ v, ‖(1 - P) (J v)‖ ≤ ε * ‖v‖ := by
  classical
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp hcompact ε hε
  let W : Submodule ℂ H := Submodule.span ℂ s
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hs
  let P : H →L[ℂ] H := W.starProjection
  have hfinite : FiniteDimensional ℂ P.range := by
    change FiniteDimensional ℂ W.starProjection.range
    rw [Submodule.range_starProjection]
    infer_instance
  have hunit : ∀ v : V, ‖v‖ = 1 → ‖((1 - P).comp J) v‖ ≤ ε := by
    intro v hv
    have hvball : v ∈ Metric.closedBall (0 : V) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, hv] using le_refl (1 : ℝ)
    obtain ⟨y, hy, hnear⟩ := Set.mem_iUnion₂.mp (hcover ⟨v, hvball, rfl⟩)
    have hyW : y ∈ W := Submodule.subset_span hy
    have hzero : Wᗮ.starProjection y = 0 := by
      rw [W.starProjection_orthogonal_val, W.starProjection_eq_self_iff.mpr hyW, sub_self]
    calc
      ‖((1 - P).comp J) v‖ = ‖Wᗮ.starProjection (J v - y)‖ := by
        rw [map_sub, hzero, sub_zero, W.starProjection_orthogonal_val]
        rfl
      _ ≤ ‖J v - y‖ := Wᗮ.norm_starProjection_apply_le _
      _ ≤ ε := (show ‖J v - y‖ < ε by
        simpa only [Metric.mem_ball, dist_eq_norm] using hnear).le
  have hop : ‖(1 - P).comp J‖ ≤ ε :=
    ContinuousLinearMap.opNorm_le_of_unit_norm hε.le hunit
  exact ⟨P, isFiniteRankProj_of_finite_range
    isStarProjection_starProjection hfinite,
    fun v => ((1 - P).comp J).le_of_opNorm_le hop v⟩

/-- The approximation has the same inverse-cutoff squared-error scale as
the spectral tail bound, without choosing a common local eigenbasis. -/
theorem exists_projection_graph_tail
    (J : V →L[ℂ] H) (hcompact : TotallyBounded (J '' Metric.closedBall (0 : V) 1))
    (s : ℕ) :
    ∃ P : H →L[ℂ] H, IsFiniteRankProj P ∧
      ∀ v, ‖(1 - P) (J v)‖ ^ 2 ≤ ‖v‖ ^ 2 / (s + 1) := by
  have hd : (0 : ℝ) < s + 1 := by positivity
  obtain ⟨P, hP, herr⟩ := exists_finite_projection_of_compact_graph J hcompact
    (inv_pos.mpr (Real.sqrt_pos.2 hd))
  refine ⟨P, hP, fun v => ?_⟩
  have he := pow_le_pow_left₀ (norm_nonneg _) (herr v) 2
  simpa only [mul_pow, inv_pow, Real.sq_sqrt hd.le, div_eq_mul_inv, mul_comm] using he

end GptLean.PhotonLocalization
