import GptLean.PhysicalGraphForms
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
Regularization of a complete graph by orthogonal projection onto its
scaled graph. The cutoff and its energy estimates are constructed using
Hilbert-space projection, without a further spectral-calculus premise.
-/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open scoped InnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem projection_distance_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (L : Submodule ℂ F) [L.HasOrthogonalProjection]
    (v : F) (w : L) : ‖v - L.starProjection v‖ ≤ ‖v - w.val‖ := by
  rw [Submodule.starProjection_minimal]
  apply ciInf_le
  exact ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K)

def scaledGraphEquiv (t : ℝ) (ht : t ≠ 0) : (H × K) ≃L[ℂ] WithLp 2 (H × K) :=
  (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℂ H)
    (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := K)
      (Units.mk0 (t : ℂ) (by exact_mod_cast ht)))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm

def regularizingGraph (t : ℝ) (ht : t ≠ 0) : E →L[ℂ] WithLp 2 (H × K) :=
  (scaledGraphEquiv (H := H) (K := K) t ht).toContinuousLinearMap.comp G.graphMap

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] in
theorem regularizingGraph_apply (t : ℝ) (ht : t ≠ 0) (u : E) :
    G.regularizingGraph t ht u = WithLp.toLp 2 (G.value u, (t : ℂ) • G.output u) := rfl

omit [CompleteSpace E] [CompleteSpace H] [CompleteSpace K] in
theorem regularizingGraph_injective (t : ℝ) (ht : t ≠ 0) :
    Function.Injective (G.regularizingGraph t ht) := by
  intro u v h
  exact G.injective (congrArg (fun z : WithLp 2 (H × K) => z.ofLp.1) h)

omit [CompleteSpace H] [CompleteSpace K] in
theorem regularizingGraph_closed (t : ℝ) (ht : t ≠ 0) :
    IsClosed (Set.range (G.regularizingGraph t ht)) := by
  have h := (scaledGraphEquiv (H := H) (K := K) t ht).toHomeomorph.isClosedMap
    _ G.graphMap_closed
  convert h using 1
  exact Set.range_comp (scaledGraphEquiv (H := H) (K := K) t ht) G.graphMap

instance regularizingGraph_complete (t : ℝ) (ht : t ≠ 0) :
    CompleteSpace (G.regularizingGraph t ht).range :=
  (G.regularizingGraph_closed t ht).completeSpace_coe

def regularizingEmbedding : H →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H K)

def regularizer (t : ℝ) (ht : t ≠ 0) : H →L[ℂ] E :=
  ((G.regularizingGraph t ht).equivRange (G.regularizingGraph_injective t ht)
    (G.regularizingGraph_closed t ht)).symm.toContinuousLinearMap.comp
      ((G.regularizingGraph t ht).range.orthogonalProjectionOnto.comp
        (regularizingEmbedding (H := H) (K := K)))

theorem regularizer_graph (t : ℝ) (ht : t ≠ 0) (v : H) :
    G.regularizingGraph t ht (G.regularizer t ht v) =
      (G.regularizingGraph t ht).range.starProjection (regularizingEmbedding v) := by
  change (G.regularizingGraph t ht)
    (((G.regularizingGraph t ht).equivRange (G.regularizingGraph_injective t ht)
      (G.regularizingGraph_closed t ht)).symm
      ((G.regularizingGraph t ht).range.orthogonalProjectionOnto (regularizingEmbedding v))) = _
  exact congrArg Subtype.val
    (((G.regularizingGraph t ht).equivRange (G.regularizingGraph_injective t ht)
      (G.regularizingGraph_closed t ht)).apply_symm_apply _)

theorem regularizer_error_sq (t : ℝ) (ht : t ≠ 0) (u : E) :
    ‖G.value u - G.value (G.regularizer t ht (G.value u))‖ ^ 2 +
      t ^ 2 * ‖G.output (G.regularizer t ht (G.value u))‖ ^ 2 ≤
        t ^ 2 * ‖G.output u‖ ^ 2 := by
  let L := G.regularizingGraph t ht
  let v := regularizingEmbedding (K := K) (G.value u)
  have hdist : ‖v - L.range.starProjection v‖ ≤ ‖v - L u‖ := by
    exact projection_distance_le L.range v ⟨L u, L.mem_range_self u⟩
  have hs := sq_le_sq₀ (norm_nonneg (v - L.range.starProjection v))
    (norm_nonneg (v - L u)) |>.mpr hdist
  rw [← G.regularizer_graph t ht (G.value u)] at hs
  change ‖WithLp.toLp 2 (G.value u - G.value (G.regularizer t ht (G.value u)),
      (0 : K) - (t : ℂ) • G.output (G.regularizer t ht (G.value u)))‖ ^ 2 ≤
    ‖WithLp.toLp 2 (G.value u - G.value u, (0 : K) - (t : ℂ) • G.output u)‖ ^ 2 at hs
  simpa only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, sub_self, zero_sub,
    norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs] using hs

theorem regularizer_output_contracts (t : ℝ) (ht : 0 < t) (u : E) :
    ‖G.output (G.regularizer t ht.ne' (G.value u))‖ ≤ ‖G.output u‖ := by
  have h := G.regularizer_error_sq t ht.ne' u
  have hs : ‖G.output (G.regularizer t ht.ne' (G.value u))‖ ^ 2 ≤ ‖G.output u‖ ^ 2 := by
    nlinarith [sq_nonneg ‖G.value u - G.value (G.regularizer t ht.ne' (G.value u))‖,
      sq_pos_of_pos ht]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem regularizer_tail (t : ℝ) (ht : 0 < t) (u : E) :
    ‖G.value u - G.value (G.regularizer t ht.ne' (G.value u))‖ ≤ t * ‖G.output u‖ := by
  have h := G.regularizer_error_sq t ht.ne' u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht.le (norm_nonneg _))).mp
  rw [mul_pow]
  exact (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans h

theorem regularizer_value_contracts (t : ℝ) (ht : t ≠ 0) (v : H) :
    ‖G.value (G.regularizer t ht v)‖ ≤ ‖v‖ := by
  have h₁ := WithLp.norm_fst_le H (G.regularizingGraph t ht (G.regularizer t ht v))
  have h₂ := (G.regularizingGraph t ht).range.norm_starProjection_apply_le
    (regularizingEmbedding (H := H) (K := K) v)
  rw [← G.regularizer_graph t ht v] at h₂
  have hnorm : ‖regularizingEmbedding (H := H) (K := K) v‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (v, (0 : K))‖ ^ 2 = ‖v‖ ^ 2
    simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact h₁.trans (h₂.trans_eq hnorm)

end GptLean.PhysicalGraphForms.CoerciveGraph
