import GptLean.PhysicalGraphRegularization
import GptLean.PhysicalGraphCross
import GptLean.PhotonLocalizationCurrentCutoffPassage

/-!
Bounded current compressions from the constructed graph regularizer.
Symmetry and a graph bound give a quantitative pure and normal error.
-/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalNormalTrace PhysicalClosedForms PhotonLocalizationCurrent
open scoped InnerProductSpace ENNReal

variable {E H K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (G : CoerciveGraph E H K) (J : E →L[ℂ] H)

theorem regularized_current_error (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ u v, ⟪G.value u, J v⟫_ℂ = ⟪J u, G.value v⟫_ℂ)
    (hJ : ∀ u, ‖J u‖ ≤ C * ‖G.output u‖)
    (t : ℝ) (ht : 0 < t) (u : E) :
    |(⟪G.value u, J u⟫_ℂ).re -
      (⟪G.value (G.regularizer t ht.ne' (G.value u)),
        J (G.regularizer t ht.ne' (G.value u))⟫_ℂ).re| ≤
      2 * C * t * ‖G.output u‖ ^ 2 := by
  have hsqrt : Real.sqrt (‖G.output u‖ ^ 2) = ‖G.output u‖ := Real.sqrt_sq (norm_nonneg _)
  apply current_projection_error (G.value u)
    (G.value (G.regularizer t ht.ne' (G.value u))) (J u)
    (J (G.regularizer t ht.ne' (G.value u))) (sq_nonneg _) ht.le
    (hsym _ u)
  · simpa only [hsqrt, mul_comm] using G.regularizer_tail t ht u
  · simpa only [hsqrt] using hJ u
  · rw [hsqrt]
    exact (hJ _).trans (mul_le_mul_of_nonneg_left (G.regularizer_output_contracts t ht u) hC)

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def compressedCurrent (t : ℝ) (ht : t ≠ 0) : B.Trace H →L[ℝ] ℝ :=
  compressedCurrentApproximation (B.realization H).functional
    (G.value.comp (G.regularizer t ht)) (J.comp (G.regularizer t ht))

theorem compressedCurrent_rankOne (t : ℝ) (ht : t ≠ 0) (v : H) :
    G.compressedCurrent J B t ht ((B.realization H).rank.rankOne v) =
      (⟪G.value (G.regularizer t ht v), J (G.regularizer t ht v)⟫_ℂ).re :=
  compressedCurrentApproximation_rankOne (B.realization H).functional _ _ v

theorem compressedCurrent_error (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ u v, ⟪G.value u, J v⟫_ℂ = ⟪J u, G.value v⟫_ℂ)
    (hJ : ∀ u, ‖J u‖ ≤ C * ‖G.output u‖)
    {u : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hs : Summable (fun n => ‖u n‖ ^ 2))
    (t : ℝ) (ht : 0 < t) :
    |G.crossValue B S G.value J x - G.compressedCurrent J B t ht.ne' x| ≤
      2 * C * t * ((G.normalForm B S).expectation x).toReal := by
  have hj := G.crossValue_source_hasSum B S G.value J hu hs
  have ha := (G.compressedCurrent J B t ht.ne').hasSum hu
  have he := G.normalForm_source_hasSum B S hu (summable_norm_sq_map G.output u hs)
  apply (hj.sub ha).norm_le_of_bounded (he.mul_left (2 * C * t))
  intro n
  rw [G.compressedCurrent_rankOne J B]
  exact G.regularized_current_error J C hC hsym hJ t ht (u n)

end GptLean.PhysicalGraphForms.CoerciveGraph
