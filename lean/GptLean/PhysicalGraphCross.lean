import GptLean.PhysicalGraphForms

/-!
Polarization of normal graph forms defines mixed bilinear observables.
Their values are independent of the square-summable reference source.
Both positive forms used here have explicitly constructed closed graphs.
-/

noncomputable section

namespace GptLean.PhysicalGraphForms.CoerciveGraph

open PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

variable {E H K F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (G : CoerciveGraph E H K)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

omit [CompleteSpace E] [CompleteSpace F] in
theorem summable_norm_sq_map (L : E →L[ℂ] F) (u : ℕ → E)
    (hu : Summable (fun n => ‖u n‖ ^ 2)) : Summable (fun n => ‖L (u n)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hu.mul_left (‖L‖ ^ 2))
  intro n
  exact (pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (u n)) 2).trans_eq (mul_pow _ _ _)

def crossValue (L R : E →L[ℂ] F) (x : B.Trace H) : ℝ :=
  (((G.append (L + R)).normalForm B S).expectation x).toReal / 4 -
    (((G.append (L - R)).normalForm B S).expectation x).toReal / 4

theorem crossValue_source_hasSum (L R : E →L[ℂ] F) {u : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hs : Summable (fun n => ‖u n‖ ^ 2)) :
    HasSum (fun n => (⟪L (u n), R (u n)⟫_ℂ).re) (G.crossValue B S L R x) := by
  have hp := (G.append (L + R)).normalForm_source_hasSum B S hu
    (summable_norm_sq_map (G.appendOutput (L + R)) u hs)
  have hm := (G.append (L - R)).normalForm_source_hasSum B S hu
    (summable_norm_sq_map (G.appendOutput (L - R)) u hs)
  apply ((hp.div_const 4).sub (hm.div_const 4)).congr_fun
  intro n
  symm
  change ‖G.appendOutput (L + R) (u n)‖ ^ 2 / 4 -
    ‖G.appendOutput (L - R) (u n)‖ ^ 2 / 4 = _
  rw [G.appendOutput_norm_sq, G.appendOutput_norm_sq]
  simp only [add_apply, sub_apply]
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  ring

include S in
theorem crossValue_source_independent (L R : E →L[ℂ] F)
    {u v : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hv : HasSum (fun n => (B.realization H).rank.rankOne (G.value (v n))) x)
    (hsu : Summable (fun n => ‖u n‖ ^ 2))
    (hsv : Summable (fun n => ‖v n‖ ^ 2)) :
    (∑' n, (⟪L (u n), R (u n)⟫_ℂ).re) =
      ∑' n, (⟪L (v n), R (v n)⟫_ℂ).re :=
  (G.crossValue_source_hasSum B S L R hu hsu).tsum_eq.trans
    (G.crossValue_source_hasSum B S L R hv hsv).tsum_eq.symm

end GptLean.PhysicalGraphForms.CoerciveGraph
