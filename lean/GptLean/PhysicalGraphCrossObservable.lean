import GptLean.PhysicalGraphCross
import GptLean.PhysicalNormalStates

/-!
Bounded trace approximants for the polarized graph observable. Their
convergence is derived from the two increasing positive form sequences.
Finite reference-source sums also give positivity-domain additivity.
-/

noncomputable section

namespace GptLean.PhysicalGraphForms

open Filter Topology RemovalState PhysicalClosedForms PhysicalNormalTrace PhysicalNormalStates
open scoped ENNReal

section Positive

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
  {Tr : PositiveTraceData T} (E : PositiveForm Tr)

theorem truncation_tendsto {x : T} (hx : x ∈ Tr.positive) (he : E.expectation x < ⊤) :
    Tendsto (fun n => E.truncation n x) atTop (𝓝 (E.expectation x).toReal) := by
  have h := (ENNReal.tendsto_toReal he.ne).comp
    (tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal (E.monotone x hx hij)))
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (E.nonneg _ x hx)] using h

theorem truncation_le_toReal {x : T} (hx : x ∈ Tr.positive)
    (he : E.expectation x < ⊤) (n : ℕ) : E.truncation n x ≤ (E.expectation x).toReal := by
  have h := ENNReal.toReal_mono he.ne (le_iSup (fun k => ENNReal.ofReal (E.truncation k x)) n)
  simpa only [ENNReal.toReal_ofReal (E.nonneg n x hx)] using h

end Positive

namespace CoerciveGraph

variable {E H K F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (G : CoerciveGraph E H K)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

theorem normalForm_source_finite {u : ℕ → E} {x : B.Trace H}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hs : Summable (fun n => ‖u n‖ ^ 2)) : (G.normalForm B S).expectation x < ⊤ := by
  rw [G.normalForm_source B S hu,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _)
      (summable_norm_sq_map G.output u hs)]
  exact ENNReal.ofReal_lt_top

theorem crossValue_add (L R : E →L[ℂ] F) {x y : B.Trace H}
    (hx : x ∈ (B.traceData (H := H)).positive) (hy : y ∈ (B.traceData (H := H)).positive)
    {u v : ℕ → E}
    (hu : HasSum (fun n => (B.realization H).rank.rankOne (G.value (u n))) x)
    (hv : HasSum (fun n => (B.realization H).rank.rankOne (G.value (v n))) y)
    (hsu : Summable (fun n => ‖u n‖ ^ 2)) (hsv : Summable (fun n => ‖v n‖ ^ 2)) :
    G.crossValue B S L R (x + y) = G.crossValue B S L R x + G.crossValue B S L R y := by
  have hpx := (G.append (L + R)).normalForm_source_finite B S hu hsu
  have hpy := (G.append (L + R)).normalForm_source_finite B S hv hsv
  have hmx := (G.append (L - R)).normalForm_source_finite B S hu hsu
  have hmy := (G.append (L - R)).normalForm_source_finite B S hv hsv
  unfold crossValue
  rw [expectation_add _ hx hy, expectation_add _ hx hy,
    ENNReal.toReal_add hpx.ne hpy.ne, ENNReal.toReal_add hmx.ne hmy.ne]
  ring

theorem crossValue_smul (L R : E →L[ℂ] F) (x : B.Trace H) {r : ℝ} (hr : 0 ≤ r) :
    G.crossValue B S L R (r • x) = r * G.crossValue B S L R x := by
  unfold crossValue
  rw [expectation_smul _ hr, expectation_smul _ hr,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
  ring

theorem crossValue_rankOne (L R : E →L[ℂ] F) (u : E) :
    G.crossValue B S L R ((B.realization H).rank.rankOne (G.value u)) =
      (inner ℂ (L u) (R u)).re := by
  have hp : ((G.append (L + R)).normalForm B S).expectation
      ((B.realization H).rank.rankOne (G.value u)) = ENNReal.ofReal (‖G.appendOutput (L + R) u‖ ^ 2) :=
    (G.append (L + R)).normalForm_rankOne B S u
  have hm : ((G.append (L - R)).normalForm B S).expectation
      ((B.realization H).rank.rankOne (G.value u)) = ENNReal.ofReal (‖G.appendOutput (L - R) u‖ ^ 2) :=
    (G.append (L - R)).normalForm_rankOne B S u
  unfold crossValue
  rw [hp, hm,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _)]
  change ‖G.appendOutput (L + R) u‖ ^ 2 / 4 - ‖G.appendOutput (L - R) u‖ ^ 2 / 4 = _
  rw [G.appendOutput_norm_sq, G.appendOutput_norm_sq]
  simp only [add_apply, sub_apply]
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  ring

def crossObservable (L R : E →L[ℂ] F) (energy : PositiveForm (B.traceData (H := H)))
    (hfinite : ∀ x ∈ (B.traceData (H := H)).positive, energy.expectation x < ⊤ →
      ((G.append (L + R)).normalForm B S).expectation x < ⊤ ∧
        ((G.append (L - R)).normalForm B S).expectation x < ⊤) : FormObservable energy where
  approximation n := (1 / 4 : ℝ) • ((G.append (L + R)).normalForm B S).truncation n -
    (1 / 4 : ℝ) • ((G.append (L - R)).normalForm B S).truncation n
  value := G.crossValue B S L R
  converges x hx he := by
    have hp := truncation_tendsto ((G.append (L + R)).normalForm B S) hx (hfinite x hx he).1
    have hm := truncation_tendsto ((G.append (L - R)).normalForm B S) hx (hfinite x hx he).2
    simpa only [sub_apply, smul_apply, smul_eq_mul, crossValue, div_eq_mul_inv, one_mul,
      mul_comm] using
      (hp.div_const 4).sub (hm.div_const 4)

end CoerciveGraph

end GptLean.PhysicalGraphForms
