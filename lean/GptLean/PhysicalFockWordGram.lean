import GptLean.PhysicalFockWordContraction

/-!
Finite creation-word overlaps are determined by one-photon Gram entries.
This follows from the actual mixed CCR and the actual vacuum, rather than
an assumed characteristic-function formula for the localization channel.
-/

noncomputable section
namespace GptLean.PhysicalFock.WordGram

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem creationBlock_inner (n : ℕ) (f : Lp ℂ 2 μ) (u v : Fock μ) :
    ⟪creationBlock μ n f u, v⟫_ℂ = ⟪u, annihilationBlock μ n f v⟫_ℂ := by
  change ⟪lp.single 2 (n + 1) (creationSector μ n f (u n)), v⟫_ℂ =
    ⟪u, lp.single 2 n (annihilationSector μ n f (v (n + 1)))⟫_ℂ
  rw [lp.inner_single_left, lp.inner_single_right]
  exact ((creationSector μ n f).adjoint_inner_right (u n) (v (n + 1))).symm

theorem creationFinite_inner (M : ℕ) (f : Lp ℂ 2 μ) (u v : Fock μ) :
    ⟪creationFinite μ M f u, v⟫_ℂ = ⟪u, annihilationFinite μ (M + 1) f v⟫_ℂ := by
  simp only [creationFinite, annihilationFinite, sum_apply, sum_inner, inner_sum,
    creationBlock_inner]

variable (C : CanonicalSectorCCR μ)

include C in
theorem word_cons_inner (f : Lp ℂ 2 μ) (w z : List (Lp ℂ 2 μ)) :
    ⟪creationWord μ (f :: w), creationWord μ z⟫_ℂ =
      ⟪creationWord μ w, wordContraction μ f z⟫_ℂ := by
  rw [← creationFinite_word μ (w.length + z.length) f w (by omega), creationFinite_inner,
    annihilationFinite_word μ C _ f z (by omega)]

theorem vacuum_word_inner (z : List (Lp ℂ 2 μ)) :
    ⟪creationWord μ [], creationWord μ z⟫_ℂ = if z = [] then 1 else 0 := by
  cases z with
  | nil =>
    rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, vacuum_norm]
    norm_num
  | cons f z =>
    change ⟪lp.single 2 0 (vacuumSector μ),
      lp.single 2 (z.length + 1) (creationWordSector μ (f :: z))⟫_ℂ = _
    rw [lp.inner_single_left, lp.single_apply_ne _ _ _ (by omega), inner_zero_right]
    simp

private def deleteEval {α : Type*} (c : α → ℂ) :
    List α → (List α → ℂ) → ℂ
  | [], _ => 0
  | a :: w, F => c a * F w + deleteEval c w (fun v => F (a :: v))

private theorem deleteEval_congr {α : Type*} (c d : α → ℂ) (w : List α)
    (F G : List α → ℂ) (hc : ∀ a, c a = d a) (hF : ∀ v, F v = G v) :
    deleteEval c w F = deleteEval d w G := by
  induction w generalizing F G with
  | nil => rfl
  | cons a w ih =>
    simp only [deleteEval, hc]
    rw [hF w, ih _ _ (fun v => hF (a :: v))]

omit [SigmaFinite μ] in
private theorem contractionTerms_eval {E : Type*} (a : E → Lp ℂ 2 μ)
    (f : Lp ℂ 2 μ) (z : List E) (F : List (Lp ℂ 2 μ) → ℂ) :
    ((wordContractionTerms μ f (z.map a)).map (fun p => p.1 * F p.2)).sum =
      deleteEval (fun b => ⟪f, a b⟫_ℂ) z (fun v => F (v.map a)) := by
  induction z generalizing F with
  | nil => simp [wordContractionTerms, deleteEval]
  | cons b z ih =>
    simp only [List.map_cons, wordContractionTerms, List.map_map, List.sum_cons,
      deleteEval, Function.comp_def]
    rw [ih (fun v => F (a b :: v))]

private theorem inner_contraction (u : Fock μ) (f : Lp ℂ 2 μ)
    (z : List (Lp ℂ 2 μ)) :
    ⟪u, wordContraction μ f z⟫_ℂ =
      ((wordContractionTerms μ f z).map
        (fun p => p.1 * ⟪u, creationWord μ p.2⟫_ℂ)).sum := by
  unfold wordContraction
  induction wordContractionTerms μ f z with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, inner_add_right, inner_smul_right, ih]

include C in
/-- Every finite creation-word overlap depends only on the corresponding
one-photon inner products, even when the two kernel families differ. -/
theorem word_inner_of_gram {E F : Type*}
    (a a' : E → Lp ℂ 2 μ) (b b' : F → Lp ℂ 2 μ)
    (hgram : ∀ e f, ⟪a e, b f⟫_ℂ = ⟪a' e, b' f⟫_ℂ)
    (w : List E) (z : List F) :
    ⟪creationWord μ (w.map a), creationWord μ (z.map b)⟫_ℂ =
      ⟪creationWord μ (w.map a'), creationWord μ (z.map b')⟫_ℂ := by
  induction w generalizing z with
  | nil => simp only [List.map_nil, vacuum_word_inner, List.map_eq_nil_iff]
  | cons e w ih =>
    simp only [List.map_cons, word_cons_inner μ C, inner_contraction]
    have hleft := contractionTerms_eval μ b (a e) z
      (fun v => ⟪creationWord μ (w.map a), creationWord μ v⟫_ℂ)
    have hright := contractionTerms_eval μ b' (a' e) z
      (fun v => ⟪creationWord μ (w.map a'), creationWord μ v⟫_ℂ)
    exact hleft.trans ((deleteEval_congr _ _ z _ _ (hgram e) (fun v => ih v)).trans hright.symm)

end GptLean.PhysicalFock.WordGram
