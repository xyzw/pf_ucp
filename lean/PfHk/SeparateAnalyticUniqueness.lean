import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
Positive-measure uniqueness for separately real-analytic functions. The proof
uses the one-dimensional isolated-zero theorem and finite-dimensional Fubini.
No open subset of the zero set is required.
-/

noncomputable section

namespace PfHk.SeparateAnalyticUniqueness

open MeasureTheory Filter Set
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 400000

/-- Analyticity in each real coordinate, with all other coordinates fixed. -/
def SeparatelyAnalytic {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ (x : Fin n → ℝ) (i : Fin n),
    AnalyticOnNhd ℝ (fun t => f (Function.update x i t)) univ

private theorem ae_ne_zero_one {f : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f univ) (h : ∃ x, f x ≠ 0) :
    ∀ᵐ x ∂volume, f x ≠ 0 := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hz | hn
  · obtain ⟨x, hx⟩ := h
    exact (hx (hz (mem_univ x))).elim
  · have hn' := ae_restrict_le_codiscreteWithin
      (μ := (volume : Measure ℝ)) MeasurableSet.univ hn
    simpa only [Filter.Eventually, Measure.restrict_univ] using hn'

private theorem continuous_fin_cons {n : ℕ} :
    Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => simpa using (continuous_fst : Continuous (fun p : ℝ × (Fin n → ℝ) => p.1))
  | succ j =>
      simpa only [Function.comp_def, Fin.cons_succ] using ((continuous_apply j).comp
        (continuous_snd : Continuous (fun p : ℝ × (Fin n → ℝ) => p.2)))

/-- A nonzero continuous, separately real-analytic function has a null zero set. -/
theorem ae_ne_zero_of_exists_ne_zero {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (ha : SeparatelyAnalytic f) (h : ∃ x, f x ≠ 0) :
    ∀ᵐ x ∂volume, f x ≠ 0 := by
  induction n with
  | zero =>
      obtain ⟨x₀, hx₀⟩ := h
      exact ae_of_all _ fun x => by
        have hx : x = x₀ := funext fun i => Fin.elim0 i
        simpa only [hx] using hx₀
  | succ n ih =>
      obtain ⟨x₀, hx₀⟩ := h
      have ha₀ : AnalyticOnNhd ℝ (fun t => f (Fin.cons t (Fin.tail x₀))) univ := by
        simpa only [Fin.update_cons_zero] using ha (Fin.cons (x₀ 0) (Fin.tail x₀)) 0
      have h₀ : ∀ᵐ t ∂volume, f (Fin.cons t (Fin.tail x₀)) ≠ 0 :=
        ae_ne_zero_one ha₀ ⟨x₀ 0, by simpa using hx₀⟩
      have hslice : ∀ᵐ t ∂volume, ∀ᵐ y ∂volume, f (Fin.cons t y) ≠ 0 := by
        filter_upwards [h₀] with t ht
        apply ih
        · exact hf.comp (continuous_fin_cons.comp (continuous_const.prodMk continuous_id))
        · intro y i
          simpa only [Fin.cons_update] using ha (Fin.cons t y) i.succ
        · exact ⟨Fin.tail x₀, ht⟩
      have hprod : ∀ᵐ p ∂(volume : Measure ℝ).prod
          (volume : Measure (Fin n → ℝ)), f (Fin.cons p.1 p.2) ≠ 0 :=
        (Measure.ae_prod_iff_ae_ae
          ((hf.comp continuous_fin_cons).measurable (measurableSet_singleton 0) |>.compl)).2
          hslice
      have hmap := (volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).quasiMeasurePreserving.ae hprod
      simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
        Fin.removeNth_zero, Fin.cons_self_tail] using hmap

/-- Positive Lebesgue measure of the zero set forces global vanishing. -/
theorem eq_zero_of_measure_zero_set_pos {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (ha : SeparatelyAnalytic f)
    (hz : 0 < volume {x | f x = 0}) : f = 0 := by
  by_contra hn
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have hae := ae_ne_zero_of_exists_ne_zero hf ha hex
  have hnull : volume {x | f x = 0} = 0 := by
    simpa only [ae_iff, not_not] using hae
  exact (ne_of_gt hz) hnull

/-- The zero-set dichotomy in Euclidean coordinates with their usual volume. -/
theorem euclidean_eq_zero_or_ae_ne_zero {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Continuous f)
    (ha : SeparatelyAnalytic (fun x => f (WithLp.toLp 2 x))) :
    f = 0 ∨ ∀ᵐ x ∂volume, f x ≠ 0 := by
  classical
  by_cases hz : f = 0
  · exact Or.inl hz
  right
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  obtain ⟨x₀, hx₀⟩ := hex
  have hc : Continuous (fun x : Fin n → ℝ => f (WithLp.toLp 2 x)) :=
    hf.comp (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
  have hn := ae_ne_zero_of_exists_ne_zero hc ha
    ⟨WithLp.ofLp x₀, by simpa using hx₀⟩
  have hmap := (PiLp.volume_preserving_ofLp (Fin n)).quasiMeasurePreserving.ae hn
  simpa only [WithLp.toLp_ofLp] using hmap

/-- The Euclidean positive-measure uniqueness conclusion. -/
theorem euclidean_eq_zero_of_measure_zero_set_pos {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Continuous f)
    (ha : SeparatelyAnalytic (fun x => f (WithLp.toLp 2 x)))
    (hz : 0 < volume {x | f x = 0}) : f = 0 := by
  rcases euclidean_eq_zero_or_ae_ne_zero hf ha with h | h
  · exact h
  · have hnull : volume {x | f x = 0} = 0 := by
      simpa only [ae_iff, not_not] using h
    exact ((ne_of_gt hz) hnull).elim

end PfHk.SeparateAnalyticUniqueness
