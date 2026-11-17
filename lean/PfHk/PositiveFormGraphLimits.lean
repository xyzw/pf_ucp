import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Graph convergence implies form convergence for a positive sum of
squares. Bounded weights then pass an inequality from a core sequence to
its operator graph limit. These are proved Hilbert-space facts. -/

noncomputable section
namespace PfHk.PositiveFormGraphLimits

open Filter
open scoped Topology InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

variable {I Q H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def form (D : I → Q →L[ℂ] H) (R P : Q →L[ℂ] H) (u v : Q) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ⟪D i u, D i v⟫_ℂ + ⟪R u, R v⟫_ℂ + ⟪P u, P v⟫_ℂ

def IsGraph (J : Q →L[ℂ] H) (D : I → Q →L[ℂ] H) (R P : Q →L[ℂ] H)
    (u : Q) (f : H) : Prop := ∀ v, form D R P v u = ⟪J v, f⟫_ℂ

variable (J : Q →L[ℂ] H) (D : I → Q →L[ℂ] H) (R P : Q →L[ℂ] H)

theorem form_sub_right (w u v : Q) :
    form D R P w (u - v) = form D R P w u - form D R P w v := by
  simp only [form, map_sub, inner_sub_right, Finset.sum_sub_distrib]
  ring

theorem IsGraph.sub {u v : Q} {f g : H}
    (hu : IsGraph J D R P u f) (hv : IsGraph J D R P v g) :
    IsGraph J D R P (u - v) (f - g) := by
  intro w
  exact (form_sub_right D R P w u v).trans
    ((congrArg₂ (fun z t : ℂ => z - t) (hu w) (hv w)).trans (inner_sub_right _ _ _).symm)

private theorem real_self (u : H) : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm

private theorem imag_self (u : H) : (⟪u, u⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) u

theorem form_diagonal (u : Q) : (form D R P u u).re =
    (1 / 2 : ℝ) * (∑ i, ‖D i u‖ ^ 2) + ‖R u‖ ^ 2 + ‖P u‖ ^ 2 := by
  simp only [form, Complex.add_re, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.one_re, Complex.one_im, Complex.re_sum, Complex.im_sum, real_self,
    imag_self]
  norm_num

theorem graph_difference_energy {u v : Q} {f g : H}
    (hu : IsGraph J D R P u f) (hv : IsGraph J D R P v g) :
    (1 / 2 : ℝ) * (∑ i, ‖D i u - D i v‖ ^ 2) +
      ‖R u - R v‖ ^ 2 + ‖P u - P v‖ ^ 2 ≤ ‖J u - J v‖ * ‖f - g‖ := by
  have h := hu.sub J D R P hv (u - v)
  have hd := (form_diagonal D R P (u - v)).symm.trans (congrArg Complex.re h)
  have he := hd.le.trans (re_inner_le_norm (𝕜 := ℂ) (J (u - v)) (f - g))
  simpa only [map_sub] using he

theorem graph_difference_covariant_sq {u v : Q} {f g : H}
    (hu : IsGraph J D R P u f) (hv : IsGraph J D R P v g) (i : I) :
    ‖D i u - D i v‖ ^ 2 ≤ 2 * (‖J u - J v‖ * ‖f - g‖) := by
  have he := graph_difference_energy J D R P hu hv
  have hi : ‖D i u - D i v‖ ^ 2 ≤ ∑ j, ‖D j u - D j v‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖D j u - D j v‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith [sq_nonneg ‖R u - R v‖, sq_nonneg ‖P u - P v‖]

theorem graph_difference_radiation_sq {u v : Q} {f g : H}
    (hu : IsGraph J D R P u f) (hv : IsGraph J D R P v g) :
    ‖R u - R v‖ ^ 2 ≤ ‖J u - J v‖ * ‖f - g‖ := by
  have he := graph_difference_energy J D R P hu hv
  have hk : 0 ≤ ∑ j, ‖D j u - D j v‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith [sq_nonneg ‖P u - P v‖]

private theorem tendsto_of_sq_norm_sub {z : ℕ → H} {v : H}
    (h : Tendsto (fun n => ‖z n - v‖ ^ 2) atTop (𝓝 0)) : Tendsto z atTop (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

theorem form_convergence {u : ℕ → Q} {v : Q} {f : ℕ → H} {g : H}
    (hu : ∀ n, IsGraph J D R P (u n) (f n)) (hv : IsGraph J D R P v g)
    (hJ : Tendsto (fun n => J (u n)) atTop (𝓝 (J v)))
    (hf : Tendsto f atTop (𝓝 g)) :
    (∀ i, Tendsto (fun n => D i (u n)) atTop (𝓝 (D i v))) ∧
      Tendsto (fun n => R (u n)) atTop (𝓝 (R v)) := by
  have hp : Tendsto (fun n => ‖J (u n) - J v‖ * ‖f n - g‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((hJ.sub (tendsto_const_nhds (x := J v))).norm.mul
        (hf.sub (tendsto_const_nhds (x := g))).norm)
  constructor
  · intro i
    apply tendsto_of_sq_norm_sub
    exact squeeze_zero (fun n => sq_nonneg _)
      (fun n => graph_difference_covariant_sq J D R P (hu n) hv i)
      (by simpa only [mul_zero] using hp.const_mul 2)
  · apply tendsto_of_sq_norm_sub
    exact squeeze_zero (fun n => sq_nonneg _)
      (fun n => graph_difference_radiation_sq J D R P (hu n) hv) hp

/-- Every fixed bounded weight can be inserted after graph-to-form
convergence. On a fixed annulus the scalar Carleman weights have this form. -/
theorem weighted_estimate_limit {u : ℕ → Q} {v : Q} {f : ℕ → H} {g : H}
    (hu : ∀ n, IsGraph J D R P (u n) (f n)) (hv : IsGraph J D R P v g)
    (hJ : Tendsto (fun n => J (u n)) atTop (𝓝 (J v)))
    (hf : Tendsto f atTop (𝓝 g))
    (W₀ W₁ Wᵣ Wf : H →L[ℂ] H) (a b c : ℝ)
    (hest : ∀ n, a * ‖W₀ (J (u n))‖ ^ 2 + b * (∑ i, ‖W₁ (D i (u n))‖ ^ 2) +
      c * ‖Wᵣ (R (u n))‖ ^ 2 ≤ ‖Wf (f n)‖ ^ 2) :
    a * ‖W₀ (J v)‖ ^ 2 + b * (∑ i, ‖W₁ (D i v)‖ ^ 2) +
      c * ‖Wᵣ (R v)‖ ^ 2 ≤ ‖Wf g‖ ^ 2 := by
  obtain ⟨hD, hR⟩ := form_convergence J D R P hu hv hJ hf
  have h₀ := (((W₀.continuous.tendsto (J v)).comp hJ).norm.pow 2).const_mul a
  have h₁ := (tendsto_finsetSum Finset.univ
    (fun i _ => ((W₁.continuous.tendsto (D i v)).comp (hD i)).norm.pow 2)).const_mul b
  have hᵣ := (((Wᵣ.continuous.tendsto (R v)).comp hR).norm.pow 2).const_mul c
  have hright := ((Wf.continuous.tendsto g).comp hf).norm.pow 2
  exact le_of_tendsto_of_tendsto' ((h₀.add h₁).add hᵣ) hright hest

end PfHk.PositiveFormGraphLimits
