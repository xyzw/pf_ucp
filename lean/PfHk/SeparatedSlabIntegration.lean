import PfHk.SlabBilinearIntegration
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini reduction of separated sphere tests in a bilinear slab form. -/

noncomputable section
namespace PfHk.SeparatedSlabIntegration

open MeasureTheory
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {X H K J : Type*} [MeasurableSpace X] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  {μ : Measure ℝ} {ν : Measure X} [SFinite μ] [SFinite ν]

private theorem real_smul_ae (a : ℝ) (v : Lp H 2 ν) {f : X → H} (hv : v =ᵐ[ν] f) :
    a • v =ᵐ[ν] fun x => a • f x := by
  filter_upwards [Lp.coeFn_smul a v, hv] with x hx hy
  rw [hx, Pi.smul_apply, hy]

theorem form_integral (c : ℝ) (η d r : ℝ → ℝ)
    (v : Lp H 2 ν) (R : ℝ → Lp H 2 ν)
    (A B : J → ℝ → Lp H 2 ν) (q p : ℝ → Lp K 2 ν)
    {vf : X → H} {Rf : ℝ → X → H} {Af Bf : J → ℝ → X → H}
    {qf pf : ℝ → X → K}
    (hv : v =ᵐ[ν] vf) (hR : ∀ t, R t =ᵐ[ν] Rf t)
    (hA : ∀ j t, A j t =ᵐ[ν] Af j t) (hB : ∀ j t, B j t =ᵐ[ν] Bf j t)
    (hq : ∀ t, q t =ᵐ[ν] qf t) (hp : ∀ t, p t =ᵐ[ν] pf t)
    (hI : Integrable (fun z : ℝ × X =>
      inner ℝ ((d z.1+c*η z.1) • vf z.2) (Rf z.1 z.2) +
        (∑ j, inner ℝ (η z.1 • Af j z.1 z.2) (Bf j z.1 z.2)) +
        2 * inner ℝ (η z.1 • qf z.1 z.2) (r z.1 • pf z.1 z.2)) (μ.prod ν)) :
    (∫ z : ℝ × X, inner ℝ ((d z.1+c*η z.1) • vf z.2) (Rf z.1 z.2) +
        (∑ j, inner ℝ (η z.1 • Af j z.1 z.2) (Bf j z.1 z.2)) +
        2 * inner ℝ (η z.1 • qf z.1 z.2) (r z.1 • pf z.1 z.2) ∂μ.prod ν) =
      ∫ t, (d t+c*η t) * inner ℝ v (R t) +
        η t * (∑ j, inner ℝ (A j t) (B j t)) + (r t*η t) * (2 * inner ℝ (q t) (p t)) ∂μ := by
  apply (integral_prod _ hI).trans
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    have he := SlabBilinearIntegration.form_eq_integral
      ((d t+c*η t) • v) (R t) (fun j => η t • A j t) (fun j => B j t)
      (η t • q t) (r t • p t)
      (real_smul_ae _ _ hv) (hR t)
      (fun j => real_smul_ae _ _ (hA j t)) (fun j => hB j t)
      (real_smul_ae _ _ (hq t)) (real_smul_ae _ _ (hp t))
    exact he.symm.trans (SlabBilinearIntegration.separated_density _ _ _ _ _ _ _ _ _ _)

theorem source_integral (η : ℝ → ℝ) (v : Lp H 2 ν) (q : ℝ → Lp H 2 ν)
    {vf : X → H} {qf : ℝ → X → H}
    (hv : v =ᵐ[ν] vf) (hq : ∀ t, q t =ᵐ[ν] qf t)
    (hI : Integrable (fun z : ℝ × X => inner ℝ (η z.1 • vf z.2) (qf z.1 z.2)) (μ.prod ν)) :
    (∫ z : ℝ × X, inner ℝ (η z.1 • vf z.2) (qf z.1 z.2) ∂μ.prod ν) =
      ∫ t, η t * inner ℝ v (q t) ∂μ := by
  apply (integral_prod _ hI).trans
  apply integral_congr_ae
  exact ae_of_all _ fun t =>
    (PfHk.PolarCalculus.l2_inner_eq_integral (η t • v) (q t)
      (real_smul_ae _ _ hv) (hq t)).symm.trans (real_inner_smul_left _ _ _)

end PfHk.SeparatedSlabIntegration
