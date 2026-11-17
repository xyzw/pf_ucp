import GptLean.RemovalSourceProduct

/-!
Exact vector-valued source marginals from original spectral tests. The
source marginal terms are arbitrary Banach-space integrals with the
standard rank-one test formula and trace-norm bound. Their summability
and target are conclusions, using the actual localized WIS vectors.
-/

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory

variable {Q X H K F Test : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Original spectral hard tests determine the exact source marginal
series. There is no conditional marginal or localized sum premise. -/
theorem localizedFiber_product_marginal_hasSum
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (B : Test → Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν))
    (W : Test → X → H →L[ℂ] H) (Wtarget : Test → Q × X → K →L[ℂ] K)
    (C Ctarget : Test → ℝ)
    (hW : ∀ t, ∀ᵐ x ∂ν, ‖W t x‖ ≤ C t)
    (hWt : ∀ t, ∀ᵐ qx ∂μ.prod ν, ‖Wtarget t qx‖ ≤ Ctarget t)
    (hmt : ∀ t (v : Lp K 2 (μ.prod ν)),
      AEStronglyMeasurable (fun qx => Wtarget t qx (v qx)) (μ.prod ν))
    (hsource_rankOne : ∀ t (v : Lp H 2 ν), inner ℂ v (conjugatedOperator U (B t) v) =
      ∫ x, inner ℂ (v x) (W t x (v x)) ∂ν)
    (htarget_rankOne : ∀ t (v : Lp K 2 (μ.prod ν)), inner ℂ v (B t v) =
      ∫ qx, inner ℂ (v qx) (Wtarget t qx (v qx)) ∂μ.prod ν)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (ψ : ℕ → Lp H 2 ν)
    (hmeas : ∀ t n, AEStronglyMeasurable (fun x => W t x (ψ n x)) ν)
    (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (sourceMarginal : ℕ → F) (target : F) (tests : Test → F →L[ℝ] ℝ)
    (separate : ∀ a b : F, (∀ t, tests t a = tests t b) → a = b)
    (Cmarginal : ℝ)
    (hbound : ∀ i, ‖sourceMarginal i‖ ≤ Cmarginal *
      ‖localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2)
    (htest : ∀ t i, tests t (sourceMarginal i) =
      (∫ q, ∫ x, inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
        (Wtarget t (q, x) (localizedFiber U f hpart hf ψ i (q, x))) ∂ν ∂μ).re)
    (hsource : ∀ t, HasSum
      (fun n => inner ℂ (ψ n) (conjugatedOperator U (B t) (ψ n))) (tests t target : ℂ)) :
    HasSum sourceMarginal target := by
  have hm : Summable (fun i =>
      ‖localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2) := by
    simpa only [Repair.flattenVectors] using
      (Repair.flattenVectors_mass (fun n => localizedVector_mass f hpart hf (ψ n)) hmass).summable
  have hs : Summable sourceMarginal := Summable.of_norm_bounded (hm.mul_left Cmarginal) hbound
  have he : (∑' i, sourceMarginal i) = target := by
    apply separate
    intro t
    have ht := localizedFiber_product_test_hasSum U (B t) (W t) (Wtarget t)
      (hW t) (hWt t) (hmt t) (hsource_rankOne t) (htarget_rankOne t)
      f hpart hf ψ (hmeas t) hmass.summable (hsource t)
    have hreal : HasSum (fun i => tests t (sourceMarginal i)) (tests t target) := by
      simpa only [← htest t, Complex.ofReal_re] using Complex.hasSum_re ht
    exact ((tests t).hasSum hs.hasSum).unique hreal
  exact he ▸ hs.hasSum

end GptLean.RemovalSource
