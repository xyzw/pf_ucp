import PfHk.WeakDivergenceProduct
import PfHk.CoordinateCoefficientLocalization

/-! Local distributional divergence and smooth truncation. Only tests
supported in the specified coordinate ball are used. Zero extension is
used for integration witnesses, never asserted to preserve divergence. -/

noncomputable section
namespace PfHk.FriedrichsDivergenceBackground

open MeasureTheory GptLean.PhysicalSourceCoordinates
open PfHk.CoordinateCoefficientLocalization
open scoped ENNReal ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000

def WeakDivergenceOn (s : Set Position) (A : Fin 3 → Position → ℝ)
    (d : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ s →
    (∫ x, d x * φ x) = -(∑ i, ∫ x, A i x * coordinatePartial φ i x)

theorem zeroExtension_test_mul (o : Position) (ρ : ℝ) (b ψ : Position → ℝ)
    (hψ : tsupport ψ ⊆ Metric.ball o ρ) (x : Position) :
    zeroExtension o ρ b x * ψ x = b x * ψ x := by
  by_cases hx : x ∈ Metric.ball o ρ
  · simp [zeroExtension, hx]
  · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψ h))
    simp [hz]

theorem WeakDivergenceOn.smooth_mul_ball {p q : ℝ≥0∞} {o : Position} {ρ : ℝ}
    {A : Fin 3 → Position → ℝ} {d χ : Position → ℝ}
    (hdiv : WeakDivergenceOn (Metric.ball o ρ) A d) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hA : ∀ i, MemLp (A i) p (volume.restrict (Metric.ball o ρ)))
    (hd : MemLp d q (volume.restrict (Metric.ball o ρ)))
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Metric.ball o ρ) :
    WeakDivergence (truncatedVector χ A) (truncatedDivergence χ A d) := by
  let A₀ := fun i => zeroExtension o ρ (A i)
  let d₀ := zeroExtension o ρ d
  have hA₀ (i : Fin 3) : LocallyIntegrable (A₀ i) volume :=
    (zeroExtension_memLp o ρ (A i) (hA i)).locallyIntegrable hp
  have hd₀ : LocallyIntegrable d₀ volume := (zeroExtension_memLp o ρ d hd).locallyIntegrable hq
  have hselected : ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, d₀ x * (χ x * φ x)) =
        -(∑ i, ∫ x, A₀ i x * coordinatePartial (fun y => χ y * φ y) i x) := by
    intro φ hφ hφs
    have hψ : tsupport (fun x => χ x * φ x) ⊆ Metric.ball o ρ :=
      tsupport_mul_subset_left.trans hχs
    have hw := hdiv (fun x => χ x * φ x) (hχ.mul hφ) hφs.mul_left hψ
    have hl : (∫ x, d₀ x * (χ x * φ x)) = ∫ x, d x * (χ x * φ x) := by
      apply integral_congr_ae
      exact ae_of_all _ (zeroExtension_test_mul o ρ d _ hψ)
    have hr : (∑ i, ∫ x, A₀ i x * coordinatePartial (fun y => χ y * φ y) i x) =
        ∑ i, ∫ x, A i x * coordinatePartial (fun y => χ y * φ y) i x := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact ae_of_all _ (zeroExtension_test_mul o ρ (A i) _
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hψ))
    exact hl.trans (hw.trans (congrArg Neg.neg hr.symm))
  have hglobal := smooth_mul_of_selected_tests hA₀ hd₀ hχ hselected
  have hvec : truncatedVector χ A₀ = truncatedVector χ A := by
    funext i x
    change χ x * zeroExtension o ρ (A i) x = χ x * A i x
    simpa only [mul_comm] using zeroExtension_test_mul o ρ (A i) χ hχs x
  have hdivg : truncatedDivergence χ A₀ d₀ = truncatedDivergence χ A d := by
    funext x
    apply congrArg₂ (fun a b : ℝ => a + b)
    · change χ x * zeroExtension o ρ d x = χ x * d x
      simpa only [mul_comm] using zeroExtension_test_mul o ρ d χ hχs x
    · apply Finset.sum_congr rfl
      intro i _
      change coordinatePartial χ i x * zeroExtension o ρ (A i) x = coordinatePartial χ i x * A i x
      simpa only [mul_comm] using zeroExtension_test_mul o ρ (A i) (coordinatePartial χ i)
        ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hχs) x
  exact (congrArg₂ WeakDivergence hvec hdivg).mp hglobal

end PfHk.FriedrichsDivergenceBackground
