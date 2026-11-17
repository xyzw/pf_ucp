import PfHk.FriedrichsDivergenceBackground
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The ordinary distributional product rule for a smooth scalar cutoff and
a locally integrable vector field. -/

noncomputable section
namespace PfHk.FriedrichsDivergenceBackground

open MeasureTheory GptLean.PhysicalSourceCoordinates
open scoped ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000

def coordinatePartial (χ : Position → ℝ) (i : Fin 3) (x : Position) : ℝ :=
  fderiv ℝ χ x (EuclideanSpace.single i 1)

def truncatedVector (χ : Position → ℝ) (A : Fin 3 → Position → ℝ) : Fin 3 → Position → ℝ :=
  fun i x => χ x * A i x

def truncatedDivergence (χ : Position → ℝ) (A : Fin 3 → Position → ℝ)
    (d : Position → ℝ) : Position → ℝ :=
  fun x => χ x * d x + ∑ i, coordinatePartial χ i x * A i x

theorem coordinatePartial_continuous {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (i : Fin 3) :
    Continuous (coordinatePartial χ i) :=
  (hχ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem coordinatePartial_mul {χ φ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) (x : Position) :
    coordinatePartial (fun y => χ y * φ y) i x = coordinatePartial χ i x * φ x + χ x * coordinatePartial φ i x := by
  unfold coordinatePartial
  change (fderiv ℝ (χ * φ) x) (EuclideanSpace.single i 1) = _
  rw [((hχ.differentiable (by simp) x).hasFDerivAt.mul
    (hφ.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem smooth_mul_of_selected_tests {A : Fin 3 → Position → ℝ} {d χ : Position → ℝ}
    (hA : ∀ i, LocallyIntegrable (A i) volume)
    (hd : LocallyIntegrable d volume) (hχ : ContDiff ℝ ∞ χ)
    (hselected : ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, d x * (χ x * φ x)) =
        -(∑ i, ∫ x, A i x * coordinatePartial (fun y => χ y * φ y) i x)) :
    WeakDivergence (truncatedVector χ A) (truncatedDivergence χ A d) := by
  intro φ hφ hφs
  have hD : Integrable (fun x => d x * (χ x * φ x)) volume := by
    exact hd.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hφ.continuous)
      hφs.mul_left
  have hL (i : Fin 3) : Integrable (fun x => A i x * (coordinatePartial χ i x * φ x)) volume := by
    exact (hA i).integrable_smul_right_of_hasCompactSupport
      ((coordinatePartial_continuous hχ i).mul hφ.continuous) hφs.mul_left
  have hR (i : Fin 3) : Integrable (fun x => A i x * (χ x * coordinatePartial φ i x)) volume := by
    exact (hA i).integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul (coordinatePartial_continuous hφ i))
      (hφs.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hw := hselected φ hφ hφs
  have hsum : (∑ i, ∫ x, A i x * coordinatePartial (fun y => χ y * φ y) i x) =
      (∑ i, ∫ x, A i x * (coordinatePartial χ i x * φ x)) +
        (∑ i, ∫ x, A i x * (χ x * coordinatePartial φ i x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [coordinatePartial_mul hχ hφ, mul_add]
    exact integral_add (hL i) (hR i)
  change (∫ x, (χ x * d x + ∑ i, coordinatePartial χ i x * A i x) * φ x) =
    -(∑ i, ∫ x, (χ x * A i x) * coordinatePartial φ i x)
  calc
    _ = (∫ x, d x * (χ x * φ x)) +
        ∑ i, ∫ x, A i x * (coordinatePartial χ i x * φ x) := by
      have he : (fun x => (χ x * d x + ∑ i, coordinatePartial χ i x * A i x) * φ x) =
          fun x => d x * (χ x * φ x) + ∑ i, A i x * (coordinatePartial χ i x * φ x) := by
        funext x
        rw [add_mul, Finset.sum_mul]
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro i _
          ring
      rw [he, integral_add hD (integrable_finsetSum _ (fun i _ => hL i)),
        integral_finsetSum _ (fun i _ => hL i)]
    _ = -(∑ i, ∫ x, A i x * (χ x * coordinatePartial φ i x)) := by
      rw [hw, hsum]
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

theorem WeakDivergence.smooth_mul {A : Fin 3 → Position → ℝ} {d χ : Position → ℝ}
    (hdiv : WeakDivergence A d) (hA : ∀ i, LocallyIntegrable (A i) volume)
    (hd : LocallyIntegrable d volume) (hχ : ContDiff ℝ ∞ χ) :
    WeakDivergence (truncatedVector χ A) (truncatedDivergence χ A d) := by
  apply smooth_mul_of_selected_tests hA hd hχ
  intro φ hφ hφs
  exact hdiv (fun x => χ x * φ x) (hχ.mul hφ) hφs.mul_left

end PfHk.FriedrichsDivergenceBackground
