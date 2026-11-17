import PfHk.SpinfulCounterexampleField
import PfHk.PauliClassicalCurl

/-! Distributional magnetic curl and local bounds for the cylindrical family. -/

noncomputable section
namespace PfHk.SpinfulCounterexampleMagnetic

open MeasureTheory Filter PfHk.SpinfulCounterexampleField
open scoped ContDiff ENNReal

set_option Elab.async false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types true

private def coordinateDerivative (f : Space → ℝ) (j : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

private theorem partial_contDiff {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative f j) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem integral_partial_mul {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (j : Fin 3) :
    (∫ x, coordinateDerivative f j x * φ x) = -(∫ x, f x * coordinateDerivative φ j x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Space))
    (((partial_contDiff hf j).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left)
    ((hf.continuous.mul (partial_contDiff hφ j).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left)
    ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x, f x * coordinateDerivative φ j x) = -(∫ x, coordinateDerivative f j x * φ x) at h
  linarith


theorem weakCurl_vectorPotential (t : ℝ) (k : Fin 3) :
    PauliClassicalCurl.WeakCurlPairOn Set.univ
      (fun j x => vectorPotential t x j) (k + 1) (k + 2)
      (fun x => curl (vectorPotential t) x k) := by
  intro φ hφ hs _
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun x => vectorPotential t x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp (contDiff_vectorPotential t)
  have hpart (i j : Fin 3) (x : Space) :
      coordinateDerivative (fun y => vectorPotential t y j) i x =
        fderiv ℝ (vectorPotential t) x (EuclideanSpace.single i 1) j := by
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        ((contDiff_vectorPotential t).differentiable (by simp) x).hasFDerivAt).fderiv)
  have hcurl (x : Space) : curl (vectorPotential t) x k =
      coordinateDerivative (fun y => vectorPotential t y (k + 2)) (k + 1) x -
        coordinateDerivative (fun y => vectorPotential t y (k + 1)) (k + 2) x := by
    simp only [hpart]
    fin_cases k <;> rfl
  have hi (i j : Fin 3) : Integrable
      (fun x => coordinateDerivative (fun y => vectorPotential t y j) i x * φ x) volume :=
    ((partial_contDiff (hcoord j) i).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hs.mul_left
  have h1 := integral_partial_mul (hcoord (k + 2)) hφ hs (k + 1)
  have h2 := integral_partial_mul (hcoord (k + 1)) hφ hs (k + 2)
  calc
    (∫ x, curl (vectorPotential t) x k * φ x) =
        (∫ x, coordinateDerivative (fun y => vectorPotential t y (k + 2)) (k + 1) x * φ x) -
          (∫ x, coordinateDerivative (fun y => vectorPotential t y (k + 1)) (k + 2) x * φ x) := by
      simp_rw [hcurl, sub_mul]
      exact integral_sub (hi _ _) (hi _ _)
    _ = _ := by
      change _ = (∫ x, vectorPotential t x (k + 1) * coordinateDerivative φ (k + 2) x) -
        ∫ x, vectorPotential t x (k + 2) * coordinateDerivative φ (k + 1) x
      linarith

theorem curl_coordinate_memLp_top (t : ℝ) (k : Fin 3) :
    MemLp (fun x => curl (vectorPotential t) x k) ∞ volume := by
  have hsq : MemLp (fun x => weight x ^ 2) ∞ volume := by
    apply (weight_memLp_top.mul weight_memLp_top).ae_eq
    exact ae_of_all _ fun x => by simp [pow_two]
  apply ((hsq.const_mul (2 * t)).mul_const ((EuclideanSpace.single 2 (1 : ℝ)) k)).ae_eq
  exact ae_of_all _ fun x => by simp [magnetic_field]

end PfHk.SpinfulCounterexampleMagnetic
