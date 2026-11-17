import PfHk.CutoffKernel
import GptLean.PhysicalSmearedKernel

/-!
Fourier transversality of the density-weighted potential difference.
The physical continuity equation holds for every bounded-gradient gauge.
Sine and cosine gauges therefore give the momentum-space identity directly.
-/

noncomputable section

namespace PfHk

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.TransformationsGauge GptLean.PhysicalFock GptLean.Gaussian
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

theorem sine_phase_derivative (k x : Position) (a : Fin 3) :
    fderiv ℝ (fun y => Real.sin (inner ℝ k y)) x (EuclideanSpace.single a 1) =
      Real.cos (inner ℝ k x) * k a := by
  change fderiv ℝ (fun y => Real.sin ((innerSL ℝ k) y)) x _ = _
  rw [fderiv_sin (innerSL ℝ k).differentiableAt, (innerSL ℝ k).fderiv]
  simp [EuclideanSpace.inner_single_right]

theorem cosine_phase_derivative (k x : Position) (a : Fin 3) :
    fderiv ℝ (fun y => Real.cos (inner ℝ k y)) x (EuclideanSpace.single a 1) =
      -Real.sin (inner ℝ k x) * k a := by
  change fderiv ℝ (fun y => Real.cos ((innerSL ℝ k) y)) x _ = _
  rw [fderiv_cos (innerSL ℝ k).differentiableAt, (innerSL ℝ k).fderiv]
  simp [EuclideanSpace.inner_single_right]

def sineGauge (k : Position) : SpatialGauge where
  fn x := Real.sin (inner ℝ k x)
  differentiable := (innerSL ℝ k).differentiable.sin
  derivativeBound := ∑ a : Fin 3, |k a|
  derivative_bounded a x := by
    rw [sine_phase_derivative, abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg (k a))).trans
      (by simpa using Finset.single_le_sum (fun b _ => abs_nonneg (k b)) (Finset.mem_univ a))

def cosineGauge (k : Position) : SpatialGauge where
  fn x := Real.cos (inner ℝ k x)
  differentiable := (innerSL ℝ k).differentiable.cos
  derivativeBound := ∑ a : Fin 3, |k a|
  derivative_bounded a x := by
    rw [cosine_phase_derivative, abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg (k a))).trans
      (by simpa using Finset.single_le_sum (fun b _ => abs_nonneg (k b)) (Finset.mem_univ a))

theorem sineGauge_gradient (k x : Position) :
    (sineGauge k).gradientVector x = Real.cos (inner ℝ k x) • k := by
  apply PiLp.ext
  intro a
  exact sine_phase_derivative k x a

theorem cosineGauge_gradient (k x : Position) :
    (cosineGauge k).gradientVector x = -Real.sin (inner ℝ k x) • k := by
  apply PiLp.ext
  intro a
  exact cosine_phase_derivative k x a

theorem fieldPhase_re (k x : Position) :
    (fieldPhase k x).re = Real.cos (inner ℝ k x) := by
  simp [fieldPhase, Complex.exp_re]

theorem fieldPhase_im (k x : Position) :
    (fieldPhase k x).im = -Real.sin (inner ℝ k x) := by
  simp [fieldPhase, Complex.exp_im]

/-- Taking the dot product with momentum commutes with the L¹ Fourier
transform. The convention is the existing unnormalized transform. -/
theorem longitudinal_fourier_integral {b : Position → Vector}
    (hb : Integrable b volume) (k : Position) :
    (∑ μ : Fin 3, (k μ : ℂ) * fourierCoeff (fun x => b x μ) k) =
      ∫ x, fieldPhase k x * ((inner ℝ k (b x) : ℝ) : ℂ) := by
  have hc (μ : Fin 3) : Integrable (fun x => b x μ) volume :=
    (EuclideanSpace.proj μ : Vector →L[ℝ] ℝ).integrable_comp hb
  have hi (μ : Fin 3) : Integrable
      (fun x => (k μ : ℂ) * (fieldPhase k x * (b x μ : ℂ))) volume :=
    (integrable_phase_mul _ (hc μ) k).const_mul _
  calc
    _ = ∑ μ : Fin 3, ∫ x, (k μ : ℂ) * (fieldPhase k x * (b x μ : ℂ)) := by
      simp only [GptLean.PhysicalGroundState.fourierCoeff, integral_const_mul]
    _ = ∫ x, ∑ μ : Fin 3, (k μ : ℂ) * (fieldPhase k x * (b x μ : ℂ)) :=
      (integral_finsetSum _ fun μ _ => hi μ).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro μ _
        ring

/-- Bounded-gradient stationarity implies pointwise Fourier transversality.
The proof uses the sine and cosine gauges explicitly. -/
theorem fourier_transverse_of_gauge_tests {b : Position → Vector}
    (hb : Integrable b volume)
    (hdiv : ∀ g : SpatialGauge, ∫ x, inner ℝ (g.gradientVector x) (b x) = 0)
    (k : Position) :
    (∑ μ : Fin 3, (k μ : ℂ) * fourierCoeff (fun x => b x μ) k) = 0 := by
  have hcos := hdiv (sineGauge k)
  have hsin := hdiv (cosineGauge k)
  simp only [sineGauge_gradient, real_inner_smul_left] at hcos
  simp only [cosineGauge_gradient, real_inner_smul_left] at hsin
  have hdot : Integrable (fun x => inner ℝ k (b x)) volume :=
    (innerSL ℝ k).integrable_comp hb
  have hint := integrable_phase_mul _ hdot k
  rw [longitudinal_fourier_integral hb k]
  apply Complex.ext
  · change (∫ x, fieldPhase k x * ((inner ℝ k (b x) : ℝ) : ℂ)).re = 0
    refine (integral_re hint).symm.trans ?_
    calc
      _ = ∫ x, Real.cos (inner ℝ k x) * inner ℝ k (b x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp [fieldPhase_re]
      _ = 0 := hcos
  · change (∫ x, fieldPhase k x * ((inner ℝ k (b x) : ℝ) : ℂ)).im = 0
    refine (integral_im hint).symm.trans ?_
    calc
      _ = ∫ x, -Real.sin (inner ℝ k x) * inner ℝ k (b x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by simp [fieldPhase_im]
      _ = 0 := hsin

/-- The two transverse directions together with momentum separate vectors.
This uses the actual orthonormal polarization frame from `gpt_lean`. -/
theorem frame_zero_of_components (F : PhysicalPolarization.Frame)
    (k v : Position) (hk : k ≠ 0)
    (htrans : ∀ l : Fin 2, inner ℝ (F.epsilon k l) v = 0)
    (hlong : inner ℝ k v = 0) : v = 0 := by
  have hlast : inner ℝ (F.basis k 2) v = 0 := by
    rw [F.radial k hk, real_inner_smul_left, hlong, mul_zero]
  have hall (a : Fin 3) : inner ℝ (F.basis k a) v = 0 := by
    fin_cases a
    · exact htrans 0
    · exact htrans 1
    · exact hlast
  apply (F.basis k).repr.injective
  apply PiLp.ext
  intro a
  rw [(F.basis k).repr_apply_apply, map_zero]
  exact hall a

/-- Complex Fourier components are separated by the same real frame,
by applying the real result to their real and imaginary parts. -/
theorem frame_complex_zero_of_components (F : PhysicalPolarization.Frame)
    (k : Position) (z : Fin 3 → ℂ) (hk : k ≠ 0)
    (htrans : ∀ l : Fin 2, (∑ μ : Fin 3, (F.epsilon k l μ : ℂ) * z μ) = 0)
    (hlong : (∑ μ : Fin 3, (k μ : ℂ) * z μ) = 0) :
    ∀ μ, z μ = 0 := by
  let vr : Position := WithLp.toLp 2 (fun μ => (z μ).re)
  let vi : Position := WithLp.toLp 2 (fun μ => (z μ).im)
  have hvr : vr = 0 := by
    apply frame_zero_of_components F k vr hk
    · intro l
      simpa [vr, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
        congrArg Complex.re (htrans l)
    · simpa [vr, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
        congrArg Complex.re hlong
  have hvi : vi = 0 := by
    apply frame_zero_of_components F k vi hk
    · intro l
      simpa [vi, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
        congrArg Complex.im (htrans l)
    · simpa [vi, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
        congrArg Complex.im hlong
  intro μ
  apply Complex.ext
  · exact congrArg (fun v : Position => v μ) hvr
  · exact congrArg (fun v : Position => v μ) hvi

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

/-- The Fourier transform of `ρ (A₁ - A₂)` has no longitudinal component. -/
theorem vectorDifference_fourier_transverse
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (k : Position) :
    (∑ μ : Fin 3, (k μ : ℂ) * fourierCoeff
      (fun x => vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x μ) k) = 0 :=
  fourier_transverse_of_gauge_tests (vectorDifference_integrable a₁ a₂ _)
    (vectorDifference_divergence i F χ C B S e h₁ h₂ hd) k

end PfHk
