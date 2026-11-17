import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
The actual L2 Fourier transform commutes with bounded maps on the Hilbert
fiber and with orthogonal changes of Euclidean coordinates. Both facts
are first proved on Schwartz representatives, then extended by density.
-/

noncomputable section

namespace GptLean.PhysicalL2FourierTransport

open MeasureTheory FourierTransform SchwartzMap
open scoped ENNReal RealInnerProductSpace

variable {X Y H K : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem schwartz_fourier_postcomp (B : H →L[ℂ] K) (f : 𝓢(X, H)) :
    𝓕 (SchwartzMap.postcompCLM B f) = SchwartzMap.postcompCLM B (𝓕 f) := by
  ext ξ
  change 𝓕 (fun x => B (f x)) ξ = B (𝓕 (fun x => f x) ξ)
  rw [Real.fourier_eq, Real.fourier_eq, ← B.integral_comp_comm]
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by simp only [Circle.smul_def, map_smul]
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr f.integrable

omit [CompleteSpace H] [CompleteSpace K] in
private theorem toLp_postcomp (B : H →L[ℂ] K) (f : 𝓢(X, H)) :
    (SchwartzMap.postcompCLM B f).toLp 2 = B.compLpL 2 volume (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM B f).coeFn_toLp 2,
    B.coeFn_compLpL (f.toLp 2), f.coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz]
  rfl

/-- Fourier transport preserves every bounded fiber observable. -/
theorem fourier_compLpL (B : H →L[ℂ] K) (u : Lp H 2 (volume : Measure X)) :
    Lp.fourierTransformₗᵢ X K (B.compLpL 2 volume u) =
      B.compLpL 2 volume (Lp.fourierTransformₗᵢ X H u) := by
  apply DenseRange.induction_on (p := fun u : Lp H 2 (volume : Measure X) =>
    Lp.fourierTransformₗᵢ X K (B.compLpL 2 volume u) =
      B.compLpL 2 volume (Lp.fourierTransformₗᵢ X H u))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) u
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ X K).continuous.comp (B.compLpL 2 volume).continuous)
      ((B.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ X H).continuous)
  intro f
  change 𝓕 (B.compLpL 2 volume (f.toLp 2)) = B.compLpL 2 volume (𝓕 (f.toLp 2))
  rw [← toLp_postcomp, SchwartzMap.toLp_fourier_eq, schwartz_fourier_postcomp,
    toLp_postcomp, SchwartzMap.toLp_fourier_eq]

/-- The inverse Fourier transform has the same fiber compatibility. -/
theorem fourierInv_compLpL (B : H →L[ℂ] K) (u : Lp H 2 (volume : Measure X)) :
    (Lp.fourierTransformₗᵢ X K).symm (B.compLpL 2 volume u) =
      B.compLpL 2 volume ((Lp.fourierTransformₗᵢ X H).symm u) := by
  apply (Lp.fourierTransformₗᵢ X K).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourier_compLpL,
    LinearIsometryEquiv.apply_symm_apply]

omit [CompleteSpace H] in
private theorem toLp_pull (A : Y ≃ₗᵢ[ℝ] X) (f : 𝓢(X, H)) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f).toLp 2 =
      Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    A.toContinuousLinearEquiv f).coeFn_toLp 2,
    Lp.coeFn_compMeasurePreserving (f.toLp 2) A.measurePreserving,
    A.measurePreserving.quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)] with x hx hy hz
  change _ = (Lp.compMeasurePreserving A A.measurePreserving (f.toLp 2)) x
  exact hx.trans (hz.symm.trans hy.symm)

/-- Orthogonal regrouping of coordinates commutes with the actual L2 Fourier map. -/
theorem fourier_pull (A : Y ≃ₗᵢ[ℝ] X) (u : Lp H 2 (volume : Measure X)) :
    Lp.fourierTransformₗᵢ Y H (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving u) =
      Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving (Lp.fourierTransformₗᵢ X H u) := by
  apply DenseRange.induction_on (p := fun u : Lp H 2 (volume : Measure X) =>
    Lp.fourierTransformₗᵢ Y H (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving u) =
      Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving (Lp.fourierTransformₗᵢ X H u))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) u
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ Y H).continuous.comp
        (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving).continuous)
      ((Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving).continuous.comp
        (Lp.fourierTransformₗᵢ X H).continuous)
  intro f
  change 𝓕 (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving (f.toLp 2)) =
    Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving (𝓕 (f.toLp 2))
  rw [← toLp_pull, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, ← toLp_pull]
  congr 1
  ext ξ
  exact Real.fourier_comp_linearIsometry A f ξ

/-- The inverse transform respects the same orthogonal coordinate transport. -/
theorem fourierInv_pull (A : Y ≃ₗᵢ[ℝ] X) (u : Lp H 2 (volume : Measure X)) :
    (Lp.fourierTransformₗᵢ Y H).symm
        (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving u) =
      Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving
        ((Lp.fourierTransformₗᵢ X H).symm u) := by
  apply (Lp.fourierTransformₗᵢ Y H).injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourier_pull,
    LinearIsometryEquiv.apply_symm_apply]

end GptLean.PhysicalL2FourierTransport
