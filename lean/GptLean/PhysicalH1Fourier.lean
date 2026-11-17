import GptLean.ElectronicH1Reindex
import GptLean.ElectronicH1Complex
import GptLean.PhysicalMultiplicationGraph
import Mathlib.Analysis.Fourier.LpSpace

/-!
The actual L2 Fourier transform of the weak electronic derivatives.
The Schwartz identity extends from the proved compact smooth core through
the closed maximal multiplication graph. The Mathlib Fourier convention
uses frequency 2πξ, which remains explicit in the symbol.
-/

noncomputable section

namespace GptLean.PhysicalH1Fourier

open MeasureTheory ElectronicH1Space FourierTransform SchwartzMap LineDeriv
open scoped ENNReal ContDiff Topology

set_option backward.isDefEq.respectTransparency.types false

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def frequencySymbol (i : I) (ξ : EuclideanSpace ℝ I) : ℂ :=
  (2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)

omit [DecidableEq I] in
def fourier : L2 H I ≃ₗᵢ[ℂ] L2 H I :=
  Lp.fourierTransformₗᵢ (EuclideanSpace ℝ I) H

omit [DecidableEq I] in
theorem fourier_schwartz (s : 𝓢(EuclideanSpace ℝ I, H)) :
    fourier (s.toLp 2) = (𝓕 s).toLp 2 := SchwartzMap.toLp_fourier_eq s

private theorem compact_derivative (f : EuclideanSpace ℝ I → H)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i : I) :
    (fourier (value (ofSmoothCompact f hf hs)),
      fourier (derivative i (ofSmoothCompact f hf hs))) ∈
        PhysicalMultiplicationGraph.graph volume (frequencySymbol i) := by
  let s : 𝓢(EuclideanSpace ℝ I, H) := hs.toSchwartzMap hf
  have hv : value (ofSmoothCompact f hf hs) = s.toLp 2 := rfl
  have hd : derivative i (ofSmoothCompact f hf hs) =
      (∂_{EuclideanSpace.single i (1 : ℝ)} s).toLp 2 := rfl
  rw [hv, hd, fourier_schwartz, fourier_schwartz]
  change ∀ᵐ ξ ∂volume, ((𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} s)).toLp 2) ξ =
    frequencySymbol i ξ • ((𝓕 s).toLp 2) ξ
  have hg : (fun ξ : EuclideanSpace ℝ I => inner ℝ ξ (EuclideanSpace.single i (1 : ℝ))).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single i (1 : ℝ))).hasTemperateGrowth
  filter_upwards [(𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} s)).coeFn_toLp 2 volume,
    (𝓕 s).coeFn_toLp 2 volume] with ξ hx hy
  rw [hx, hy, SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, frequencySymbol]
  rw [← Complex.coe_smul, smul_smul]

/-- Weak coordinate derivatives become the actual maximal frequency multipliers. -/
theorem derivative_graph (u : H1 H I) (i : I) :
    (fourier (value u), fourier (derivative i u)) ∈
      PhysicalMultiplicationGraph.graph volume (frequencySymbol i) := by
  refine (ElectronicH1Reindex.dense_genericSmoothCore (E := H) (I := I)).induction ?_ ?_ u
  · rintro _ ⟨f, hf, hs, rfl⟩
    exact compact_derivative f hf hs i
  · exact (PhysicalMultiplicationGraph.graph_closed volume (frequencySymbol i)).preimage
      ((fourier.continuous.comp value.continuous).prodMk
        (fourier.continuous.comp (derivative i).continuous))

theorem derivative_ae (u : H1 H I) (i : I) :
    fourier (derivative i u) =ᵐ[volume]
      fun ξ => frequencySymbol i ξ • fourier (value u) ξ := derivative_graph u i

/-- Plancherel gives the exact frequency integral for each coordinate energy. -/
theorem derivative_energy (u : H1 H I) (i : I) :
    ‖derivative i u‖ ^ 2 = ∫ ξ,
      ‖frequencySymbol i ξ‖ ^ 2 * ‖fourier (value u) ξ‖ ^ 2 := by
  have h := Repair.toL2_norm_sq (Lp.memLp (fourier (derivative i u)))
  simp only [Lp.toLp_coeFn, fourier.norm_map] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [derivative_ae u i] with ξ hx
  rw [hx, norm_smul, mul_pow]

/-- The same identity on the complex H1 graph used by the physical reference. -/
theorem complex_derivative_ae (u : ElectronicH1Complex.ComplexH1 H I) (i : I) :
    fourier (ElectronicH1Complex.derivative i u) =ᵐ[volume]
      fun ξ => frequencySymbol i ξ • fourier (ElectronicH1Complex.value u) ξ :=
  derivative_ae (ElectronicH1Complex.realEquiv u) i

theorem complex_derivative_energy (u : ElectronicH1Complex.ComplexH1 H I) (i : I) :
    ‖ElectronicH1Complex.derivative i u‖ ^ 2 = ∫ ξ,
      ‖frequencySymbol i ξ‖ ^ 2 * ‖fourier (ElectronicH1Complex.value u) ξ‖ ^ 2 :=
  derivative_energy (ElectronicH1Complex.realEquiv u) i

end GptLean.PhysicalH1Fourier
