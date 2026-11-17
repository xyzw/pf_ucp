import PfHk.RadialGaugeLinearity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Joint continuity and hence sphere measurability of the physical
angular coefficients and their logarithmic derivatives. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
attribute [local irreducible] directionKernel couplingDerivative curvature angularLabel

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

theorem directionKernel_expansion (i : Fin 3) (v x : FieldSpace) :
    directionKernel F χ hUV i v x =
      ∑ j : Fin 3, v j • directionKernel F χ hUV i (EuclideanSpace.single j 1) x := by
  let L : FieldSpace →ₗ[ℝ] WeightedPhotonKernel :=
    { toFun v := directionKernel F χ hUV i v x
      map_add' v w := directionKernel_add F χ hUV i v w x
      map_smul' c v := directionKernel_real_smul F χ hUV i v x c }
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have h := congrArg L hv
  simpa only [map_sum, map_smul, L, LinearMap.coe_mk, AddHom.coe_mk] using h.symm

theorem directionKernel_joint_continuous (i : Fin 3) :
    Continuous (fun p : FieldSpace × FieldSpace => directionKernel F χ hUV i p.1 p.2) := by
  have he : (fun p : FieldSpace × FieldSpace => directionKernel F χ hUV i p.1 p.2) =
      fun p => ∑ j : Fin 3, p.1 j • directionKernel F χ hUV i (EuclideanSpace.single j 1) p.2 :=
    funext (fun p => directionKernel_expansion F χ hUV i p.1 p.2)
  rw [he]
  apply continuous_finsetSum
  intro j _
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp continuous_fst).smul
    ((directionKernel_continuous F χ hUV i (EuclideanSpace.single j 1)).comp continuous_snd)

theorem couplingDerivative_joint_continuous (j : Fin N × Fin 3) :
    Continuous (fun p : Configuration N × Configuration N => couplingDerivative F χ hUV e j p.1 p.2) := by
  have hv : Continuous (fun p : Configuration N × Configuration N => particle p.1 j.1) :=
    (particleLinear j.1).continuous_of_finiteDimensional.comp continuous_fst
  have hx : Continuous (fun p : Configuration N × Configuration N => particle p.2 j.1) :=
    (particleLinear j.1).continuous_of_finiteDimensional.comp continuous_snd
  have hpair : Continuous (fun p : Configuration N × Configuration N =>
      (particle p.1 j.1, particle p.2 j.1)) := hv.prodMk hx
  have hd : Continuous (fun p : Configuration N × Configuration N =>
      directionKernel F χ hUV j.2 (particle p.1 j.1) (particle p.2 j.1)) :=
    (directionKernel_joint_continuous F χ hUV j.2).comp hpair
  unfold couplingDerivative
  exact (continuous_const : Continuous (fun _ : Configuration N × Configuration N => (-e : ℝ))).smul hd

theorem curvature_joint_continuous :
    Continuous (fun p : Configuration N × Configuration N × Configuration N =>
      curvature F χ hUV e p.1 p.2.1 p.2.2) := by
  let T := Configuration N × Configuration N × Configuration N
  have hX : Continuous (fun p : T => p.1) := continuous_fst
  have hv : Continuous (fun p : T => p.2.1) := continuous_fst.comp continuous_snd
  have hw : Continuous (fun p : T => p.2.2) := continuous_snd.comp continuous_snd
  have hc : ∀ j : Fin N × Fin 3, Continuous (fun p : T => p.2.1 j) := fun j =>
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp hv
  have hd : ∀ j : Fin N × Fin 3, Continuous (fun p : T => p.2.2 j) := fun j =>
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp hw
  have hvd : ∀ j : Fin N × Fin 3, Continuous (fun p : T => couplingDerivative F χ hUV e j p.2.1 p.1) :=
    fun j => (couplingDerivative_joint_continuous F χ hUV e j).comp (hv.prodMk hX)
  have hwd : ∀ j : Fin N × Fin 3, Continuous (fun p : T => couplingDerivative F χ hUV e j p.2.2 p.1) :=
    fun j => (couplingDerivative_joint_continuous F χ hUV e j).comp (hw.prodMk hX)
  unfold curvature
  exact (continuous_finsetSum _ (fun j _ => (hd j).smul (hvd j))).sub
    (continuous_finsetSum _ (fun j _ => (hc j).smul (hwd j)))

theorem angularLabel_joint_continuous :
    Continuous (fun p : Configuration N × Configuration N × ℝ =>
      angularLabel F χ hUV e p.1 p.2.1 p.2.2) := by
  let T := Configuration N × Configuration N × ℝ
  have hθ : Continuous (fun p : T × ℝ => p.1.1) := continuous_fst.comp continuous_fst
  have hζ : Continuous (fun p : T × ℝ => p.1.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : T × ℝ => p.2) := continuous_snd
  have harg : Continuous (fun p : T × ℝ => (p.2 • p.1.1, p.1.1, p.1.2.1)) :=
    (hs.smul hθ).prodMk (hθ.prodMk hζ)
  have hc : Continuous (fun p : T × ℝ => curvature F χ hUV e (p.2 • p.1.1) p.1.1 p.1.2.1) :=
    (curvature_joint_continuous F χ hUV e).comp harg
  unfold angularLabel
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hs.smul hc)
    (continuous_snd.comp continuous_snd)

/-- Spatial measurability needed to lift the angular label to sphere L². -/
theorem angularLabel_continuous_theta (ζ : Configuration N) (r : ℝ) :
    Continuous (fun θ : Configuration N => angularLabel F χ hUV e θ ζ r) := by
  have harg : Continuous (fun θ : Configuration N => (θ, ζ, r)) :=
    continuous_id.prodMk (continuous_const.prodMk continuous_const)
  exact (angularLabel_joint_continuous F χ hUV e).comp harg

/-- The physical logarithmic derivative coefficient is continuous in θ. -/
theorem angularDerivative_continuous_theta (ζ : Configuration N) (t : ℝ) :
    Continuous (fun θ : Configuration N => (-(Real.exp (-t) ^ 2)) •
      curvature F χ hUV e (Real.exp (-t) • θ) θ ζ) := by
  have harg : Continuous (fun θ : Configuration N => (Real.exp (-t) • θ, θ, ζ)) :=
    ((continuous_const : Continuous (fun _ : Configuration N => Real.exp (-t))).smul
      continuous_id).prodMk (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun θ : Configuration N => curvature F χ hUV e (Real.exp (-t) • θ) θ ζ) :=
    (curvature_joint_continuous F χ hUV e).comp harg
  exact (continuous_const : Continuous (fun _ : Configuration N => (-(Real.exp (-t) ^ 2) : ℝ))).smul hc

end PfHk.RadialGauge
