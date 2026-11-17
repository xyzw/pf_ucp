import PfHk.CenteredSphereAngularEnergy
import PfHk.StrongOperatorDerivative
import PfHk.SpatialFieldOperatorBound

/-! The moving-argument product rule for the actual angular sphere form.
The strong field derivative and a local uniform operator bound justify
differentiating a curve in the radiation graph L2 space. -/

noncomputable section
namespace PfHk.CenteredSphereAngularField

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open PfHk.RadialGauge (curvatureConstant curvatureConstant_nonneg)
open scoped ENNReal Topology InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000
local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] field fieldDerivative angularVector energy formDerivative

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)

theorem field_opNorm_le (j : Fin N × Fin 3) (t : ℝ) :
    ‖field F χ hUV e O C j t‖ ≤ 3 * coefficientBound (N := N) F χ hUV e t := by
  unfold field
  exact SpatialFieldParameterDerivative.spatialField_opNorm_le _ C _ _ _
    (mul_nonneg (sq_nonneg _) (curvatureConstant_nonneg F χ hUV e)) _

theorem field_local_opNorm_le (j : Fin N × Fin 3) (t : ℝ) :
    ∀ᶠ s in 𝓝 t, ‖field F χ hUV e O C j s‖ ≤
      3 * localDerivativeBound (N := N) F χ hUV e t := by
  filter_upwards [Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1)] with s hs
  apply (field_opNorm_le F χ hUV e O C j s).trans
  have heq : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hs.1] : -2 * s ≤ 2 - 2 * t))
      (curvatureConstant_nonneg (N := N) F χ hUV e)) (by norm_num : (0 : ℝ) ≤ 3)
  unfold coefficientBound localDerivativeBound
  rw [heq]
  exact hm

theorem field_moving_hasDerivAt (j : Fin N × Fin 3) {q : ℝ → SphereRadiation N}
    {dq : SphereRadiation N} {t : ℝ}
    (hq : L2OperatorDerivative.HasL2DerivAt q dq t) :
    L2OperatorDerivative.HasL2DerivAt
      (fun s => field F χ hUV e O C j s (q s))
      (field F χ hUV e O C j t dq + fieldDerivative F χ hUV e O C j t (q t)) t := by
  let A : ℝ → SphereRadiation N →L[ℝ] SpherePhoton N :=
    fun s => (field F χ hUV e O C j s).restrictScalars ℝ
  have ha (u : SphereRadiation N) : HasDerivAt (fun s => A s u)
      (fieldDerivative F χ hUV e O C j t u) t := by
    convert! field_hasDerivAt F χ hUV e O C j t u using 1
  have hb : ∀ᶠ s in 𝓝 t, ‖A s‖ ≤ 3 * localDerivativeBound (N := N) F χ hUV e t := by
    simpa only [A, ContinuousLinearMap.norm_restrictScalars] using
      field_local_opNorm_le F χ hUV e O C j t
  convert! StrongOperatorDerivative.hasDerivAt_apply ha hb hq using 1

theorem energy_moving_hasDerivAt {q : ℝ → SphereRadiation N}
    {p : ℝ → (Fin N × Fin 3) → SpherePhoton N} {dq : SphereRadiation N}
    {dp : (Fin N × Fin 3) → SpherePhoton N} {t : ℝ}
    (hq : L2OperatorDerivative.HasL2DerivAt q dq t)
    (hp : ∀ j, L2OperatorDerivative.HasL2DerivAt (fun s => p s j) (dp j) t) :
    HasDerivAt (fun s => energy F χ hUV e O C (p s) (q s) s)
      (2 * (∑ j, inner ℝ (angularVector F χ hUV e O C (p t) (q t) j t)
        (angularVector F χ hUV e O C dp dq j t)) + formDerivative F χ hUV e O C (p t) (q t) t) t := by
  have hd (j : Fin N × Fin 3) :=
    ((hp j).add ((field_moving_hasDerivAt F χ hUV e O C j hq).const_smul Complex.I)).norm_sq
  have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert! hs using 1 <;> first
    | rfl
    | (funext s; simp only [energy, angularVector, Finset.sum_apply, Pi.add_apply, Pi.smul_apply])
    | (simp only [formDerivative, angularVector, Pi.add_apply, Pi.smul_apply,
        smul_add, inner_add_right, mul_add,
        Finset.sum_add_distrib, ← Finset.mul_sum]; ring)

end PfHk.CenteredSphereAngularField
