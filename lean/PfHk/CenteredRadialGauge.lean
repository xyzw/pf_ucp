import PfHk.RadialGaugeContinuity
import PfHk.RadialGaugeAngularSlope

/-!
The physical radial gauge about an arbitrary electronic configuration.
The coefficients are the actual translated kernels `g_j(X₀+X)`. No photon
translation symmetry is used. All moment bounds are inherited at the
translated evaluation point and hence have no dependence on the center.
-/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

def couplingKernel (j : Fin N × Fin 3) (X : Configuration N) : WeightedPhotonKernel :=
  RadialGauge.couplingKernel F χ e j (O + X)

def couplingDerivative (j : Fin N × Fin 3) (v X : Configuration N) : WeightedPhotonKernel :=
  RadialGauge.couplingDerivative F χ hUV e j v (O + X)

def curvature (X v w : Configuration N) : WeightedPhotonKernel :=
  RadialGauge.curvature F χ hUV e (O + X) v w

attribute [local irreducible] couplingKernel couplingDerivative curvature
  RadialGauge.couplingKernel RadialGauge.couplingDerivative RadialGauge.curvature

theorem couplingKernel_continuous (j : Fin N × Fin 3) :
    Continuous (couplingKernel F χ e O j) := by
  unfold couplingKernel
  exact (RadialGauge.couplingKernel_continuous F χ e j).comp (continuous_const.add continuous_id)

theorem couplingDerivative_continuous (j : Fin N × Fin 3) (v : Configuration N) :
    Continuous (couplingDerivative F χ hUV e O j v) := by
  unfold couplingDerivative
  exact (RadialGauge.couplingDerivative_continuous F χ hUV e j v).comp
    (continuous_const.add continuous_id)

theorem couplingCurve_hasDerivAt (j : Fin N × Fin 3) (X v : Configuration N) (t : ℝ) :
    HasDerivAt (fun s => couplingKernel F χ e O j (X + s • v))
      (couplingDerivative F χ hUV e O j v (X + t • v)) t := by
  convert! RadialGauge.couplingCurve_hasDerivAt F χ hUV e j (O + X) v t using 1 <;>
    simp only [couplingKernel, couplingDerivative, add_assoc]

theorem couplingDerivative_real_smul (j : Fin N × Fin 3) (X v : Configuration N) (c : ℝ) :
    couplingDerivative F χ hUV e O j (c • v) X = c • couplingDerivative F χ hUV e O j v X := by
  unfold couplingDerivative
  exact RadialGauge.couplingDerivative_real_smul F χ hUV e j v (O + X) c

theorem couplingKernel_fixed (j : Fin N × Fin 3) (X : Configuration N) :
    F.conjugation (couplingKernel F χ e O j X).val.1 = (couplingKernel F χ e O j X).val.1 := by
  unfold couplingKernel
  exact RadialGauge.couplingKernel_fixed F χ e j (O + X)

theorem couplingDerivative_fixed (j : Fin N × Fin 3) (v X : Configuration N) :
    F.conjugation (couplingDerivative F χ hUV e O j v X).val.1 =
      (couplingDerivative F χ hUV e O j v X).val.1 := by
  unfold couplingDerivative
  exact RadialGauge.couplingDerivative_fixed F χ hUV e j v (O + X)

theorem curvature_eq (X v w : Configuration N) :
    curvature F χ hUV e O X v w =
      (∑ j : Fin N × Fin 3, w j • couplingDerivative F χ hUV e O j v X) -
        ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e O j w X := by
  unfold curvature RadialGauge.curvature couplingDerivative
  rfl

@[simp] theorem curvature_self (X v : Configuration N) : curvature F χ hUV e O X v v = 0 := by
  unfold curvature
  exact RadialGauge.curvature_self F χ hUV e (O + X) v

theorem curvature_continuous (v w : Configuration N) :
    Continuous (fun X => curvature F χ hUV e O X v w) := by
  unfold curvature
  exact (RadialGauge.curvature_continuous F χ hUV e v w).comp (continuous_const.add continuous_id)

theorem curvature_joint_continuous :
    Continuous (fun p : Configuration N × Configuration N × Configuration N =>
      curvature F χ hUV e O p.1 p.2.1 p.2.2) := by
  have harg : Continuous (fun p : Configuration N × Configuration N × Configuration N =>
      (O + p.1, p.2.1, p.2.2)) :=
    (continuous_const.add continuous_fst).prodMk continuous_snd
  unfold curvature
  exact (RadialGauge.curvature_joint_continuous F χ hUV e).comp harg

theorem curvature_fixed (X v w : Configuration N) :
    F.conjugation (curvature F χ hUV e O X v w).val.1 =
      (curvature F χ hUV e O X v w).val.1 := by
  unfold curvature
  exact RadialGauge.curvature_fixed F χ hUV e (O + X) v w

theorem curvature_real_smul_left (X v w : Configuration N) (c : ℝ) :
    curvature F χ hUV e O X (c • v) w = c • curvature F χ hUV e O X v w := by
  unfold curvature
  exact RadialGauge.curvature_real_smul_left F χ hUV e (O + X) v w c

theorem curvature_real_smul_right (X v w : Configuration N) (c : ℝ) :
    curvature F χ hUV e O X v (c • w) = c • curvature F χ hUV e O X v w := by
  unfold curvature
  exact RadialGauge.curvature_real_smul_right F χ hUV e (O + X) v w c

theorem curvature_add_right (X v w z : Configuration N) :
    curvature F χ hUV e O X v (w + z) =
      curvature F χ hUV e O X v w + curvature F χ hUV e O X v z := by
  unfold curvature
  exact RadialGauge.curvature_add_right F χ hUV e (O + X) v w z

/-- The same constant works at every center. -/
theorem curvature_norm_le (X v w : Configuration N) :
    ‖curvature F χ hUV e O X v w‖ ≤
      RadialGauge.curvatureConstant (N := N) F χ hUV e * ‖v‖ * ‖w‖ := by
  unfold curvature RadialGauge.curvatureConstant
  exact RadialGauge.curvature_norm_le F χ hUV e (O + X) v w

def rayIntegrand (θ : Configuration N) (r : ℝ) : WeightedPhotonKernel :=
  ∑ j : Fin N × Fin 3, θ j • couplingKernel F χ e O j (r • θ)

def label (X : Configuration N) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..1, rayIntegrand F χ e O X s

def unitary (W : ConcreteWeylLaw photonMeasure) (X : Configuration N) : PhotonFock ≃ₗᵢ[ℂ] PhotonFock :=
  W.weyl (Complex.I • (label F χ e O X).val.1)

theorem rayIntegrand_continuous (θ : Configuration N) : Continuous (rayIntegrand F χ e O θ) := by
  unfold rayIntegrand
  exact continuous_finsetSum _ (fun j _ =>
    (continuous_const : Continuous (fun _ : ℝ => θ j)).smul
      ((couplingKernel_continuous F χ e O j).comp (continuous_id.smul continuous_const)))

theorem rayIntegrand_fixed (θ : Configuration N) (r : ℝ) :
    F.conjugation (rayIntegrand F χ e O θ r).val.1 = (rayIntegrand F χ e O θ r).val.1 :=
  RadialGauge.sum_fixed F _ (fun j => real_smul_fixed F _ _ (couplingKernel_fixed F χ e O j _))

theorem label_fixed (X : Configuration N) :
    F.conjugation (label F χ e O X).val.1 = (label F χ e O X).val.1 :=
  integral_fixed F _ ((rayIntegrand_continuous F χ e O X).intervalIntegrable 0 1)
    (rayIntegrand_fixed F χ e O X)

theorem rayIntegrand_smul (θ : Configuration N) (r s : ℝ) :
    rayIntegrand F χ e O (r • θ) s = r • rayIntegrand F χ e O θ (s * r) := by
  simp only [rayIntegrand, PiLp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, mul_assoc]

theorem label_smul (θ : Configuration N) (r : ℝ) :
    label F χ e O (r • θ) = ∫ s in (0 : ℝ)..r, rayIntegrand F χ e O θ s := by
  unfold label
  simp_rw [rayIntegrand_smul]
  rw [intervalIntegral.integral_smul]
  simp

theorem label_radial_hasDerivAt (θ : Configuration N) (r : ℝ) :
    HasDerivAt (fun s : ℝ => label F χ e O (s • θ)) (rayIntegrand F χ e O θ r) r := by
  simp_rw [label_smul]
  exact intervalIntegral.integral_hasDerivAt_right
    ((rayIntegrand_continuous F χ e O θ).intervalIntegrable 0 r)
    (rayIntegrand_continuous F χ e O θ).stronglyMeasurable.stronglyMeasurableAtFilter
    (rayIntegrand_continuous F χ e O θ).continuousAt

def angularLabel (θ ζ : Configuration N) (r : ℝ) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..r, s • curvature F χ hUV e O (s • θ) θ ζ

theorem angularIntegrand_continuous (θ ζ : Configuration N) :
    Continuous (fun s : ℝ => s • curvature F χ hUV e O (s • θ) θ ζ) :=
  continuous_id.smul ((curvature_continuous F χ hUV e O θ ζ).comp
    (continuous_id.smul continuous_const))

theorem angularLabel_radial_hasDerivAt (θ ζ : Configuration N) (r : ℝ) :
    HasDerivAt (angularLabel F χ hUV e O θ ζ)
      (r • curvature F χ hUV e O (r • θ) θ ζ) r :=
  intervalIntegral.integral_hasDerivAt_right
    ((angularIntegrand_continuous F χ hUV e O θ ζ).intervalIntegrable 0 r)
    (angularIntegrand_continuous F χ hUV e O θ ζ).stronglyMeasurable.stronglyMeasurableAtFilter
    (angularIntegrand_continuous F χ hUV e O θ ζ).continuousAt

theorem angularLabel_logarithmic_hasDerivAt (θ ζ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => angularLabel F χ hUV e O θ ζ (Real.exp (-s)))
      ((-(Real.exp (-t) ^ 2)) • curvature F χ hUV e O (Real.exp (-t) • θ) θ ζ) t := by
  have ht : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  convert! (angularLabel_radial_hasDerivAt F χ hUV e O θ ζ (Real.exp (-t))).scomp t ht using 1
  simp only [smul_smul, neg_mul, pow_two]

theorem angularLabel_fixed (θ ζ : Configuration N) (r : ℝ) :
    F.conjugation (angularLabel F χ hUV e O θ ζ r).val.1 =
      (angularLabel F χ hUV e O θ ζ r).val.1 :=
  integral_fixed F _ ((angularIntegrand_continuous F χ hUV e O θ ζ).intervalIntegrable 0 r)
    (fun s => real_smul_fixed F _ _ (curvature_fixed F χ hUV e O (s • θ) θ ζ))

theorem angularLabel_norm_le (θ ζ : Configuration N)
    (hθ : ‖θ‖ ≤ 1) (hζ : ‖ζ‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖angularLabel F χ hUV e O θ ζ r‖ ≤ r ^ 2 * RadialGauge.curvatureConstant (N := N) F χ hUV e := by
  have hC := RadialGauge.curvatureConstant_nonneg (N := N) F χ hUV e
  have hdir : ‖θ‖ * ‖ζ‖ ≤ 1 :=
    (mul_le_mul hθ hζ (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := r) (C := r * RadialGauge.curvatureConstant (N := N) F χ hUV e)
    (f := fun s => s • curvature F χ hUV e O (s • θ) θ ζ) (by
      intro s hs
      rw [Set.uIoc_of_le hr] at hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      have hb := curvature_norm_le F χ hUV e O (s • θ) θ ζ
      have h₁ := mul_le_mul_of_nonneg_left hdir hC
      have h₂ : ‖curvature F χ hUV e O (s • θ) θ ζ‖ ≤
          RadialGauge.curvatureConstant (N := N) F χ hUV e := by nlinarith only [hb, h₁]
      exact (mul_le_mul_of_nonneg_left h₂ hs.1.le).trans
        (mul_le_mul_of_nonneg_right hs.2 hC))
  simpa only [angularLabel, sub_zero, abs_of_nonneg hr, pow_two, mul_assoc, mul_comm, mul_left_comm] using h

/-- The origin construction is the zero-center special case. -/
theorem label_zero_center (X : Configuration N) :
    label F χ e 0 X = RadialGauge.label F χ e X := by
  simp only [label, rayIntegrand, couplingKernel, zero_add, RadialGauge.label, RadialGauge.rayIntegrand]

attribute [local irreducible] rayIntegrand label angularLabel unitary

theorem rayIntegrand_joint_continuous :
    Continuous (fun p : Configuration N × ℝ => rayIntegrand F χ e O p.1 p.2) := by
  have hθ : Continuous (fun p : Configuration N × ℝ => p.1) := continuous_fst
  have hr : Continuous (fun p : Configuration N × ℝ => p.2) := continuous_snd
  have hX : Continuous (fun p : Configuration N × ℝ => p.2 • p.1) := hr.smul hθ
  have hg (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ =>
      couplingKernel F χ e O j (p.2 • p.1)) :=
    (couplingKernel_continuous F χ e O j).comp hX
  have hc (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ => p.1 j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp hθ
  unfold rayIntegrand
  exact continuous_finsetSum _ (fun j _ => (hc j).smul (hg j))

theorem label_continuous : Continuous (label F χ e O) := by
  unfold label
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (rayIntegrand_joint_continuous F χ e O) 0 1

theorem angularLabel_joint_continuous :
    Continuous (fun p : Configuration N × Configuration N × ℝ =>
      angularLabel F χ hUV e O p.1 p.2.1 p.2.2) := by
  let T := Configuration N × Configuration N × ℝ
  have hθ : Continuous (fun p : T × ℝ => p.1.1) := continuous_fst.comp continuous_fst
  have hζ : Continuous (fun p : T × ℝ => p.1.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : T × ℝ => p.2) := continuous_snd
  have harg : Continuous (fun p : T × ℝ => (p.2 • p.1.1, p.1.1, p.1.2.1)) :=
    (hs.smul hθ).prodMk (hθ.prodMk hζ)
  have hc : Continuous (fun p : T × ℝ => curvature F χ hUV e O (p.2 • p.1.1) p.1.1 p.1.2.1) :=
    (curvature_joint_continuous F χ hUV e O).comp harg
  unfold angularLabel
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hs.smul hc)
    (continuous_snd.comp continuous_snd)

theorem angularLabel_continuous_theta (ζ : Configuration N) (r : ℝ) :
    Continuous (fun θ : Configuration N => angularLabel F χ hUV e O θ ζ r) := by
  have harg : Continuous (fun θ : Configuration N => (θ, ζ, r)) :=
    continuous_id.prodMk (continuous_const.prodMk continuous_const)
  exact (angularLabel_joint_continuous F χ hUV e O).comp harg

theorem angularDerivative_continuous_theta (ζ : Configuration N) (t : ℝ) :
    Continuous (fun θ : Configuration N => (-(Real.exp (-t) ^ 2)) •
      curvature F χ hUV e O (Real.exp (-t) • θ) θ ζ) := by
  have harg : Continuous (fun θ : Configuration N => (Real.exp (-t) • θ, θ, ζ)) :=
    ((continuous_const : Continuous (fun _ : Configuration N => Real.exp (-t))).smul
      continuous_id).prodMk (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun θ : Configuration N => curvature F χ hUV e O (Real.exp (-t) • θ) θ ζ) :=
    (curvature_joint_continuous F χ hUV e O).comp harg
  exact (continuous_const : Continuous (fun _ : Configuration N => (-(Real.exp (-t) ^ 2) : ℝ))).smul hc

theorem angular_derivative_norm_le (θ ζ : Configuration N) (s : ℝ) :
    ‖(-(Real.exp (-s) ^ 2)) • curvature F χ hUV e O (Real.exp (-s) • θ) θ ζ‖ ≤
      Real.exp (-2 * s) * RadialGauge.curvatureConstant (N := N) F χ hUV e * ‖θ‖ * ‖ζ‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_left
    (curvature_norm_le F χ hUV e O (Real.exp (-s) • θ) θ ζ) (sq_nonneg (Real.exp (-s)))
  have heq : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  rw [heq]
  nlinarith only [h]

theorem angularLabel_logarithmic_slope_bound (θ ζ : Configuration N)
    (hθ : ‖θ‖ ≤ 1) (hζ : ‖ζ‖ ≤ 1) (t h : ℝ) (hh : |h| ≤ 1) :
    ‖h⁻¹ • (angularLabel F χ hUV e O θ ζ (Real.exp (-(t + h))) -
      angularLabel F χ hUV e O θ ζ (Real.exp (-t)))‖ ≤
      Real.exp (2 - 2 * t) * RadialGauge.curvatureConstant (N := N) F χ hUV e := by
  have hC := RadialGauge.curvatureConstant_nonneg (N := N) F χ hUV e
  apply L2ParameterDerivative.local_slope_norm_le (mul_nonneg (Real.exp_pos _).le hC)
    (fun s _ => angularLabel_logarithmic_hasDerivAt F χ hUV e O θ ζ s) _ hh
  intro s hs
  have hexp : Real.exp (-2 * s) ≤ Real.exp (2 - 2 * t) :=
    Real.exp_le_exp.mpr (by linarith [hs.1])
  have hnorm : ‖θ‖ * ‖ζ‖ ≤ 1 := by
    nlinarith [mul_le_mul hθ hζ (norm_nonneg ζ) (by norm_num : (0 : ℝ) ≤ 1)]
  have hcoef : 0 ≤ Real.exp (-2 * s) * RadialGauge.curvatureConstant (N := N) F χ hUV e := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hnorm hcoef
  have h₂ := mul_le_mul_of_nonneg_right hexp hC
  have h₃ := angular_derivative_norm_le F χ hUV e O θ ζ s
  nlinarith

end PfHk.CenteredRadialGauge
