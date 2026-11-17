import PfHk.CenteredRadialGaugeC1
import PfHk.CenteredRadialGaugePolar
import PfHk.WeylGraphC1Calculus
import PfHk.CompactL2Parameter
import PfHk.LogPolarCalculus
import PfHk.PhysicalSphereSpace

/-! Physical specialization of the universal Weyl smooth-vector calculus.
All displacement labels and their derivatives are the constructed actual
centered PF labels. Only first radial derivatives of their radiation
weight are used, so no additional ultraviolet moment enters. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open PfHk.RadialGauge (energyComponent)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 350000
attribute [local irreducible] label sqrtLabel rayIntegrand energyRay unitary graphLift
  radiationGraphInclusion fullRadiationInclusion fullRootProjection

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)

include hUV in
theorem gauged_core_contDiff (B : StandardWeylGraphC1 W) {s : Set (Configuration N)}
    (a : SmoothCore s) : ContDiff ℝ (1 : ℕ∞) (gaugedValue F χ e O W a.rootWave) := by
  have hf : ContDiff ℝ (1 : ℕ∞) (fun X => Complex.I • (label F χ e O X).val.1) :=
    (((component false).contDiff).comp (label_contDiff F χ hUV e O)).const_smul Complex.I
  have hu : ContDiff ℝ (1 : ℕ∞) (fun X => fullRadiationInclusion (a.representative X)) :=
    ((fullRadiationInclusion.restrictScalars ℝ).contDiff.comp a.smooth).of_le (by simp)
  have h := B.ambient_c1 (Configuration N) _ _ a.photonCutoff hf hu a.photonFinite
  convert! h using 1
  funext X
  unfold gaugedValue unitary coreValue SmoothCore.rootWave fullRadiationInclusion
  rfl

def logarithmicPoint (p : ℝ × Sphere N) : Configuration N := Real.exp (-p.1) • p.2.val

theorem logarithmicPoint_continuous : Continuous (logarithmicPoint (N := N)) :=
  (Real.continuous_exp.comp continuous_fst.neg).smul
    (continuous_subtype_val.comp continuous_snd)

def sphereGraphWave {s : Set (Configuration N)} (a : SmoothCore s) (p : ℝ × Sphere N) :
    RadiationGraphSpace :=
  graphLift F χ hUV e O W (logarithmicPoint p) (a.rootWave (logarithmicPoint p))

/-- Joint graph regularity on the actual sphere. The derivative is obtained
from universal Weyl graph calculus after proving every physical label
and original-core premise. -/
theorem exists_joint_graph_derivative (B : StandardWeylGraphC1 W)
    {s : Set (Configuration N)} (a : SmoothCore s) :
    Continuous (sphereGraphWave F χ hUV e O W a) ∧
      ∃ d : ℝ × Sphere N → RadiationGraphSpace, Continuous d ∧
        ∀ θ t, HasDerivAt (fun v => sphereGraphWave F χ hUV e O W a (v, θ)) (d (t, θ)) t := by
  let x : ℝ × Sphere N → Configuration N := logarithmicPoint
  let r : ℝ × Sphere N → ℝ := fun p => Real.exp (-p.1)
  let f : ℝ × Sphere N → Lp ℂ 2 photonMeasure := fun p => Complex.I • (label F χ e O (x p)).val.1
  let df : ℝ × Sphere N → Lp ℂ 2 photonMeasure := fun p =>
    Complex.I • ((-r p) • component false (rayIntegrand F χ e O p.2.val (r p)))
  let y : ℝ × Sphere N → Lp ℂ 2 photonMeasure := fun p => Complex.I • sqrtLabel F χ hUV e O (x p)
  let dy : ℝ × Sphere N → Lp ℂ 2 photonMeasure := fun p =>
    Complex.I • ((-r p) • energyComponent true (energyRay F χ hUV e O p.2.val (r p)))
  let u : ℝ × Sphere N → FullRadiationGraph := fun p => a.representative (x p)
  let du : ℝ × Sphere N → FullRadiationGraph := fun p =>
    fderiv ℝ a.representative (x p) ((-r p) • p.2.val)
  have hx : Continuous x := logarithmicPoint_continuous
  have hr : Continuous r := Real.continuous_exp.comp continuous_fst.neg
  have hθ : Continuous (fun p : ℝ × Sphere N => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hf : Continuous f := by
    have hfc := ((component false).continuous.comp
      ((label_continuous F χ e O).comp hx)).const_smul Complex.I
    convert! hfc using 1
  have hdf : Continuous df := by
    convert! (hr.neg.smul ((component false).continuous.comp
      ((rayIntegrand_joint_continuous F χ e O).comp (hθ.prodMk hr)))).const_smul Complex.I using 1
  have hyc : Continuous y := by
    convert! ((sqrtLabel_continuous F χ hUV e O).comp hx).const_smul Complex.I using 1
  have hdy : Continuous dy := by
    convert! (hr.neg.smul ((energyComponent true).continuous.comp
      ((energyRay_joint_continuous F χ hUV e O).comp (hθ.prodMk hr)))).const_smul Complex.I using 1
  have hu : Continuous u := a.smooth.continuous.comp hx
  have hdu : Continuous du :=
    ((a.smooth.continuous_fderiv (by simp)).comp hx).clm_apply (hr.neg.smul hθ)
  have hy (p : ℝ × Sphere N) :
      ∀ᵐ k ∂photonMeasure, y p k = (Real.sqrt ‖k.1‖ : ℂ) * f p k :=
    imaginary_label_relation F χ hUV e O (x p)
  have hfd (θ : Sphere N) (t : ℝ) :
      L2OperatorDerivative.HasL2DerivAt (fun v => f (v, θ)) (df (t, θ)) t := by
    have hh := (label_radial_hasDerivAt F χ e O θ.val (Real.exp (-t))).scomp t
      (PolarCalculus.radius_hasDerivAt t)
    have hc := ((component false).hasFDerivAt.comp_hasDerivAt t hh).const_smul Complex.I
    convert! hc using 1 <;> simp only [f, df, x, r, logarithmicPoint, Function.comp_def, map_smul]
  have hyd (θ : Sphere N) (t : ℝ) :
      L2OperatorDerivative.HasL2DerivAt (fun v => y (v, θ)) (dy (t, θ)) t := by
    convert! (sqrtLabel_logarithmic_hasDerivAt F χ hUV e O θ.val t).const_smul Complex.I using 1
  have hud (θ : Sphere N) (t : ℝ) : HasGraphDerivAt (fun v => u (v, θ)) (du (t, θ)) t := by
    have hxder := (PolarCalculus.radius_hasDerivAt t).smul_const θ.val
    convert! smooth_curve_hasDerivAt a.representative a.smooth hxder using 1
  have hout := B.parameter_graph_c1 (Sphere N) f df y dy hy u du a.photonCutoff
    hf hdf hyc hdy hu hdu hfd hyd hud (fun p => a.photonFinite (x p))
  have he : graphAction W f y hy u = sphereGraphWave F χ hUV e O W a := by
    funext p
    unfold graphAction sphereGraphWave graphLift
    rfl
  rw [he] at hout
  convert! hout using 1

end PfHk.CenteredRadialGauge
