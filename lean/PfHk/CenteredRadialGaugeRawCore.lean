import PfHk.CenteredRadialGaugeRadialCore
import PfHk.SphereCoreConstruction
import PfHk.SphereRestrictionCalculus

/-! The actual unscaled logarithmic-polar curve of a smooth physical
operator-core vector. Every strong sphere derivative is constructed from
its original representative and the actual radial Weyl gauge. -/

noncomputable section
namespace PfHk.CenteredRadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 350000
local instance rawCorePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphInclusion fullRadiationInclusion
  graphLift gaugedValue gaugedRadialValue sphereGraphWave

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  {s : Set (Configuration N)} (a : SmoothCore s)

def rawGraphDerivative : ℝ × Sphere N → RadiationGraphSpace :=
  Classical.choose (exists_joint_graph_derivative F χ hUV e O W B a).2

theorem rawGraphDerivative_continuous : Continuous (rawGraphDerivative F χ hUV e O W B a) :=
  (Classical.choose_spec (exists_joint_graph_derivative F χ hUV e O W B a).2).1

theorem sphereGraphWave_hasDerivAt (θ : Sphere N) (t : ℝ) :
    HasDerivAt (fun v => sphereGraphWave F χ hUV e O W a (v, θ))
      (rawGraphDerivative F χ hUV e O W B a (t, θ)) t :=
  (Classical.choose_spec (exists_joint_graph_derivative F χ hUV e O W B a).2).2 θ t

def logarithmicFirstValue (X : Configuration N) : PhotonFock :=
  -gaugedRadialValue F χ e O C W a X

include hUV B in
theorem logarithmicFirstValue_contDiff : ContDiff ℝ (1 : ℕ∞)
    (logarithmicFirstValue F χ e O C W a) :=
  (gaugedRadialValue_contDiff F χ hUV e O C W B a (a.photonCutoff + 1)
    (radialGenerator_photonFinite F χ e O C a)).neg

theorem rawGraphDerivative_inclusion (p : ℝ × Sphere N) :
    radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a p) =
      logarithmicFirstValue F χ e O C W a (logarithmicPoint p) := by
  have he : (fun t => radiationGraphInclusion (sphereGraphWave F χ hUV e O W a (t, p.2))) =
      fun t => gaugedValue F χ e O W a.rootWave (Real.exp (-t) • p.2.val) :=
    funext fun t => sphereGraphWave_inclusion F χ hUV e O W a (t, p.2)
  convert! mapped_derivative_unique (radiationGraphInclusion.restrictScalars ℝ)
    (sphereGraphWave_hasDerivAt F χ hUV e O W B a p.2 p.1)
    (logarithmic_gauged_hasDerivAt F χ hUV e O C W B a p.2 p.1) he using 1

def logarithmicSecondValue (p : ℝ × Sphere N) : PhotonFock :=
  fderiv ℝ (logarithmicFirstValue F χ e O C W a) (logarithmicPoint p)
    ((-Real.exp (-p.1)) • p.2.val)

include hUV B in
theorem logarithmicSecondValue_continuous :
    Continuous (logarithmicSecondValue F χ e O C W a) := by
  have h := logarithmicFirstValue_contDiff F χ hUV e O C W B a
  exact ((h.continuous_fderiv (by simp)).comp logarithmicPoint_continuous).clm_apply
    ((Real.continuous_exp.comp continuous_fst.neg).neg.smul
      (continuous_subtype_val.comp continuous_snd))

theorem rawGraphDerivative_inclusion_hasDerivAt (θ : Sphere N) (t : ℝ) :
    HasDerivAt (fun v => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (v, θ)))
      (logarithmicSecondValue F χ e O C W a (t, θ)) t := by
  have he : (fun v => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (v, θ))) =
      fun v => logarithmicFirstValue F χ e O C W a (Real.exp (-v) • θ.val) :=
    funext fun v => rawGraphDerivative_inclusion F χ hUV e O C W B a (v, θ)
  rw [he]
  exact ((logarithmicFirstValue_contDiff F χ hUV e O C W B a).differentiable
    one_ne_zero _).hasFDerivAt.comp_hasDerivAt t ((radius_hasDerivAt t).smul_const θ.val)

include B in
theorem sphereGraphWave_sphereC1 (t : ℝ) :
    SphereC1 (fun θ => radiationGraphInclusion (sphereGraphWave F χ hUV e O W a (t, θ))) := by
  have he : (fun θ => radiationGraphInclusion (sphereGraphWave F χ hUV e O W a (t, θ))) =
      radialRestriction (gaugedValue F χ e O W a.rootWave) (Real.exp (-t)) :=
    funext fun θ => sphereGraphWave_inclusion F χ hUV e O W a (t, θ)
  rw [he]
  exact radialRestriction_sphereC1 _ (gauged_core_contDiff F χ hUV e O W B a) _

include C in
theorem rawGraphDerivative_sphereC1 (t : ℝ) :
    SphereC1 (fun θ => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (t, θ))) := by
  have he : (fun θ => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (t, θ))) =
      radialRestriction (logarithmicFirstValue F χ e O C W a) (Real.exp (-t)) :=
    funext fun θ => rawGraphDerivative_inclusion F χ hUV e O C W B a (t, θ)
  rw [he]
  exact radialRestriction_sphereC1 _ (logarithmicFirstValue_contDiff F χ hUV e O C W B a) _

include B in
theorem sphereGraphWave_gradient_continuous
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock) (j : Fin N × Fin 3) :
    Continuous (fun p : ℝ × Sphere N => sphereGradient
      (fun θ => radiationGraphInclusion (sphereGraphWave F χ hUV e O W a (p.1, θ))) j p.2) := by
  have he : (fun p : ℝ × Sphere N => sphereGradient
      (fun θ => radiationGraphInclusion (sphereGraphWave F χ hUV e O W a (p.1, θ))) j p.2) =
      fun p => sphereGradient (fun θ => (1 : ℝ) • gaugedValue F χ e O W a.rootWave
        (Real.exp (-p.1) • θ.val)) j p.2 := by
    funext p
    congr 1
    funext θ
    simpa only [one_smul, logarithmicPoint] using sphereGraphWave_inclusion F χ hUV e O W a (p.1, θ)
  rw [he]
  exact scaled_radial_gradient_continuous P _ (gauged_core_contDiff F χ hUV e O W B a)
    continuous_const (Real.continuous_exp.comp continuous_neg) (fun t => Real.exp_pos _) j

include C in
theorem rawGraphDerivative_gradient_continuous
    (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock) (j : Fin N × Fin 3) :
    Continuous (fun p : ℝ × Sphere N => sphereGradient
      (fun θ => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (p.1, θ))) j p.2) := by
  have he : (fun p : ℝ × Sphere N => sphereGradient
      (fun θ => radiationGraphInclusion (rawGraphDerivative F χ hUV e O W B a (p.1, θ))) j p.2) =
      fun p => sphereGradient (fun θ => (1 : ℝ) • logarithmicFirstValue F χ e O C W a
        (Real.exp (-p.1) • θ.val)) j p.2 := by
    funext p
    congr 1
    funext θ
    simpa only [one_smul, logarithmicPoint] using rawGraphDerivative_inclusion F χ hUV e O C W B a (p.1, θ)
  rw [he]
  exact scaled_radial_gradient_continuous P _ (logarithmicFirstValue_contDiff F χ hUV e O C W B a)
    continuous_const (Real.continuous_exp.comp continuous_neg) (fun t => Real.exp_pos _) j

/-- The actual logarithmic-polar image before scalar conformal weighting. -/
def rawCore (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
    (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock) : CoreCurve N :=
  CoreCurve.ofContinuousGraphFamily G
    (sphereGraphWave F χ hUV e O W a) (rawGraphDerivative F χ hUV e O W B a)
    (logarithmicSecondValue F χ e O C W a)
    (exists_joint_graph_derivative F χ hUV e O W B a).1
    (rawGraphDerivative_continuous F χ hUV e O W B a)
    (logarithmicSecondValue_continuous F χ hUV e O C W B a)
    (sphereGraphWave_hasDerivAt F χ hUV e O W B a)
    (rawGraphDerivative_inclusion_hasDerivAt F χ hUV e O C W B a)
    (sphereGraphWave_sphereC1 F χ hUV e O W B a)
    (rawGraphDerivative_sphereC1 F χ hUV e O C W B a)
    (sphereGraphWave_gradient_continuous F χ hUV e O W B a P)
    (rawGraphDerivative_gradient_continuous F χ hUV e O C W B a P)

variable (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)

theorem rawCore_value_representative (t : ℝ) (θ : Sphere N) :
    ((rawCore F χ hUV e O C W B a P G).value t).representative θ =
      gaugedValue F χ e O W a.rootWave (Real.exp (-t) • θ.val) :=
  sphereGraphWave_inclusion F χ hUV e O W a (t, θ)

theorem rawCore_first_representative (t : ℝ) (θ : Sphere N) :
    ((rawCore F χ hUV e O C W B a P G).first t).representative θ =
      -gaugedRadialValue F χ e O C W a (Real.exp (-t) • θ.val) :=
  rawGraphDerivative_inclusion F χ hUV e O C W B a (t, θ)

theorem rawCore_value_ae (t : ℝ) :
    (rawCore F χ hUV e O C W B a P G).ambient t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => gaugedValue F χ e O W a.rootWave (Real.exp (-t) • θ.val) :=
  ((rawCore F χ hUV e O C W B a P G).value t).ambient_ae.trans
    (Filter.EventuallyEq.of_eq (funext (rawCore_value_representative F χ hUV e O C W B a P G t)))

theorem rawCore_first_ae (t : ℝ) :
    (rawCore F χ hUV e O C W B a P G).firstAmbient t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => -gaugedRadialValue F χ e O C W a (Real.exp (-t) • θ.val) :=
  ((rawCore F χ hUV e O C W B a P G).first t).ambient_ae.trans
    (Filter.EventuallyEq.of_eq (funext (rawCore_first_representative F χ hUV e O C W B a P G t)))

theorem rawCore_radiation_ae (t : ℝ) :
    ((rawCore F χ hUV e O C W B a P G).value t).radiation =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => graphLift F χ hUV e O W (Real.exp (-t) • θ.val)
        (a.rootWave (Real.exp (-t) • θ.val)) := by
  convert! familyCore_radiation_ae (sphereGraphWave F χ hUV e O W a)
    (exists_joint_graph_derivative F χ hUV e O W B a).1
    (sphereGraphWave_sphereC1 F χ hUV e O W B a)
    (sphereGraphWave_gradient_continuous F χ hUV e O W B a P) t using 1
  funext θ
  unfold sphereGraphWave logarithmicPoint
  rfl

theorem rawCore_gradient_ae (t : ℝ) (j : Fin N × Fin 3) :
    ((rawCore F χ hUV e O C W B a P G).value t).gradient j =ᵐ[sphereMeasure (Fin N × Fin 3)]
      sphereGradient (radialRestriction (gaugedValue F χ e O W a.rootWave) (Real.exp (-t))) j := by
  have he : ((rawCore F χ hUV e O C W B a P G).value t).representative =
      radialRestriction (gaugedValue F χ e O W a.rootWave) (Real.exp (-t)) :=
    funext (rawCore_value_representative F χ hUV e O C W B a P G t)
  exact (((rawCore F χ hUV e O C W B a P G).value t).gradient_ae j).trans
    (Filter.EventuallyEq.of_eq (congrArg (fun f => sphereGradient f j) he))

end PfHk.CenteredRadialGauge
