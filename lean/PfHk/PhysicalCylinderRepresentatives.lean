import PfHk.PhysicalCylinderSource
import PfHk.L2DensityIntegral
import PfHk.SphereCoreRepresentatives

/-! Actual representatives of the conformal physical core and its radial
and angular covariant derivatives. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalFieldRegularity
  PfHk.PhysicalOperatorDomain PfHk.WeylGraphC1Calculus PfHk.PolarCalculus
  PfHk.SphereCoreGeometry PfHk.CenteredRadialGauge
open PfHk.SphereAngularField (Sphere SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
local instance cylinderRepresentativesRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] CenteredSphereAngularField.angularVector kernelField
  gaugedValue coreValue graphLift gaugedRadialValue angularCore rawCore
  CoreCurve.conformal CoreCurve.scalar CoreVector.scale CoreVector.ambient

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N) (C : CanonicalSectorCCR photonMeasure)
  (W : ConcreteWeylLaw photonMeasure) (B : StandardWeylGraphC1 W)
  (P : StandardPolarCalculus (Fin N × Fin 3) PhotonFock)
  (G : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
  {s : Set (Configuration N)} (a : SmoothCore s)

theorem curve_ambient_ae (c t : ℝ) :
    (curve F χ hUV e O C W B P G a c).ambient t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => Real.exp (-c*t) • gaugedValue F χ e O W a.rootWave (Real.exp (-t) • θ.val) := by
  have he := (rawCore F χ hUV e O C W B a P G).conformal_ambient c t
  exact (Filter.EventuallyEq.of_eq (congrArg (fun v : SpherePhoton N => ⇑v) he)).trans
    (L2QuadraticForms.real_smul_ae _ _ (rawCore_value_ae F χ hUV e O C W B a P G t))

theorem curve_radiation_ae (c t : ℝ) :
    ((curve F χ hUV e O C W B P G a c).value t).radiation =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => Real.exp (-c*t) • graphLift F χ hUV e O W (Real.exp (-t) • θ.val)
        (a.rootWave (Real.exp (-t) • θ.val)) := by
  exact CoreVector.radiation_ae_of_eq _ _
    ((rawCore F χ hUV e O C W B a P G).conformal_value c t) _
    (CoreVector.scaled_radiation_ae _ (Real.exp (-c*t)) _
      (rawCore_radiation_ae F χ hUV e O C W B a P G t))

theorem curve_gradient_ae (c t : ℝ) (j : Fin N × Fin 3) :
    ((curve F χ hUV e O C W B P G a c).value t).gradient j =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => Real.exp (-c*t) • sphereGradient
        (radialRestriction (gaugedValue F χ e O W a.rootWave) (Real.exp (-t))) j θ := by
  have he := (congrArg (fun v : CoreVector N => v.gradient j)
    ((rawCore F χ hUV e O C W B a P G).conformal_value c t)).trans
      (CoreVector.scale_gradient (Real.exp (-c*t)) ((rawCore F χ hUV e O C W B a P G).value t) j)
  exact (Filter.EventuallyEq.of_eq (congrArg (fun v : SpherePhoton N => ⇑v) he)).trans
    (L2QuadraticForms.real_smul_ae _ _ (rawCore_gradient_ae F χ hUV e O C W B a P G t j))

theorem radial_ae (c t : ℝ) :
    (curve F χ hUV e O C W B P G a c).firstAmbient t +
      c • (curve F χ hUV e O C W B P G a c).ambient t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => -((Real.exp (-c*t)*Real.exp (-t)) •
        radialFirst (gaugedValue F χ e O W a.rootWave) (Real.exp (-t)) θ) := by
  have he := (rawCore F χ hUV e O C W B a P G).conformal_radial c t
  apply (Filter.EventuallyEq.of_eq (congrArg (fun v : SpherePhoton N => ⇑v) he)).trans
  have ha := L2QuadraticForms.real_smul_ae (Real.exp (-c*t)) _
    (rawCore_first_ae F χ hUV e O C W B a P G t)
  apply ha.trans
  exact ae_of_all _ fun θ => by
    have hEuler := gaugedValue_radial F χ hUV e O C W B a (Real.exp (-t) • θ.val)
    have hm := (fderiv ℝ (gaugedValue F χ e O W a.rootWave) (Real.exp (-t) • θ.val)).map_smul
      (Real.exp (-t)) θ.val
    have hr : Real.exp (-t) • radialFirst (gaugedValue F χ e O W a.rootWave)
        (Real.exp (-t)) θ = gaugedRadialValue F χ e O C W a (Real.exp (-t) • θ.val) :=
      hm.symm.trans hEuler
    calc
      _ = Real.exp (-c*t) • (-(Real.exp (-t) •
        radialFirst (gaugedValue F χ e O W a.rootWave) (Real.exp (-t)) θ)) :=
        congrArg (fun v : PhotonFock => Real.exp (-c*t) • (-v)) hr.symm
      _ = _ := by rw [smul_neg, smul_smul]

def angular (c t : ℝ) (j : Fin N × Fin 3) : SpherePhoton N :=
  CenteredSphereAngularField.angularVector F χ hUV e O C
    ((curve F χ hUV e O C W B P G a c).value t).gradient
    ((curve F χ hUV e O C W B P G a c).value t).radiation j t

theorem rawAngular_ae (t : ℝ) (j : Fin N × Fin 3) :
    CenteredSphereAngularField.angularVector F χ hUV e O C
      ((rawCore F χ hUV e O C W B a P G).value t).gradient
      ((rawCore F χ hUV e O C W B a P G).value t).radiation j t =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => angularCore F χ hUV e O C W a.rootWave (Real.exp (-t)) θ j := by
  filter_upwards [CenteredSphereAngularField.angularVector_ae F χ hUV e O C
    ((rawCore F χ hUV e O C W B a P G).value t).gradient
    ((rawCore F χ hUV e O C W B a P G).value t).radiation j t,
    rawCore_radiation_ae F χ hUV e O C W B a P G t,
    rawCore_gradient_ae F χ hUV e O C W B a P G t j] with θ hx hq hp
  unfold angularCore
  exact hx.trans (congrArg₂ (fun v : PhotonFock => fun q : RadiationGraphSpace =>
    v + Complex.I • kernelField C (CenteredSphereAngularField.coefficient F χ hUV e O j t θ) q) hp hq)

theorem curveAngular_ae (c t : ℝ) (j : Fin N × Fin 3) :
    angular F χ hUV e O C W B P G a c t j =ᵐ[sphereMeasure (Fin N × Fin 3)]
      fun θ => Real.exp (-c*t) • angularCore F χ hUV e O C W a.rootWave (Real.exp (-t)) θ j := by
  have he := (congrArg (fun v : CoreVector N =>
    CenteredSphereAngularField.angularVector F χ hUV e O C v.gradient v.radiation j t)
    ((rawCore F χ hUV e O C W B a P G).conformal_value c t)).trans
    (angularVector_scale F χ hUV e O C (Real.exp (-c*t)) t
      ((rawCore F χ hUV e O C W B a P G).value t) j)
  exact (Filter.EventuallyEq.of_eq (congrArg (fun v : SpherePhoton N => ⇑v) he)).trans
    (L2QuadraticForms.real_smul_ae _ _ (rawAngular_ae F χ hUV e O C W B P G a t j))

end PfHk.PhysicalCylinderSource
