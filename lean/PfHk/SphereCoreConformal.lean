import PfHk.SphereCoreAlgebra
import PfHk.LogPolarCalculus

/-! Conformal scaling of the actual logarithmic sphere core curve. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (SpherePhoton)
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
local instance conformalCorePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

theorem conformalFactor_first_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s => -c*Real.exp (-c*s)) (c^2*Real.exp (-c*t)) t := by
  convert! (conformalFactor_hasDerivAt c t).const_mul (-c) using 1 <;> first | rfl | ring

private theorem conformal_radial_algebra {H : Type*} [AddCommGroup H] [Module ℝ H]
    (a c : ℝ) (v w : H) :
    (a • v + (-c*a) • w) + c • (a • w) = a • v := by
  simp only [smul_smul, neg_mul, neg_smul]
  abel

variable {N : ℕ}

def CoreCurve.conformal (u : CoreCurve N) (c : ℝ) : CoreCurve N :=
  u.scalar (fun t => Real.exp (-c*t)) (fun t => -c*Real.exp (-c*t))
    (fun t => c^2*Real.exp (-c*t))
    (conformalFactor_hasDerivAt c) (conformalFactor_first_hasDerivAt c)

theorem CoreCurve.conformal_value (u : CoreCurve N) (c t : ℝ) :
    (u.conformal c).value t = (u.value t).scale (Real.exp (-c*t)) := rfl

theorem CoreCurve.conformal_ambient (u : CoreCurve N) (c t : ℝ) :
    (u.conformal c).ambient t = Real.exp (-c*t) • u.ambient t := by
  change ((u.value t).scale (Real.exp (-c*t))).ambient = _
  exact CoreVector.scale_ambient _ _

theorem CoreCurve.conformal_first (u : CoreCurve N) (c t : ℝ) :
    (u.conformal c).firstAmbient t =
      Real.exp (-c*t) • u.firstAmbient t + (-c*Real.exp (-c*t)) • u.ambient t := by
  change (((u.first t).scale (Real.exp (-c*t))).add
    ((u.value t).scale (-c*Real.exp (-c*t)))).ambient = _
  exact CoreVector.add_scale_ambient _ _ _ _

theorem CoreCurve.conformal_second (u : CoreCurve N) (c t : ℝ) :
    (u.conformal c).second t = Real.exp (-c*t) • u.second t +
      (2*(-c*Real.exp (-c*t))) • u.firstAmbient t +
      (c^2*Real.exp (-c*t)) • u.ambient t := rfl

attribute [local irreducible] CoreCurve.conformal CoreCurve.scalar CoreVector.scale
  CoreVector.add CoreVector.ambient

theorem CoreCurve.conformal_radial (u : CoreCurve N) (c t : ℝ) :
    (u.conformal c).firstAmbient t + c • (u.conformal c).ambient t =
      Real.exp (-c*t) • u.firstAmbient t := by
  exact (congrArg₂ (fun x y : SpherePhoton N => x + c • y)
    (u.conformal_first c t) (u.conformal_ambient c t)).trans
      (conformal_radial_algebra (Real.exp (-c*t)) c (u.firstAmbient t) (u.ambient t))

end PfHk.SphereCoreGeometry
