import PfHk.SphereCoreAlgebra
import PfHk.L2DensityIntegral

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SphereRadiation)
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
attribute [local irreducible] CoreVector.scale

theorem CoreVector.scaled_radiation_ae {N : ℕ} (u : CoreVector N) (a : ℝ)
    (f : Sphere N → RadiationGraphSpace)
    (hu : u.radiation =ᵐ[sphereMeasure (Fin N × Fin 3)] f) :
    (u.scale a).radiation =ᵐ[sphereMeasure (Fin N × Fin 3)] fun θ => a • f θ := by
  have he := CoreVector.scale_radiation a u
  apply (Filter.EventuallyEq.of_eq (congrArg (fun v : SphereRadiation N => ⇑v) he)).trans
  exact L2QuadraticForms.real_smul_normed_ae a u.radiation hu

theorem CoreVector.radiation_ae_of_eq {N : ℕ} (u v : CoreVector N) (h : u = v)
    (f : Sphere N → RadiationGraphSpace)
    (hv : v.radiation =ᵐ[sphereMeasure (Fin N × Fin 3)] f) :
    u.radiation =ᵐ[sphereMeasure (Fin N × Fin 3)] f := by
  cases h
  exact hv

end PfHk.SphereCoreGeometry
