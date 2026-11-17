import PfHk.SphereCoreGeometry
import PfHk.SphereGradientGraph
import PfHk.ClosedGraphDifferentiation

/-! Ordinary sphere-gradient differentiation on actual photon core
representatives, through the closed ordinary gradient graph. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000
local instance sphereCoreGraphPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ}

theorem CoreVector.gradient_graph (v : CoreVector N) :
    (v.ambient, v.gradient) ∈ sphereGradientGraph (Fin N × Fin 3) PhotonFock :=
  mem_sphereGradientGraph _ _ v.ambient v.gradient v.representative v.regularity v.ambient_ae v.gradient_ae

/-- The gradient derivative follows from closed operator calculus and
ordinary first-order representative regularity. No second angular
derivative of a gauge is asserted or assumed. -/
theorem gradient_hasDerivAt (P : StandardSphereGradient (Fin N × Fin 3) PhotonFock)
    (u du : ℝ → CoreVector N)
    (hu : ∀ t, L2OperatorDerivative.HasL2DerivAt (fun s => (u s).ambient) (du t).ambient t)
    (hdu : Continuous (fun t => (du t).ambient))
    (hdp : Continuous (fun t => (du t).gradient)) (j : Fin N × Fin 3) (t : ℝ) :
    L2OperatorDerivative.HasL2DerivAt (fun s => (u s).gradient j) ((du t).gradient j) t := by
  have hp := ClosedGraphDifferentiation.hasDerivAt_snd
    (sphereGradientGraph (Fin N × Fin 3) PhotonFock)
    (sphereGradientGraph_closed (Fin N × Fin 3) PhotonFock) P.closable
    hu hdu hdp (fun s => (u s).gradient_graph) (fun s => (du s).gradient_graph) t
  let L : ((Fin N × Fin 3) → SpherePhoton N) →L[ℝ] SpherePhoton N :=
    ContinuousLinearMap.proj j
  convert! L.hasFDerivAt.comp_hasDerivAt t hp using 1

end PfHk.SphereCoreGeometry
