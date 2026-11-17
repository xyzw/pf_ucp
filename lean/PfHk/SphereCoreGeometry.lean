import PfHk.PhysicalSphereSpace
import PfHk.L2OperatorDerivative

/-!
The ordinary sphere core used for weak polar transport. Its gradients are
the actual derivatives of a C1 representative. The radiation graph and
all gradient components live in the actual surface-measure L2 spaces.
No operator equation or form product rule occurs in this core definition.
-/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ}

/-- A first-order sphere core vector with its genuine radiation graph. -/
structure CoreVector (N : ℕ) where
  radiation : SphereRadiation N
  gradient : (Fin N × Fin 3) → SpherePhoton N
  representative : Sphere N → PhotonFock
  regularity : SphereC1 representative
  value_ae : (fun θ => radiationGraphInclusion (radiation θ)) =ᵐ[sphereMeasure (Fin N × Fin 3)]
    representative
  gradient_ae : ∀ j, gradient j =ᵐ[sphereMeasure (Fin N × Fin 3)] sphereGradient representative j

def CoreVector.ambient (v : CoreVector N) : SpherePhoton N :=
  spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3)) v.radiation

theorem CoreVector.ambient_ae (v : CoreVector N) :
    v.ambient =ᵐ[sphereMeasure (Fin N × Fin 3)] v.representative :=
  (radiationGraphInclusion.coeFn_compLpL v.radiation).trans v.value_ae

/-- Strong derivatives in the graph and ordinary-gradient L2 spaces.
The second derivative is needed only in the ambient Hilbert space. -/
structure CoreCurve (N : ℕ) where
  value : ℝ → CoreVector N
  first : ℝ → CoreVector N
  second : ℝ → SpherePhoton N
  radiation_hasDerivAt : ∀ t, L2OperatorDerivative.HasL2DerivAt
    (fun s => (value s).radiation) (first t).radiation t
  gradient_hasDerivAt : ∀ j t, L2OperatorDerivative.HasL2DerivAt
    (fun s => (value s).gradient j) ((first t).gradient j) t
  first_hasDerivAt : ∀ t, L2OperatorDerivative.HasL2DerivAt
    (fun s => (first s).ambient) (second t) t

def CoreCurve.ambient (u : CoreCurve N) (t : ℝ) : SpherePhoton N := (u.value t).ambient

def CoreCurve.firstAmbient (u : CoreCurve N) (t : ℝ) : SpherePhoton N := (u.first t).ambient

theorem CoreCurve.ambient_hasDerivAt (u : CoreCurve N) (t : ℝ) :
    L2OperatorDerivative.HasL2DerivAt u.ambient (u.firstAmbient t) t := by
  let L := (spatialRadiationInclusion (sphereMeasure (Fin N × Fin 3))).restrictScalars ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt t (u.radiation_hasDerivAt t)
  convert! h using 1

end PfHk.SphereCoreGeometry
