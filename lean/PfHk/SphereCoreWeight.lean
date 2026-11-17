import PfHk.SphereCoreFormScaling
import PfHk.SmoothCarlemanConjugation

/-! The actual exponential Carleman weight on sphere core curves. A
proved smooth extension below the working cylinder removes the irrelevant
singularity at t = 0 without changing any expression for t ≥ 2. -/

noncomputable section
namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus PfHk.CarlemanWeights
  PfHk.CylinderConjugation
open PfHk.SphereAngularField (SpherePhoton)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
local instance coreWeightPhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ}

def CoreCurve.exponential (u : CoreCurve N) (τ α : ℝ) : CoreCurve N :=
  u.scalar (smoothExponential τ α) (deriv (smoothExponential τ α))
    (deriv (deriv (smoothExponential τ α)))
    (smoothExponential_hasDerivAt τ α) (smoothExponential_deriv_hasDerivAt τ α)

theorem CoreCurve.exponential_value (u : CoreCurve N) (τ α t : ℝ) :
    (u.exponential τ α).value t = (u.value t).scale (smoothExponential τ α t) := rfl

theorem CoreCurve.exponential_ambient (u : CoreCurve N) (τ α : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    (u.exponential τ α).ambient t = weighted τ (weight α) u.ambient t := by
  change ((u.value t).scale (smoothExponential τ α t)).ambient = _
  exact (CoreVector.scale_ambient _ _).trans (smoothExponential_weighted τ α u.ambient ht)

theorem CoreCurve.exponential_first (u : CoreCurve N) (τ α : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    (u.exponential τ α).firstAmbient t =
      weightedFirst τ (weight α) (weightPrime α) u.ambient u.firstAmbient t := by
  change (((u.first t).scale (smoothExponential τ α t)).add
    ((u.value t).scale (deriv (smoothExponential τ α) t))).ambient = _
  exact (CoreVector.add_scale_ambient _ _ _ _).trans
    (smoothExponential_weightedFirst τ α u.ambient u.firstAmbient ht)

theorem CoreCurve.exponential_second (u : CoreCurve N) (τ α : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    (u.exponential τ α).second t = weightedSecond τ (weight α) (weightPrime α) (beta α)
      u.ambient u.firstAmbient u.second t := by
  change smoothExponential τ α t • u.second t +
    (2 * deriv (smoothExponential τ α) t) • u.firstAmbient t +
    deriv (deriv (smoothExponential τ α)) t • u.ambient t = _
  exact smoothExponential_weightedSecond τ α u.ambient u.firstAmbient u.second ht

end PfHk.SphereCoreGeometry
