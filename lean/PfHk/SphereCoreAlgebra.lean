import PfHk.SphereCoreGeometry
import PfHk.PolarCalculusAlgebra
import Mathlib.Tactic.Module

/-! Addition and real scaling preserve the actual sphere core and its
gradient representatives. -/

noncomputable section

namespace PfHk
theorem scalar_first_hasDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a da : ℝ → ℝ} {q dq : ℝ → H} {dda : ℝ} {ddq : H} {t : ℝ}
    (ha : HasDerivAt a (da t) t) (hda : HasDerivAt da dda t)
    (hq : HasDerivAt q (dq t) t) (hdq : HasDerivAt dq ddq t) :
    HasDerivAt (fun s => a s • dq s + da s • q s)
      (a t • ddq + (2 * da t) • dq t + dda • q t) t := by
  convert (ha.smul hdq).add (hda.smul hq) using 1 <;> first
    | rfl
    | (funext s; rfl)
    | (rw [show 2 * da t = da t + da t by ring, add_smul]; abel)
end PfHk

namespace PfHk.SphereCoreGeometry

open MeasureTheory GptLean GptLean.PhysicalFock PfHk.PolarCalculus
open PfHk.SphereAngularField (Sphere SpherePhoton SphereRadiation)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
local instance coreAlgebraPhotonRealInner : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] radiationGraphInclusion

variable {N : ℕ}

def CoreVector.add (u v : CoreVector N) : CoreVector N where
  radiation := u.radiation + v.radiation
  gradient := fun j => u.gradient j + v.gradient j
  representative := fun θ => u.representative θ + v.representative θ
  regularity := u.regularity.add v.regularity
  value_ae := by
    filter_upwards [Lp.coeFn_add u.radiation v.radiation, u.value_ae, v.value_ae] with θ ha hb hc
    rw [ha, Pi.add_apply, map_add, hb, hc]
  gradient_ae := by
    intro j
    filter_upwards [Lp.coeFn_add (u.gradient j) (v.gradient j), u.gradient_ae j, v.gradient_ae j]
      with θ ha hb hc
    rw [ha, Pi.add_apply, hb, hc, sphereGradient_add u.regularity v.regularity]

def CoreVector.scale (a : ℝ) (u : CoreVector N) : CoreVector N where
  radiation := a • u.radiation
  gradient := fun j => a • u.gradient j
  representative := fun θ => a • u.representative θ
  regularity := u.regularity.smul a
  value_ae := by
    filter_upwards [Lp.coeFn_smul a u.radiation, u.value_ae] with θ ha hb
    rw [ha, Pi.smul_apply, LinearMapClass.map_smul_of_tower, hb]
  gradient_ae := by
    intro j
    filter_upwards [Lp.coeFn_smul a (u.gradient j), u.gradient_ae j] with θ ha hb
    rw [ha, Pi.smul_apply, hb]
    exact (sphereGradient_smul u.regularity a j θ).symm

theorem CoreVector.add_ambient (u v : CoreVector N) :
    (u.add v).ambient = u.ambient + v.ambient := by
  unfold CoreVector.ambient CoreVector.add
  exact map_add _ _ _

theorem CoreVector.scale_ambient (a : ℝ) (u : CoreVector N) :
    (u.scale a).ambient = a • u.ambient := by
  unfold CoreVector.ambient CoreVector.scale
  exact LinearMapClass.map_smul_of_tower _ _ _

theorem CoreVector.add_radiation (u v : CoreVector N) :
    (u.add v).radiation = u.radiation + v.radiation := rfl

theorem CoreVector.scale_radiation (a : ℝ) (u : CoreVector N) :
    (u.scale a).radiation = a • u.radiation := rfl

theorem CoreVector.add_gradient (u v : CoreVector N) (j : Fin N × Fin 3) :
    (u.add v).gradient j = u.gradient j + v.gradient j := rfl

theorem CoreVector.scale_gradient (a : ℝ) (u : CoreVector N) (j : Fin N × Fin 3) :
    (u.scale a).gradient j = a • u.gradient j := rfl

theorem CoreVector.add_scale_ambient (a b : ℝ) (u v : CoreVector N) :
    ((u.scale a).add (v.scale b)).ambient = a • u.ambient + b • v.ambient :=
  (CoreVector.add_ambient _ _).trans (congrArg₂ (fun x y : SpherePhoton N => x+y)
    (CoreVector.scale_ambient a u) (CoreVector.scale_ambient b v))

attribute [local irreducible] CoreVector.add CoreVector.scale CoreVector.ambient

/-- A scalar C2 weight acts on the genuine sphere core curve. -/
def CoreCurve.scalar (u : CoreCurve N) (a da dda : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a (da t) t) (hda : ∀ t, HasDerivAt da (dda t) t) : CoreCurve N where
  value := fun t => (u.value t).scale (a t)
  first := fun t => ((u.first t).scale (a t)).add ((u.value t).scale (da t))
  second := fun t => a t • u.second t + (2 * da t) • u.firstAmbient t + dda t • u.ambient t
  radiation_hasDerivAt := by
    intro t
    simp only [CoreVector.add_radiation, CoreVector.scale_radiation]
    convert! (ha t).smul (u.radiation_hasDerivAt t) using 1
  gradient_hasDerivAt := by
    intro j t
    simp only [CoreVector.add_gradient, CoreVector.scale_gradient]
    convert! (ha t).smul (u.gradient_hasDerivAt j t) using 1
  first_hasDerivAt := by
    intro t
    simp only [CoreVector.add_scale_ambient]
    convert! PfHk.scalar_first_hasDerivAt (ha t) (hda t)
      (u.ambient_hasDerivAt t) (u.first_hasDerivAt t) using 1

end PfHk.SphereCoreGeometry
