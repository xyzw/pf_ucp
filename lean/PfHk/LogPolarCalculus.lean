import PfHk.PolarCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Ordinary logarithmic polar change of measure and conformal scaling.
The retained measure identity is universal and uses the same actual
`volume.toSphere` measure as the proved polar measure-preserving map.
No physical coefficient, graph, operator, or estimate occurs in that input.
-/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

variable (I : Type*) [Fintype I] [DecidableEq I]

abbrev Cylinder := ℝ × UnitSphere I

def cylinderMeasure : Measure (Cylinder I) := volume.prod (sphereMeasure I)

def logarithmicJacobian (t : ℝ) : ℝ := Real.exp (-(Fintype.card I : ℝ) * t)

def logarithmicPullback (f : Position I → ℝ) (p : Cylinder I) : ℝ :=
  logarithmicJacobian I p.1 * f (Real.exp (-p.1) • p.2.val)

/-- The ordinary change of variables `X=exp(-t)θ`, including absolute
integrability. The positive-dimension premise excludes the atomic
zero-dimensional Lebesgue measure. -/
structure StandardLogPolarCalculus (I : Type*) [Fintype I] [DecidableEq I] : Prop where
  integrable_change : 0 < Fintype.card I → ∀ f : Position I → ℝ,
    Integrable f volume ↔ Integrable (logarithmicPullback I f) (cylinderMeasure I)
  integral_change : 0 < Fintype.card I → ∀ f : Position I → ℝ, Integrable f volume →
    (∫ X, f X) = ∫ p : Cylinder I, logarithmicPullback I f p ∂cylinderMeasure I

variable {I}
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def conformalValue (c : ℝ) (u : Position I → H) (t : ℝ) (θ : UnitSphere I) : H :=
  Real.exp (-c * t) • u (Real.exp (-t) • θ.val)

theorem radius_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  simpa only [Function.comp_def, mul_neg, mul_one] using
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg

theorem conformalFactor_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-c * s))
      (-c * Real.exp (-c * t)) t := by
  convert! (Real.hasDerivAt_exp (-c * t)).comp t ((hasDerivAt_id t).const_mul (-c)) using 1 <;>
    simp only [Function.comp_def, mul_one] <;> ring

/-- Differentiation of conformal scaling, from ordinary Fréchet differentiation. -/
theorem conformalValue_hasDerivAt (c : ℝ) (u : Position I → H)
    (t : ℝ) (θ : UnitSphere I)
    (hu : DifferentiableAt ℝ u (Real.exp (-t) • θ.val)) :
    HasDerivAt (fun s => conformalValue c u s θ)
      ((-c) • conformalValue c u t θ -
        (Real.exp (-c * t) * Real.exp (-t)) •
          (fderiv ℝ u (Real.exp (-t) • θ.val) θ.val)) t := by
  have hr : HasDerivAt (fun s : ℝ => u (s • θ.val))
      (fderiv ℝ u (Real.exp (-t) • θ.val) θ.val) (Real.exp (-t)) := by
    convert! hu.hasFDerivAt.comp_hasDerivAt (Real.exp (-t))
      ((hasDerivAt_id (Real.exp (-t))).smul_const θ.val) using 1 <;> simp only [one_smul]
  have hf := hr.scomp t (radius_hasDerivAt t)
  have h := (conformalFactor_hasDerivAt c t).smul hf
  convert! h using 1
  simp only [conformalValue, Function.comp_def, map_smul, smul_smul, smul_neg, neg_smul,
    mul_neg, sub_eq_add_neg]
  module

end PfHk.PolarCalculus
