import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.Ring

/-!
Ordinary radial integration by parts after logarithmic conformal scaling.
The angular term enters only through its weak form, so the calculation
requires no second angular derivative of a gauge coefficient.
-/

noncomputable section
namespace PfHk.WeakCylinderForm

open MeasureTheory
open scoped InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def radialFlux (c : ℝ) (v z dz : ℝ → H) (t : ℝ) : ℝ :=
  inner ℝ (v t) (dz t + c • z t)

def density (c : ℝ) (r A T : ℝ → ℝ) (v dv z dz : ℝ → H) (t : ℝ) : ℝ :=
  inner ℝ (dv t + c • v t) (dz t + c • z t) + A t + r t * T t

def operator (c : ℝ) (r : ℝ → ℝ) (z ddz k q : ℝ → H) (t : ℝ) : H :=
  -ddz t + k t + c ^ 2 • z t + r t • q t

theorem radialFlux_hasDerivAt (c : ℝ) {r A T : ℝ → ℝ}
    {v dv z dz ddz k q : ℝ → H} {t : ℝ}
    (hv : HasDerivAt v (dv t) t) (hz : HasDerivAt z (dz t) t)
    (hdz : HasDerivAt dz (ddz t) t)
    (hA : A t = inner ℝ (v t) (k t)) (hT : T t = inner ℝ (v t) (q t)) :
    HasDerivAt (radialFlux c v z dz)
      (density c r A T v dv z dz t - inner ℝ (v t) (operator c r z ddz k q t)) t := by
  have h := hv.inner ℝ (hdz.add (hz.const_smul c))
  convert h using 1 <;> try rfl
  simp only [density, operator, hA, hT, Pi.add_apply, Pi.smul_apply, inner_add_left, inner_add_right,
    inner_neg_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Weak logarithmic radial integration by parts as an equality of actual
integrals. The hypotheses are ordinary derivative and integrability facts. -/
theorem integral_density_eq_operator (c : ℝ) {r A T : ℝ → ℝ}
    {v dv z dz ddz k q : ℝ → H}
    (hv : ∀ t, HasDerivAt v (dv t) t) (hz : ∀ t, HasDerivAt z (dz t) t)
    (hdz : ∀ t, HasDerivAt dz (ddz t) t)
    (hA : ∀ t, A t = inner ℝ (v t) (k t)) (hT : ∀ t, T t = inner ℝ (v t) (q t))
    (hflux : Integrable (radialFlux c v z dz))
    (hform : Integrable (density c r A T v dv z dz))
    (hop : Integrable (fun t => inner ℝ (v t) (operator c r z ddz k q t))) :
    (∫ t, density c r A T v dv z dz t) =
      ∫ t, inner ℝ (v t) (operator c r z ddz k q t) := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun t => radialFlux_hasDerivAt c (hv t) (hz t) (hdz t) (hA t) (hT t))
    (hform.sub hop) hflux
  rw [integral_sub hform hop] at h
  exact sub_eq_zero.mp h

/-- The usual fundamental lemma is already available in Mathlib. It
turns the scalar localized weak polar equation into an almost-everywhere
identity, with no operator-valued differentiation premise. -/
theorem ae_zero_of_scalar_tests {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ t, η t * f t) = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
  intro η hη hs
  exact h η hη hs

end PfHk.WeakCylinderForm
