import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Ring

/-! Scalar integral identities used to transport the Coulomb and magnetic
pairings without unfolding the physical state spaces during algebra. -/

noncomputable section

namespace PfHk.CounterexamplePairingAlgebra

open MeasureTheory

set_option autoImplicit false
set_option Elab.async false

variable {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}

/-- Remove a singleton particle index from a finite sum. -/
theorem sum_one {J : Type*} [Fintype J] (f : Fin 1 × J → ℝ) :
    (∑ q, f q) = ∑ j, f (0, j) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, Fin.default_eq_zero]

/-- An almost-everywhere Coulomb coefficient gives its scalar pairing. -/
theorem scalar_integral (Z : ℝ) (v n r : Q → ℝ)
    (hv : v =ᵐ[μ] fun x => -Z / r x) :
    (∫ x, v x * n x ∂μ) = -Z * ∫ x, n x / r x ∂μ := by
  calc
    _ = ∫ x, -Z * (n x / r x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
      ring
    _ = _ := integral_const_mul _ _

/-- An almost-everywhere scalar factor passes through the integral. -/
theorem scaled_integral (t : ℝ) (f g : Q → ℝ)
    (h : f =ᵐ[μ] fun x => t * g x) :
    (∫ x, f x ∂μ) = t * ∫ x, g x ∂μ :=
  (integral_congr_ae h).trans (integral_const_mul _ _)

/-- A common scalar factor passes through a finite family of integrals. -/
theorem scaled_sum {J : Type*} [Fintype J] (t : ℝ) (f g : J → Q → ℝ)
    (h : ∀ j, f j =ᵐ[μ] fun x => t * g j x) :
    (∑ j, ∫ x, f j x ∂μ) = t * ∑ j, ∫ x, g j x ∂μ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => scaled_integral t (f j) (g j) (h j)

/-- Transport the magnetic pairing through equal Lp representatives and
an almost-everywhere scalar coefficient identity. -/
theorem magnetic_pairing_ae {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [Inner ℂ H]
    (ψ ψ' d d' δ : Lp H 2 μ) (a b : Q → ℝ) (t : ℝ)
    (hψ : ψ = ψ') (hd : d = d') (hδ : δ = (-Complex.I) • d)
    (ha : a =ᵐ[μ] fun x => t * b x) :
    (fun x => a x * (inner ℂ (ψ x) (δ x)).re) =ᵐ[μ]
      fun x => t * (b x * (inner ℂ (ψ' x) ((-Complex.I) • d' x)).re) := by
  subst ψ'
  subst d'
  subst δ
  filter_upwards [Lp.coeFn_smul (-Complex.I) d, ha] with x hdx hax
  rw [hdx, hax]
  exact mul_assoc _ _ _

end PfHk.CounterexamplePairingAlgebra
