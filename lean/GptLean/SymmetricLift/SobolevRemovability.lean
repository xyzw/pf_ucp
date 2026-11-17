import GptLean.SymmetricLift.CollisionGeometry
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.Module

/-!
Removal of exceptional coordinate lines in the tensor-lift appendix.

The integration-by-parts theorem below proves a weak derivative identity
from classical derivatives away from a singular set. Its geometric input
is that almost every entire line avoids that set. No weak derivative
identity on the full space is assumed. This covers the smooth input step
of the lift. Approximation of a general H¹ input is a separate obligation.
-/

noncomputable section

namespace GptLean.SymmetricLift

open MeasureTheory Filter
attribute [local instance] Classical.propDecidable

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Base points whose whole line stays inside the regular set. -/
def regularLine (D : Set E) (v x : E) : Prop :=
  ∀ t : ℝ, x + t • v ∈ D

theorem regularLine_translate (D : Set E) (v x : E) (s : ℝ) :
    regularLine D v (x + s • v) ↔ regularLine D v x := by
  constructor
  · intro h t
    have ht := h (t - s)
    convert ht using 1
    module
  · intro h t
    have ht := h (s + t)
    convert ht using 1
    module

/-- Changing the function to zero on exceptional whole lines creates a
representative with a line derivative at every point. -/
theorem hasLineDerivAt_regularLine_patch
    {D : Set E} {v : E} {f f' : E → F}
    (hf : ∀ x ∈ D, HasLineDerivAt ℝ f (f' x) x v) (x : E) :
    HasLineDerivAt ℝ (fun y => if regularLine D v y then f y else 0)
      (if regularLine D v x then f' x else 0) x v := by
  unfold HasLineDerivAt
  simp only [regularLine_translate]
  by_cases hx : regularLine D v x
  · simp only [ite_eq_left hx]
    exact hf x (by simpa using hx 0)
  · simp only [ite_eq_right hx]
    exact hasDerivAt_const 0 0

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Global weak derivative identity from derivatives on the regular set.
The integrability assumptions are precisely the three products used by
integration by parts, so compactly supported tests can be used locally. -/
theorem integral_smul_lineDeriv_eq_neg_of_ae_regularLine
    {D : Set E} {v : E} {f f' : E → F} {φ φ' : E → ℝ}
    (hline : ∀ᵐ x ∂μ, regularLine D v x)
    (hf : ∀ x ∈ D, HasLineDerivAt ℝ f (f' x) x v)
    (hφ : ∀ x, HasLineDerivAt ℝ φ (φ' x) x v)
    (hφ'f : Integrable (fun x => φ' x • f x) μ)
    (hφf' : Integrable (fun x => φ x • f' x) μ)
    (hφf : Integrable (fun x => φ x • f x) μ) :
    ∫ x, φ x • f' x ∂μ = - ∫ x, φ' x • f x ∂μ := by
  let g := fun x => if regularLine D v x then f x else 0
  let g' := fun x => if regularLine D v x then f' x else 0
  have hg : g =ᵐ[μ] f := hline.mono (fun x hx => ite_eq_left hx)
  have hg' : g' =ᵐ[μ] f' := hline.mono (fun x hx => ite_eq_left hx)
  have h₁ : (fun x => φ' x • g x) =ᵐ[μ] (fun x => φ' x • f x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have h₂ : (fun x => φ x • g' x) =ᵐ[μ] (fun x => φ x • f' x) := by
    filter_upwards [hg'] with x hx
    rw [hx]
  have h₃ : (fun x => φ x • g x) =ᵐ[μ] (fun x => φ x • f x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (hφ'f.congr h₁.symm) (hφf'.congr h₂.symm) (hφf.congr h₃.symm)
    (fun x _ => hφ x) (fun x _ => hasLineDerivAt_regularLine_patch hf x)
  change (∫ x, φ x • g' x ∂μ) = -(∫ x, φ' x • g x ∂μ) at h
  rwa [integral_congr_ae h₁, integral_congr_ae h₂] at h

/-- Collision diagonals contribute no distributional boundary term.
This is the concrete geometric specialization used for a smooth tensor
input, once the local metric bound supplies the integrable test products. -/
theorem integral_smul_coordinate_derivative_across_collisions
    {N : ℕ} (q : Fin N × Fin 3)
    {f f' : Configuration N → F} {φ φ' : Configuration N → ℝ}
    (hf : ∀ x ∈ distinctConfigurations N,
      HasLineDerivAt ℝ f (f' x) x (EuclideanSpace.single q 1))
    (hφ : ∀ x, HasLineDerivAt ℝ φ (φ' x) x (EuclideanSpace.single q 1))
    (hφ'f : Integrable (fun x => φ' x • f x) volume)
    (hφf' : Integrable (fun x => φ x • f' x) volume)
    (hφf : Integrable (fun x => φ x • f x) volume) :
    ∫ x, φ x • f' x = - ∫ x, φ' x • f x :=
  integral_smul_lineDeriv_eq_neg_of_ae_regularLine
    (ae_coordinate_line_distinct q) hf hφ hφ'f hφf' hφf

end GptLean.SymmetricLift
