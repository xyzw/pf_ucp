import GptLean.PhysicalFockExponential

/-!
Finite creation-word coassociativity for two actual splittings.
If the three one-photon output components agree, the retained-first and
environment-first assignment polynomials agree in every additive target.
The cutoff component identities are proved separately from real multipliers.
-/

noncomputable section
namespace GptLean.PhysicalFock.SplitCoassociation

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {E : Type*} [AddCommMonoid E]

def eval
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ)) (F : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) : E :=
  ((splitAssignments μ j w).map F).sum

theorem eval_cons
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (f : Lp ℂ 2 μ) (w : List (Lp ℂ 2 μ))
    (F : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    eval μ j (f :: w) F =
      eval μ j w (fun p => F (retainedMap j f :: p.1, p.2)) +
        eval μ j w (fun p => F (p.1, discardedMap μ j f :: p.2)) := by
  simp [eval, splitAssignments, List.map_map, Function.comp_def]

theorem eval_add
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (w : List (Lp ℂ 2 μ))
    (F G : List (Lp ℂ 2 μ) × List (Lp ℂ 2 μ) → E) :
    eval μ j w (fun p => F p + G p) = eval μ j w F + eval μ j w G := by
  simp [eval, List.sum_map_add]

/-- Splitting the retained leg and splitting the environment produce
the same three-mode word polynomial under the actual component identities. -/
theorem eval_coassociate
    (j k : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (h₁ : ∀ f, retainedMap j (retainedMap k f) = retainedMap j f)
    (h₂ : ∀ f, discardedMap μ j (retainedMap k f) = retainedMap k (discardedMap μ j f))
    (h₃ : ∀ f, discardedMap μ k f = discardedMap μ k (discardedMap μ j f))
    (w : List (Lp ℂ 2 μ))
    (F : List (Lp ℂ 2 μ) → List (Lp ℂ 2 μ) → List (Lp ℂ 2 μ) → E) :
    eval μ k w (fun p => eval μ j p.1 (fun q => F q.1 q.2 p.2)) =
      eval μ j w (fun p => eval μ k p.2 (fun q => F p.1 q.1 q.2)) := by
  induction w generalizing F with
  | nil => simp [eval, splitAssignments]
  | cons f w ih =>
    simp only [eval_cons, eval_add]
    rw [ih (fun a b c => F (retainedMap j (retainedMap k f) :: a) b c),
      ih (fun a b c => F a (discardedMap μ j (retainedMap k f) :: b) c),
      ih (fun a b c => F a b (discardedMap μ k f :: c)), h₁ f, h₂ f, h₃ f]
    exact add_assoc _ _ _

end GptLean.PhysicalFock.SplitCoassociation
