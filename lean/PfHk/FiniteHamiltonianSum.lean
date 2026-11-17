import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Abel

/-! Finite Hilbert-space algebra for the five external-potential terms. -/

noncomputable section
namespace PfHk.FiniteHamiltonianSum

variable {H I J : Type*} [AddCommGroup H] [Module ℂ H] [Fintype I] [Fintype J]

abbrev Index (I J : Type*) := I ⊕ (I ⊕ (J ⊕ (J ⊕ Unit)))

def term (a b : I → H) (d v : J → H) (w : H) : Index I J → H
  | .inl i => a i
  | .inr (.inl i) => (1 / 2 : ℂ) • b i
  | .inr (.inr (.inl n)) => (-Complex.I / 2) • d n
  | .inr (.inr (.inr (.inl n))) => v n
  | .inr (.inr (.inr (.inr _))) => w

theorem sum_eq (a b : I → H) (d v : J → H) (w : H) :
    (∑ t, term a b d v w t) =
      (∑ i, a i) + (1 / 2 : ℂ) • (∑ i, b i) +
        (-Complex.I / 2) • (∑ n, d n) + ((∑ n, v n) + w) := by
  simp only [Index, Fintype.sum_sum_type, term, Fintype.sum_unique,
    ← Finset.smul_sum, add_assoc]

theorem group_scalar (a b d p n : H) : a + b + d + p - n = a + b + d + (p - n) := by
  abel

end PfHk.FiniteHamiltonianSum
