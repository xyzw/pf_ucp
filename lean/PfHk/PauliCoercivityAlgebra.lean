import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Real inequalities used after the physical derivative and multiplier
bounds. This module contains no operator-domain or continuation premise. -/

namespace PfHk.PauliCoercivityAlgebra

open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 30000

theorem sum_scalar_bounds {S Q : Type*} [Fintype S] [Fintype Q]
    (r : S → ℝ) (d : S → Q → ℝ) (m : S → ℝ) (ε C : ℝ)
    (h : ∀ s, r s ≤ ε * (∑ q, d s q) + C * m s) :
    (∑ s, r s) ≤ ε * (∑ q, ∑ s, d s q) + C * ∑ s, m s := by
  calc
    _ ≤ ∑ s, (ε * (∑ q, d s q) + C * m s) :=
      Finset.sum_le_sum (fun s _ => h s)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]

theorem sum_uniform_bounds {S Q : Type*} [Fintype S] [Fintype Q]
    (f : Q → S → ℝ) (r m : S → ℝ) (a b : ℝ)
    (h : ∀ q s, f q s ≤ a * r s + b * m s) :
    (∑ q, ∑ s, f q s) ≤
      (Fintype.card Q : ℝ) * a * (∑ s, r s) +
      (Fintype.card Q : ℝ) * b * ∑ s, m s := by
  calc
    _ ≤ ∑ _q : Q, ∑ s, (a * r s + b * m s) :=
      Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun s _ => h q s))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

theorem sum_repeated_bound {Q : Type*} [Fintype Q]
    (f : Q → ℝ) (ε O C m : ℝ) (h : ∀ q, f q ≤ ε * O + C * m) :
    (∑ q, f q) ≤ (Fintype.card Q : ℝ) * ε * O + (Fintype.card Q : ℝ) * C * m := by
  calc
    _ ≤ ∑ _q : Q, (ε * O + C * m) := Finset.sum_le_sum (fun q _ => h q)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem recover_ordinary {O P R m F A d K e ε C : ℝ}
    (hO : 0 ≤ O)
    (hrec : O ≤ 3 * P + 9 * e ^ 2 * F + 9 * A)
    (hfield : F ≤ 8 * d * K ^ 2 * R + 2 * d * K ^ 2 * m)
    (hvector : A ≤ d * ε * O + d * C * m)
    (hsmall : 9 * d * ε ≤ 1 / 2) :
    O ≤ 6 * P + 144 * e ^ 2 * d * K ^ 2 * R +
      (36 * e ^ 2 * d * K ^ 2 + 18 * d * C) * m := by
  have hf := mul_le_mul_of_nonneg_left hfield (by positivity : 0 ≤ 9 * e ^ 2)
  have ha := mul_le_mul_of_nonneg_left hvector (by norm_num : (0 : ℝ) ≤ 9)
  have hs := mul_le_mul_of_nonneg_right hsmall hO
  nlinarith only [hrec, hf, ha, hs]

theorem form_lower_bound {O P R m V W Q L C ε C₀ : ℝ}
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hW : 0 ≤ W) (hε : 0 ≤ ε)
    (hO : O ≤ L * (P + R) + C * m)
    (hV : V ≤ ε * O + C₀ * m)
    (hQ : Q = P / 2 + R + W - V)
    (hsmall : ε * L ≤ 1 / 4) :
    (P + R) / 4 - (C₀ + ε * C) * m ≤ Q := by
  have ho := mul_le_mul_of_nonneg_left hO hε
  have hs := mul_le_mul_of_nonneg_right hsmall (add_nonneg hP hR)
  nlinarith only [ho, hs, hV, hQ, hR, hW]

theorem full_energy_bound {O P R m V W Q L C ε C₀ : ℝ}
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hW : 0 ≤ W) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hO : O ≤ L * (P + R) + C * m)
    (hV : V ≤ ε * O + C₀ * m)
    (hQ : Q = P / 2 + R + W - V)
    (hsmall : ε * L ≤ 1 / 4) :
    O + P + R ≤ 4 * (L + 1) * Q + (4 * (L + 1) * (C₀ + ε * C) + C) * m := by
  have hl := form_lower_bound hP hR hW hε hO hV hQ hsmall
  have hpr : P + R ≤ 4 * Q + 4 * (C₀ + ε * C) * m := by linarith only [hl]
  have hm := mul_le_mul_of_nonneg_left hpr (by linarith only [hL] : 0 ≤ L + 1)
  nlinarith only [hO, hm]

end PfHk.PauliCoercivityAlgebra
