import GptLean.Repair.Channel
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
The current manuscript's new general part (ii) of
`lem-fermionic-current-repair` and `pair-Hardy-bound`.

This file extends the finite channel algebra to any summable index family,
proves the pair-counting coefficient in the Hardy bound, and derives the exact
constant C_N = 2(N-1)b_N. Inputs are the usual covariant product rule, Parseval
identities, and the single-pair diamagnetic/Hardy estimate. The actual countable
trace-class channel and Sobolev form-domain passages are not constructed here.
-/

namespace GptLean.Repair

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Infinite channel energy identity from Parseval and the connection.
A `HasSum` hypothesis records genuine convergence, not a formal infinite sum. -/
theorem countable_channel_energy {α : Type*}
    (K K' : α → H →ₗ[ℂ] H) (v : H →ₗ[ℂ] H) (u ψ : H) (M : ℝ)
    (hnorm : HasSum (fun a => ‖K a u‖ ^ 2) (‖u‖ ^ 2))
    (hconn : HasSum (fun a => inner ℂ (K a u) (K' a ψ))
      (Complex.I * inner ℂ u (v ψ)))
    (hmetric : HasSum (fun a => ‖K' a ψ‖ ^ 2) M) :
    HasSum (fun a => ‖K a u - Complex.I • K' a ψ‖ ^ 2)
      (‖u‖ ^ 2 + 2 * (inner ℂ u (v ψ)).re + M) := by
  have hc : HasSum (fun a => (inner ℂ (K a u) (Complex.I • K' a ψ)).re)
      (-(inner ℂ u (v ψ)).re) := by
    have hh := Complex.hasSum_re (hconn.mul_left Complex.I)
    simpa only [inner_smul_right, ← mul_assoc, Complex.I_mul_I,
      neg_one_mul, Complex.neg_re] using hh
  have hs := (hnorm.sub (hc.mul_left 2)).add hmetric
  have he : ∀ a, ‖K a u - Complex.I • K' a ψ‖ ^ 2 =
      ‖K a u‖ ^ 2 - 2 * (inner ℂ (K a u) (Complex.I • K' a ψ)).re +
        ‖K' a ψ‖ ^ 2 := by
    intro a
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp [norm_smul]
  simpa only [he, mul_neg, sub_neg_eq_add] using hs

/-- The countable channel's complex current identity. -/
theorem countable_channel_current {α : Type*}
    (K K' : α → H →ₗ[ℂ] H) (v : H →ₗ[ℂ] H) (u ψ : H)
    (hnorm : HasSum (fun a => inner ℂ (K a ψ) (K a u)) (inner ℂ ψ u))
    (hconn : HasSum (fun a => inner ℂ (K a ψ) (K' a ψ))
      (Complex.I * inner ℂ ψ (v ψ))) :
    HasSum (fun a => inner ℂ (K a ψ) (K a u - Complex.I • K' a ψ))
      (inner ℂ ψ u + inner ℂ ψ (v ψ)) := by
  have hs := hnorm.sub (hconn.mul_left Complex.I)
  simpa only [inner_sub_right, inner_smul_right, ← mul_assoc,
    Complex.I_mul_I, neg_one_mul, sub_neg_eq_add] using hs

/-- All commuting observables are preserved, also for a countable channel. -/
theorem countable_channel_preserves {α : Type*}
    (K : α → H →ₗ[ℂ] H) (W : H →ₗ[ℂ] H) (ψ : H)
    (hnorm : ∀ x y, HasSum (fun a => inner ℂ (K a x) (K a y)) (inner ℂ x y))
    (hW : ∀ a x, W (K a x) = K a (W x)) :
    HasSum (fun a => inner ℂ (K a ψ) (W (K a ψ))) (inner ℂ ψ (W ψ)) := by
  simpa only [hW] using hnorm ψ (W ψ)

/-- Positive trace-class summands converge in trace norm when their traces
sum to one. The trace-class Banach space is abstract here, and the standard
positive-operator identity norm = trace is the only operator-specific input. -/
theorem trace_norm_channel_exists {α T : Type*} [NormedAddCommGroup T]
    [CompleteSpace T] (channel : α → T) (mass : α → ℝ)
    (hmass : HasSum mass 1) (htraceNorm : ∀ a, ‖channel a‖ = mass a) :
    ∃ output : T, HasSum channel output := by
  have hs : Summable (fun a => ‖channel a‖) := by
    simpa only [htraceNorm] using hmass.summable
  exact hs.of_norm

/-- Convert between ordered and unordered sums of a symmetric pair kernel. -/
theorem half_ordered_pair_sum {N : ℕ} (P : Fin N → Fin N → ℝ)
    (hP : ∀ i j, P i j = P j i) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, (if i = j then 0 else P i j) =
      ∑ i, ∑ j, (if i < j then P i j else 0) := by
  have he : ∀ i j : Fin N, (if i = j then (0 : ℝ) else P i j) =
      (if i < j then P i j else 0) + (if j < i then P j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le, hP i j]
  simp_rw [he, Finset.sum_add_distrib]
  have hs : (∑ i : Fin N, ∑ j : Fin N, if j < i then P j i else 0) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then P i j else 0 := by
    rw [Finset.sum_comm]
  rw [hs]
  ring

/-- Each electronic derivative occurs N-1 times in the unordered pairs.
Writing a symmetric pair sum as half of its ordered off-diagonal sum removes
any dependence on the particular enumeration of the electron labels. -/
theorem sum_pair_derivatives {N : ℕ} (d : Fin N → ℝ) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, (if i = j then 0 else d i + d j) =
      (N - 1 : ℝ) * ∑ i, d i := by
  have he : ∀ i j : Fin N,
      (if i = j then (0 : ℝ) else d i + d j) =
        d i + d j - (if i = j then 2 * d i else 0) := by
    intro i j
    split_ifs with h
    · subst j
      ring
    · ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Summing the single-pair estimate gives the factor 2(N-1). -/
theorem pair_hardy_sum {N : ℕ} (d : Fin N → ℝ) (P : Fin N → Fin N → ℝ)
    (hpair : ∀ i j, i ≠ j → P i j ≤ 2 * (d i + d j)) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, (if i = j then 0 else P i j) ≤
      2 * (N - 1 : ℝ) * ∑ i, d i := by
  have hs : (∑ i, ∑ j, (if i = j then 0 else P i j)) ≤
      ∑ i, ∑ j, 2 * (if i = j then 0 else d i + d j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases h : i = j
    · simp [h]
    · simpa [h] using hpair i j h
  simp_rw [← Finset.mul_sum] at hs
  have hc := sum_pair_derivatives d
  linarith

/-- The final Hardy bound uses only nonnegativity of the other PF energies. -/
theorem pair_hardy_energy {N : ℕ} (hN : 1 ≤ N) (d : Fin N → ℝ)
    (P : Fin N → Fin N → ℝ) (E : ℝ)
    (hpair : ∀ i j, i ≠ j → P i j ≤ 2 * (d i + d j))
    (hkin : (∑ i, d i) ≤ 2 * E) :
    (1 / 2 : ℝ) * ∑ i, ∑ j, (if i = j then 0 else P i j) ≤
      4 * (N - 1 : ℝ) * E := by
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) ≤ N - 1 := by linarith
  have hp := pair_hardy_sum d P hpair
  have hm := mul_le_mul_of_nonneg_left hkin (show (0 : ℝ) ≤ 2 * (N - 1 : ℝ) by positivity)
  nlinarith

/-- General repair with the manuscript's exact C_N = 2(N-1)b_N. -/
theorem general_repair_cost {N : ℕ} (E E' J G R P b : ℝ)
    (hb : 0 ≤ b) (hexact : E' = E + J + R / 2)
    (hmetric : R ≤ G + b * P) (hHardy : P ≤ 4 * (N - 1 : ℝ) * E) :
    E' ≤ (1 + 2 * (N - 1 : ℝ) * b) * E + J + G / 2 := by
  have hm := mul_le_mul_of_nonneg_left hHardy hb
  rw [hexact]
  nlinarith

end GptLean.Repair
