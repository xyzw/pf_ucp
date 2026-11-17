import PfHk.CoordinateSobolev

/-! The bounded-coefficient L2 inequality in an arbitrary normed space. -/

noncomputable section
namespace PfHk.ScalarCoefficientNormAlgebra

open MeasureTheory
open scoped ENNReal

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {μ : Measure X}

theorem sum_multiplier {J : Type*} (s : Finset J) (b : J → X → ℝ)
    (u : Lp H 2 μ) (hb : ∀ j ∈ s, MemLp (fun x => b j x • u x) 2 μ) :
    MemLp (fun x => (∑ j ∈ s, b j x) • u x) 2 μ := by
  simpa only [Finset.sum_smul] using memLp_finsetSum s hb

theorem bounded_multiplier (b : X → ℝ) (hb : MemLp b ∞ μ) (u : Lp H 2 μ) :
    ∃ hm : MemLp (fun x => b x • u x) 2 μ,
      ‖hm.toLp (fun x => b x • u x)‖ ^ 2 ≤ (eLpNorm b ∞ μ).toReal ^ 2 * ‖u‖ ^ 2 := by
  have hm : MemLp (fun x => b x • u x) 2 μ := (Lp.memLp u).smul hb
  refine ⟨hm, ?_⟩
  have he := eLpNorm_smul_le_mul_eLpNorm (p := ∞) (q := 2) (r := 2)
    (Lp.aestronglyMeasurable u) hb.aestronglyMeasurable
  have hn : ‖hm.toLp (fun x => b x • u x)‖ ≤ (eLpNorm b ∞ μ).toReal * ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact (ENNReal.toReal_mono
      (ENNReal.mul_ne_top hb.eLpNorm_ne_top (Lp.memLp u).eLpNorm_ne_top) he).trans_eq
      ENNReal.toReal_mul
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (mul_pow _ _ _)

theorem three_endpoint_bound (p r j K T e M : ℝ)
    (hp : p ≤ K * T) (hr : r ≤ K * T) (hj : j ≤ K * T) :
    2 * p + 16 * e ^ 2 * M ^ 2 * r + 4 * e ^ 2 * M ^ 2 * j ≤
      (2 + 20 * e ^ 2 * M ^ 2) * K * T := by
  have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hr' := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 16 * e ^ 2 * M ^ 2)
  have hj' := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ 4 * e ^ 2 * M ^ 2)
  exact (add_le_add (add_le_add hp' hr') hj').trans_eq (by ring)

theorem bessel_half_to_sixth {N : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (n : Fin N) (u v : GptLean.ElectronicH1Space.L2 H (Fin N × Fin 3))
    (h : CoordinateSobolev.BesselPair n (1 / 2) u v) :
    CoordinateSobolev.BesselPair n (3 / 6) u v := by
  rw [show (3 : ℝ) / 6 = 1 / 2 by norm_num]
  exact h

end PfHk.ScalarCoefficientNormAlgebra
