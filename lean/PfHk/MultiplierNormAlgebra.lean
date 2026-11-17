import GptLean.Repair.TraceChannel

/-! Generic Hilbert-space norm algebra used before specialization to the
physical Fock space. -/

noncomputable section
namespace PfHk.MultiplierNormAlgebra

open MeasureTheory GptLean
open scoped ENNReal

theorem weighted_norm_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c a b : ℝ) (f d v : H) (h : ‖f‖ ≤ a * ‖d‖ + b * ‖v‖) :
    ‖c • f‖ ≤ a * ‖c • d‖ + b * ‖c • v‖ := by
  simp only [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |c| * (a * ‖d‖ + b * ‖v‖) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

theorem two_term_square {s a b d v : ℝ} (hs : 0 ≤ s)
    (h : s ≤ a * d + b * v) : s ^ 2 ≤ 2 * a ^ 2 * d ^ 2 + 2 * b ^ 2 * v ^ 2 := by
  have ht := pow_le_pow_left₀ hs h 2
  nlinarith [sq_nonneg (a * d - b * v)]

theorem complex_difference_square {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : ℝ) (p f : H) :
    ‖(-Complex.I) • p - (e : ℂ) • f‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * e ^ 2 * ‖f‖ ^ 2 := by
  have ht := norm_sub_le ((-Complex.I) • p) ((e : ℂ) • f)
  simp only [norm_smul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs] at ht
  have hs := two_term_square (norm_nonneg ((-Complex.I) • p - (e : ℂ) • f))
    (show ‖(-Complex.I) • p - (e : ℂ) • f‖ ≤ 1 * ‖p‖ + |e| * ‖f‖ by simpa using ht)
  simpa only [one_pow, mul_one, sq_abs] using hs

theorem real_smul_complex_sub {H : Type*} [AddCommGroup H] [Module ℝ H] [Module ℂ H]
    [SMulCommClass ℝ ℂ H] (b e : ℝ) (p f : H) :
    b • ((-Complex.I) • p - (e : ℂ) • f) =
      (-Complex.I) • (b • p) - (e : ℂ) • (b • f) := by
  rw [smul_sub, smul_comm b (-Complex.I), smul_comm b (e : ℂ)]

theorem l2_square_bound {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X)
    (f d v : Lp H 2 μ) (A B : ℝ)
    (hp : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ A * ‖d x‖ ^ 2 + B * ‖v x‖ ^ 2) :
    ‖f‖ ^ 2 ≤ A * ‖d‖ ^ 2 + B * ‖v‖ ^ 2 := by
  have hn (w : Lp H 2 μ) : ‖w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂μ := by
    simpa only [Lp.toLp_coeFn] using Repair.toL2_norm_sq (Lp.memLp w)
  have hd := (Lp.memLp d).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hv := (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [hn f, hn d, hn v, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hd.const_mul A) (hv.const_mul B)]
  exact integral_mono_ae ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    ((hd.const_mul A).add (hv.const_mul B)) hp

end PfHk.MultiplierNormAlgebra
