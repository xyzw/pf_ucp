import GptLean.SymmetricLift

/-! Gluing identities when chart hypotheses hold only on their own domains. -/
noncomputable section
namespace GptLean.SymmetricLift
open WithLp
open scoped BigOperators
variable {H K ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Fintype ι]

theorem glue_inner_supported (P : H →ₗ[ℂ] H) (χ : ι → ℝ)
    (V : ι → H →ₗ[ℂ] K) (active : ι → Prop)
    (horth : ∀ u v, inner ℂ (P u) (v - P v) = 0)
    (hpartition : ∑ a, χ a ^ 2 = 1)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hiso : ∀ a, active a → ∀ u v, inner ℂ (V a u) (V a v) = inner ℂ u v)
    (u v : H) : inner ℂ (glue P χ V u) (glue P χ V v) = inner ℂ u v := by
  have hc : ∑ a, (χ a : ℂ) ^ 2 = 1 := by exact_mod_cast hpartition
  have hi (a : ι) :
      inner ℂ ((χ a : ℂ) • V a (u - P u)) ((χ a : ℂ) • V a (v - P v)) =
        (χ a : ℂ) ^ 2 * inner ℂ (u - P u) (v - P v) := by
    by_cases ha : active a
    · simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hiso a ha]
      ring
    · simp [hzero a ha]
  simp only [glue, WithLp.prod_inner_apply, PiLp.inner_apply, hi]
  rw [← Finset.sum_mul, hc, one_mul]
  exact projection_split_inner P horth u v

theorem glue_flat_supported (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K) (active : ι → Prop)
    (hpartition : ∑ a, χ a * dχ a = 0)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hiso : ∀ a, active a → ∀ u v, inner ℂ (V a u) (V a v) = inner ℂ u v)
    (hflat : ∀ a, active a → ∀ u v, inner ℂ (V a u) (dV a v) = 0)
    (u v : H) : inner ℂ (glue P χ V u) (glueDerivative P χ dχ V dV v) = 0 := by
  have hc : ∑ a, (χ a : ℂ) * (dχ a : ℂ) = 0 := by exact_mod_cast hpartition
  have hi (a : ι) : inner ℂ ((χ a : ℂ) • V a (u - P u))
      ((dχ a : ℂ) • V a (v - P v) + (χ a : ℂ) • dV a (v - P v)) =
        ((χ a : ℂ) * (dχ a : ℂ)) * inner ℂ (u - P u) (v - P v) := by
    by_cases ha : active a
    · simp only [inner_smul_left, inner_add_right, inner_smul_right,
        Complex.conj_ofReal, hiso a ha, hflat a ha, mul_zero, add_zero]
      ring
    · simp [hzero a ha]
  simp only [glue, glueDerivative, WithLp.prod_inner_apply, PiLp.inner_apply,
    inner_zero_right, zero_add, hi]
  rw [← Finset.sum_mul, hc, zero_mul]

theorem glue_metric_supported (P : H →ₗ[ℂ] H) (χ dχ : ι → ℝ)
    (V dV : ι → H →ₗ[ℂ] K) (active : ι → Prop)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hdzero : ∀ a, ¬ active a → dχ a = 0)
    (hiso : ∀ a, active a → ∀ u, ‖V a u‖ = ‖u‖)
    (hflat : ∀ a, active a → ∀ u v, inner ℂ (V a u) (dV a v) = 0)
    (hfixed : ∀ a, active a → ∀ u, dV a (P u) = 0) (u : H) :
    ‖glueDerivative P χ dχ V dV u‖ ^ 2 =
      (∑ a, dχ a ^ 2) * ‖u - P u‖ ^ 2 + ∑ a, χ a ^ 2 * ‖dV a u‖ ^ 2 := by
  have hi (a : ι) :
      ‖(dχ a : ℂ) • V a (u - P u) + (χ a : ℂ) • dV a (u - P u)‖ ^ 2 =
        dχ a ^ 2 * ‖u - P u‖ ^ 2 + χ a ^ 2 * ‖dV a u‖ ^ 2 := by
    by_cases ha : active a
    · rw [scaled_orthogonal_norm _ _ _ _ (hflat a ha _ _), hiso a ha,
        derivative_on_remainder P _ (hfixed a ha)]
    · simp [hzero a ha, hdzero a ha]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [glueDerivative, WithLp.fst, WithLp.snd, ofLp_toLp, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add, PiLp.norm_sq_eq_of_L2, hi]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

theorem glue_equivariant_supported (P R : H →ₗ[ℂ] H) (χ χ' : ι → ℝ)
    (V V' : ι → H →ₗ[ℂ] K) (active : ι → Prop) (hχ : χ' = χ)
    (hPR : ∀ u, P (R u) = P u) (hRP : ∀ u, R (P u) = P u)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hV : ∀ a, active a → ∀ u, V' a (R u) = V a u) (u : H) :
    glue P χ' V' (R u) = glue P χ V u := by
  subst χ'
  have hrem : R u - P u = R (u - P u) := by simp [hRP]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · exact hPR u
  · apply (WithLp.ext_iff 2).mpr
    funext a
    by_cases ha : active a
    · simp only [glue, WithLp.ofLp_toLp, hPR, hrem, hV a ha]
    · simp [glue, hzero a ha]

end GptLean.SymmetricLift
