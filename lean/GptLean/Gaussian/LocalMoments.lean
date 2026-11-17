import GptLean.RemovalEstimates

/-!
Integration and scaling in Step 3 of exact soft removal. The standard
Sobolev estimate on each ball and derivative field moment bounds are
explicit local inputs. Integrability of the conditional Z² moment and its
uniform κ² bound are conclusions, not assumed here.
-/

namespace GptLean.Gaussian

open MeasureTheory Filter
open GptLean.RemovalEstimates

variable {Q ι : Type*} [MeasurableSpace Q] {μ : Measure Q} [Fintype ι]

theorem integrated_scaled_sobolev
    (ord : ι → ℕ) {F : Q → ℝ} (M : ι → Q → ℝ)
    {C R k B : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 ≤ B)
    (hkR0 : 0 ≤ k * R) (hkR1 : k * R ≤ 1)
    (hFm : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ u ∂μ, 0 ≤ F u)
    (hM : ∀ i, Integrable (M i) μ)
    (hSob : ∀ᵐ u ∂μ, F u ≤ C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) * M i u)
    (hMom : ∀ i, ∫ u, M i u ∂μ ≤ R ^ (3 : ℤ) * k ^ (2 * ord i + 2) * B) :
    Integrable F μ ∧ ∫ u, F u ∂μ ≤ C * (Fintype.card ι : ℝ) * k ^ 2 * B := by
  let major : Q → ℝ := fun u => C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) * M i u
  have hterms : ∀ i, Integrable (fun u => R ^ (2 * (ord i : ℤ) - 3) * M i u) μ :=
    fun i => (hM i).const_mul _
  have hmajor : Integrable major μ :=
    (integrable_finsetSum Finset.univ (fun i _ => hterms i)).const_mul C
  have hFi : Integrable F μ := hmajor.mono' hFm (by
    filter_upwards [hF0, hSob] with u hu hs
    simpa only [Real.norm_of_nonneg hu] using hs)
  refine ⟨hFi, ?_⟩
  have hterm_bound (i : ι) :
      R ^ (2 * (ord i : ℤ) - 3) * (∫ u, M i u ∂μ) ≤ k ^ 2 * B := by
    calc
      _ ≤ R ^ (2 * (ord i : ℤ) - 3) *
          (R ^ (3 : ℤ) * k ^ (2 * ord i + 2) * B) :=
        mul_le_mul_of_nonneg_left (hMom i) (zpow_nonneg hR.le _)
      _ = (k * R) ^ (2 * ord i) * k ^ 2 * B := by
        rw [← mul_assoc, ← mul_assoc, rescaling_identity hR.ne' (ord i)]
      _ ≤ k ^ 2 * B := mul_le_mul_of_nonneg_right (rescaling_le hkR0 hkR1 (ord i)) hB
  calc
    ∫ u, F u ∂μ ≤ ∫ u, major u ∂μ := integral_mono_ae hFi hmajor hSob
    _ = C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) * (∫ u, M i u ∂μ) := by
      rw [show major = (fun u => C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) * M i u) from rfl,
        integral_const_mul, integral_finsetSum _ (fun i _ => hterms i)]
      simp only [integral_const_mul]
    _ ≤ C * ∑ _i : ι, k ^ 2 * B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm_bound i)) hC
    _ = C * (Fintype.card ι : ℝ) * k ^ 2 * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The integrated first moment follows from the proved second-moment
estimate and the actual integral Cauchy–Schwarz theorem. -/
theorem first_moment_from_scaled_sobolev
    (ord : ι → ℕ) (M : ι → Q → ℝ) {p Z : Q → ℝ}
    {C R k B : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 ≤ B)
    (hkR0 : 0 ≤ k * R) (hkR1 : k * R ≤ 1)
    (hp : ∀ u, 0 ≤ p u) (hZ : ∀ u, 0 ≤ Z u)
    (hpm : AEStronglyMeasurable p μ) (hZm : AEStronglyMeasurable Z μ)
    (hpi : Integrable p μ) (hM : ∀ i, Integrable (M i) μ)
    (hSob : ∀ᵐ u ∂μ, p u * Z u ^ 2 ≤
      C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) * M i u)
    (hMom : ∀ i, ∫ u, M i u ∂μ ≤ R ^ (3 : ℤ) * k ^ (2 * ord i + 2) * B) :
    Integrable (fun u => p u * Z u ^ 2) μ ∧
    ∫ u, p u * Z u ^ 2 ∂μ ≤ C * (Fintype.card ι : ℝ) * k ^ 2 * B ∧
    ∫ u, p u * Z u ∂μ ≤
      Real.sqrt (∫ u, p u ∂μ) * Real.sqrt (C * (Fintype.card ι : ℝ) * k ^ 2 * B) := by
  have hpow : AEStronglyMeasurable (fun u => Z u ^ 2) μ := by
    convert hZm.mul hZm using 1
    ext u
    simp [pow_two]
  obtain ⟨hsecond, hsecondbound⟩ := integrated_scaled_sobolev ord M hC hR hB hkR0 hkR1
    (hpm.mul hpow) (Eventually.of_forall (fun u => mul_nonneg (hp u) (sq_nonneg _)))
    hM hSob hMom
  refine ⟨hsecond, hsecondbound, ?_⟩
  exact (integral_mul_le_sqrt_mul_sqrt hp hZ hpm hZm hpi hsecond).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsecondbound) (Real.sqrt_nonneg _))

/-- Weighted L¹ integrability is a consequence of finite zeroth and second
moments, so the first-moment integral cannot silently default to zero. -/
theorem weighted_first_moment_integrable {p Z : Q → ℝ}
    (hp : ∀ u, 0 ≤ p u) (hZ : ∀ u, 0 ≤ Z u)
    (hpm : AEStronglyMeasurable p μ) (hZm : AEStronglyMeasurable Z μ)
    (hpi : Integrable p μ) (hsecond : Integrable (fun u => p u * Z u ^ 2) μ) :
    Integrable (fun u => p u * Z u) μ := by
  apply (hpi.add hsecond).mono' (hpm.mul hZm)
  filter_upwards with u
  change ‖p u * Z u‖ ≤ p u + p u * Z u ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (hp u) (hZ u))]
  have hs := mul_nonneg (hp u) (sq_nonneg (Z u - 1))
  have hz2 := mul_nonneg (hp u) (sq_nonneg (Z u))
  nlinarith

/-- The local remainder is integrated before applying the moment bound.
Both its integrability and the quantitative repair cost are conclusions. -/
theorem integrated_repair_cost_from_moments {p Z rem : Q → ℝ}
    {C₀ CZ e R k B : ℝ} (hC₀ : 0 ≤ C₀) (hCZ : 0 ≤ CZ)
    (he : 0 ≤ e) (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hp : ∀ u, 0 ≤ p u) (hZ : ∀ u, 0 ≤ Z u)
    (hpm : AEStronglyMeasurable p μ) (hZm : AEStronglyMeasurable Z μ)
    (hpi : Integrable p μ) (hsecond : Integrable (fun u => p u * Z u ^ 2) μ)
    (hsecondbound : ∫ u, p u * Z u ^ 2 ∂μ ≤ CZ * k ^ 2 * B)
    (hrm : AEStronglyMeasurable rem μ) (hr0 : ∀ᵐ u ∂μ, 0 ≤ rem u)
    (hr : ∀ᵐ u ∂μ, rem u ≤
      C₀ * (e ^ 2 * R ^ 2 * (p u * Z u ^ 2) + e * (p u * Z u))) :
    Integrable rem μ ∧
    ∫ u, rem u ∂μ ≤ C₀ * max CZ (Real.sqrt CZ) * e ^ 2 * k ^ 2 * R ^ 2 * B +
      C₀ * max CZ (Real.sqrt CZ) * e * k * Real.sqrt ((∫ u, p u ∂μ) * B) := by
  have hfirst := weighted_first_moment_integrable hp hZ hpm hZm hpi hsecond
  have hmajor := ((hsecond.const_mul (e ^ 2 * R ^ 2)).add (hfirst.const_mul e)).const_mul C₀
  have hri : Integrable rem μ := hmajor.mono' hrm (by
    filter_upwards [hr0, hr] with u h0 hu
    change ‖rem u‖ ≤ C₀ * (e ^ 2 * R ^ 2 * (p u * Z u ^ 2) + e * (p u * Z u))
    simpa only [Real.norm_of_nonneg h0] using hu)
  refine ⟨hri, ?_⟩
  have hrem : ∫ u, rem u ∂μ ≤
      C₀ * (e ^ 2 * R ^ 2 * (∫ u, p u * Z u ^ 2 ∂μ) + e * (∫ u, p u * Z u ∂μ)) := by
    calc
      _ ≤ ∫ u, C₀ * (e ^ 2 * R ^ 2 * (p u * Z u ^ 2) + e * (p u * Z u)) ∂μ :=
        integral_mono_ae hri hmajor hr
      _ = _ := by
        rw [integral_const_mul, integral_add (hsecond.const_mul _) (hfirst.const_mul _),
          integral_const_mul, integral_const_mul]
  exact rem_le_of_moments hC₀ hCZ he hk (integral_nonneg hp) hB hrem hsecondbound
    (integral_mul_le_sqrt_mul_sqrt hp hZ hpm hZm hpi hsecond)

end GptLean.Gaussian
