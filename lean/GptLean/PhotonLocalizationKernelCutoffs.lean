import GptLean.PhotonLocalizationKernelModel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Actual smooth photon-position cutoffs.

A single smooth bump, composed with sine and cosine, supplies the square
partition required for one-photon localization. Its rescalings have the
prescribed inner and outer radii. The two exterior errors are actual L²
multipliers, with their contractivity and compact-uniform convergence
proved from these formulas.

The negative homogeneous Sobolev realization and its uniform multiplier
bound remain standard analytic inputs. No L² cutoff, cutoff bound, or
cutoff convergence hypothesis is needed in the constructor below.
-/

namespace GptLean.PhotonLocalizationKernelCutoffs

open MeasureTheory Filter Set Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Fixed smooth bump with inner radius one and outer radius two. -/
noncomputable def baseBump : ContDiffBump (0 : P) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The retained cutoff. Using a trigonometric square partition also makes
the discarded cutoff smooth at the ends of the transition region. -/
noncomputable def retained (R : ℝ) (y : P) : ℝ :=
  Real.sin (Real.pi / 2 * (baseBump (P := P)) (R⁻¹ • y))

/-- The complementary, discarded cutoff. -/
noncomputable def discarded (R : ℝ) (y : P) : ℝ :=
  Real.cos (Real.pi / 2 * (baseBump (P := P)) (R⁻¹ • y))

private theorem angle_bounds (R : ℝ) (y : P) :
    0 ≤ Real.pi / 2 * (baseBump (P := P)) (R⁻¹ • y) ∧
      Real.pi / 2 * (baseBump (P := P)) (R⁻¹ • y) ≤ Real.pi / 2 := by
  constructor
  · exact mul_nonneg (by positivity) (baseBump (P := P)).nonneg
  · exact (mul_le_mul_of_nonneg_left (baseBump (P := P)).le_one (by positivity)).trans_eq
      (mul_one _)

theorem retained_nonneg (R : ℝ) (y : P) : 0 ≤ retained R y := by
  exact Real.sin_nonneg_of_nonneg_of_le_pi (angle_bounds R y).1
    ((angle_bounds R y).2.trans (by linarith [Real.pi_pos]))

theorem retained_le_one (R : ℝ) (y : P) : retained R y ≤ 1 :=
  Real.sin_le_one _

theorem discarded_nonneg (R : ℝ) (y : P) : 0 ≤ discarded R y := by
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [(angle_bounds R y).1, Real.pi_pos]) (angle_bounds R y).2

theorem discarded_le_one (R : ℝ) (y : P) : discarded R y ≤ 1 :=
  Real.cos_le_one _

theorem square_partition (R : ℝ) (y : P) :
    retained R y ^ 2 + discarded R y ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

theorem retained_smooth (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (retained (P := P) R) :=
  ((contDiff_const.mul ((baseBump (P := P)).contDiff.comp
    (contDiff_const.smul contDiff_id))).sin)

theorem discarded_smooth (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (discarded (P := P) R) :=
  ((contDiff_const.mul ((baseBump (P := P)).contDiff.comp
    (contDiff_const.smul contDiff_id))).cos)

private theorem scaled_norm {R : ℝ} (hR : 0 < R) (y : P) :
    ‖R⁻¹ • y‖ = ‖y‖ / R := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  ring

theorem retained_eq_one {R : ℝ} (hR : 0 < R) {y : P} (hy : ‖y‖ ≤ R) :
    retained R y = 1 := by
  have hb : (baseBump (P := P)) (R⁻¹ • y) = 1 := by
    apply (baseBump (P := P)).one_of_mem_closedBall
    change dist (R⁻¹ • y) 0 ≤ 1
    rw [dist_zero_right, scaled_norm hR, div_le_one hR]
    exact hy
  simp [retained, hb]

theorem discarded_eq_zero {R : ℝ} (hR : 0 < R) {y : P} (hy : ‖y‖ ≤ R) :
    discarded R y = 0 := by
  have hb : (baseBump (P := P)) (R⁻¹ • y) = 1 := by
    apply (baseBump (P := P)).one_of_mem_closedBall
    change dist (R⁻¹ • y) 0 ≤ 1
    rw [dist_zero_right, scaled_norm hR, div_le_one hR]
    exact hy
  simp [discarded, hb]

theorem retained_eq_zero {R : ℝ} (hR : 0 < R) {y : P} (hy : 2 * R ≤ ‖y‖) :
    retained R y = 0 := by
  have hb : (baseBump (P := P)) (R⁻¹ • y) = 0 := by
    apply (baseBump (P := P)).zero_of_le_dist
    change 2 ≤ dist (R⁻¹ • y) 0
    rw [dist_zero_right, scaled_norm hR, le_div_iff₀ hR]
    exact hy
  simp [retained, hb]

theorem discarded_eq_one {R : ℝ} (hR : 0 < R) {y : P} (hy : 2 * R ≤ ‖y‖) :
    discarded R y = 1 := by
  have hb : (baseBump (P := P)) (R⁻¹ • y) = 0 := by
    apply (baseBump (P := P)).zero_of_le_dist
    change 2 ≤ dist (R⁻¹ • y) 0
    rw [dist_zero_right, scaled_norm hR, le_div_iff₀ hR]
    exact hy
  simp [discarded, hb]

/-- A larger cutoff is exactly one throughout the support of the smaller
cutoff. This is the one-photon absorption identity used by nested channels. -/
theorem retained_absorption {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hRS : 2 * R ≤ S) (y : P) : retained R y * retained S y = retained R y := by
  by_cases hy : ‖y‖ ≤ S
  · rw [retained_eq_one hS hy, mul_one]
  · rw [retained_eq_zero hR (hRS.trans (le_of_not_ge hy)), zero_mul]

/-- The manuscript's successive radii provide exact absorption. Strict
ordering is necessary because a smooth cutoff is not an idempotent. -/
theorem retained_absorption_geometric {m l : ℕ} (hml : m < l) (y : P) :
    retained ((3 : ℝ) ^ (m + 1)) y * retained ((3 : ℝ) ^ (l + 1)) y =
      retained ((3 : ℝ) ^ (m + 1)) y := by
  apply retained_absorption (by positivity) (by positivity)
  calc 2 * (3 : ℝ) ^ (m + 1) ≤ 3 * (3 : ℝ) ^ (m + 1) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (3 : ℝ) ^ (m + 2) := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (3 : ℝ) ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The geometrically separated radii used by the localization channels. -/
def radius (n : ℕ) : ℝ := (3 : ℝ) ^ (n + 1)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

theorem le_radius (n : ℕ) : (n : ℝ) ≤ radius n := by
  have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) (n + 1)
  norm_num only [Nat.cast_add, Nat.cast_one, show (1 : ℝ) + 2 = 3 by norm_num] at h
  unfold radius
  nlinarith [show (0 : ℝ) ≤ n by positivity]

/-- The retained field error at the geometric localization radius. -/
noncomputable def tail (n : ℕ) (y : P) : ℝ :=
  1 - retained (radius n) y

/-- The discarded vacuum error at the same radius. -/
noncomputable def discard (n : ℕ) (y : P) : ℝ :=
  discarded (radius n) y

theorem tail_abs_le_one (n : ℕ) (y : P) : |tail n y| ≤ 1 := by
  rw [tail, abs_of_nonneg (sub_nonneg.mpr (retained_le_one _ _))]
  linarith [retained_nonneg (radius n) y]

theorem discard_abs_le_one (n : ℕ) (y : P) : |discard n y| ≤ 1 := by
  rw [discard, abs_of_nonneg (discarded_nonneg _ _)]
  exact discarded_le_one _ _

theorem tail_vanish (n : ℕ) (y : P) (hy : ‖y‖ ≤ n) : tail n y = 0 := by
  rw [tail, retained_eq_one (radius_pos n) (hy.trans (le_radius n))]
  exact sub_self _

theorem discard_vanish (n : ℕ) (y : P) (hy : ‖y‖ ≤ n) : discard n y = 0 := by
  exact discarded_eq_zero (radius_pos n) (hy.trans (le_radius n))

/-- Multiplication by the exterior error is eventually identically zero
on every compactly supported function, before taking any Sobolev norm. -/
theorem tail_smul_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : P → E) (hf : HasCompactSupport f) :
    ∀ᶠ n in atTop, (fun y => tail n y • f y) = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop N] with n hn
  funext y
  by_cases hy : f y = 0
  · simp [hy]
  · have hyr : ‖y‖ ≤ n := (hR y (subset_tsupport f (by simpa using hy))).trans
      (hN.trans (by exact_mod_cast hn))
    simp [tail_vanish n y hyr]

/-- The negative-Sobolev strong limit follows from the actual compact
support action. Only the dense realization map and its bounded multiplier
intertwining remain to be supplied by the Sobolev construction. -/
theorem negative_strong_zero_of_compact_core
    {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (realize : (P → E) → S) (hzero : realize 0 = 0)
    (core : Set (P → E)) (hcompact : ∀ f ∈ core, HasCompactSupport f)
    (hdense : Dense (realize '' core))
    (negative : ℕ → S →L[ℝ] S) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖negative n‖ ≤ C)
    (hact : ∀ n f, f ∈ core →
      negative n (realize f) = realize (fun y => tail n y • f y)) (u : S) :
    Tendsto (fun n => negative n u) atTop (𝓝 0) := by
  apply PhotonKernelLocalization.strong_zero_of_dense negative hC hbound hdense
  rintro v ⟨f, hf, rfl⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [tail_smul_eventually_zero f (hcompact f hf)] with n hn
  rw [hact n f hf, hn, hzero]

section Measurable

variable [MeasurableSpace P] [BorelSpace P]
  {μ : Measure P} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem retained_measurable (R : ℝ) : AEStronglyMeasurable (retained (P := P) R) μ :=
  (retained_smooth R).continuous.aestronglyMeasurable

theorem discarded_measurable (R : ℝ) : AEStronglyMeasurable (discarded (P := P) R) μ :=
  (discarded_smooth R).continuous.aestronglyMeasurable

omit [MeasurableSpace P] [BorelSpace P] in
theorem retained_abs_le_one (R : ℝ) (y : P) : |retained R y| ≤ 1 := by
  rw [abs_of_nonneg (retained_nonneg _ _)]
  exact retained_le_one _ _

omit [MeasurableSpace P] [BorelSpace P] in
theorem discarded_abs_le_one (R : ℝ) (y : P) : |discarded R y| ≤ 1 := by
  rw [abs_of_nonneg (discarded_nonneg _ _)]
  exact discarded_le_one _ _

/-- The retained multiplier at an arbitrary radius. -/
noncomputable def retainedOperator (R : ℝ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  PhotonKernelLocalization.l2Multiplier (retained R) (retained_measurable R)
    (ae_of_all _ (retained_abs_le_one R))

/-- The discarded multiplier at an arbitrary radius. -/
noncomputable def discardedOperator (R : ℝ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  PhotonKernelLocalization.l2Multiplier (discarded R) (discarded_measurable R)
    (ae_of_all _ (discarded_abs_le_one R))

/-- The concrete square partition gives the one-photon dilation's norm
identity, without assuming a localization isometry. -/
theorem square_partition_l2 (R : ℝ) (u : Lp E 2 μ) :
    ‖retainedOperator R u‖ ^ 2 + ‖discardedOperator R u‖ ^ 2 = ‖u‖ ^ 2 := by
  have hi (v : Lp E 2 μ) : Integrable (fun y => ‖v y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    PhotonKernelLocalization.l2_norm_sq_eq_integral,
    ← integral_add (hi _) (hi _)]
  apply integral_congr_ae
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained R) (retained_measurable R) (ae_of_all _ (retained_abs_le_one R)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded R) (discarded_measurable R) (ae_of_all _ (discarded_abs_le_one R)) u]
    with y h₁ h₂
  rw [show retainedOperator R u y = retained R y • u y from h₁,
    show discardedOperator R u y = discarded R y • u y from h₂]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← add_mul, square_partition, one_mul]

/-- The actual one-photon localization map into the Hilbert direct sum.
It is the map to be second-quantized in the Fock dilation. -/
noncomputable def onePhotonIsometry (R : ℝ) :
    Lp E 2 μ →ₗᵢ[ℝ] WithLp 2 (Lp E 2 μ × Lp E 2 μ) where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (Lp E 2 μ × Lp E 2 μ)).symm.toLinearMap.comp
    ((retainedOperator R).toLinearMap.prod (discardedOperator R).toLinearMap)
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact square_partition_l2 R u

theorem onePhotonIsometry_apply (R : ℝ) (u : Lp E 2 μ) :
    onePhotonIsometry R u = WithLp.toLp 2 (retainedOperator R u, discardedOperator R u) := rfl

section Complex

variable [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [BorelSpace P] in
/-- The real-valued cutoff commutes with complex scalars on actual L²
representatives. This upgrades the dilation to the complex photon space. -/
theorem multiplier_map_complex_smul (χ : P → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1)
    (c : ℂ) (u : Lp E 2 μ) :
    PhotonKernelLocalization.l2Multiplier χ hχ hb (c • u) =
      c • PhotonKernelLocalization.l2Multiplier χ hχ hb u := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae χ hχ hb (c • u),
    PhotonKernelLocalization.l2Multiplier_apply_ae χ hχ hb u,
    Lp.coeFn_smul c u,
    Lp.coeFn_smul c (PhotonKernelLocalization.l2Multiplier χ hχ hb u)]
    with y h₁ h₂ h₃ h₄
  simp only [h₁, h₄, h₃, Pi.smul_apply, h₂]
  exact smul_comm _ _ _

/-- Complex-linear version of the concrete one-photon dilation. -/
noncomputable def complexOnePhotonIsometry (R : ℝ) :
    Lp E 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp E 2 μ × Lp E 2 μ) where
  toFun := onePhotonIsometry R
  map_add' := (onePhotonIsometry R).map_add
  map_smul' c u := by
    apply (WithLp.equiv 2 _).injective
    change (retainedOperator R (c • u), discardedOperator R (c • u)) =
      (c • retainedOperator R u, c • discardedOperator R u)
    apply Prod.ext
    · exact multiplier_map_complex_smul _ _ _ _ _
    · exact multiplier_map_complex_smul _ _ _ _ _
  norm_map' := (onePhotonIsometry R).norm_map

end Complex

/-- Actual operator absorption follows from the pointwise cutoff identity. -/
theorem retainedOperator_absorption {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hRS : 2 * R ≤ S) (u : Lp E 2 μ) :
    retainedOperator R (retainedOperator S u) = retainedOperator R u := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained R) (retained_measurable R) (ae_of_all _ (retained_abs_le_one R))
      (retainedOperator S u),
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained S) (retained_measurable S) (ae_of_all _ (retained_abs_le_one S)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained R) (retained_measurable R) (ae_of_all _ (retained_abs_le_one R)) u]
    with y h₁ h₂ h₃
  rw [show retainedOperator R (retainedOperator S u) y =
      retained R y • retainedOperator S u y from h₁,
    show retainedOperator S u y = retained S y • u y from h₂,
    show retainedOperator R u y = retained R y • u y from h₃,
    smul_smul, retained_absorption hR hS hRS]

/-- The concrete retained multiplier satisfies the one-photon number
estimate using the standard fractional Hardy inequality. -/
theorem retainedOperator_mass_le_hardy (u : Lp E 2 μ) {R CH energy : ℝ}
    (hR : 0 < R) (hradius : ∀ᵐ y ∂μ, 0 < ‖y‖)
    (hweighted : Integrable (fun y => ‖u y‖ ^ 2 / ‖y‖) μ)
    (hHardy : (∫ y, ‖u y‖ ^ 2 / ‖y‖ ∂μ) ≤ CH * energy) :
    ‖retainedOperator R u‖ ^ 2 ≤ 2 * CH * R * energy := by
  rw [retainedOperator, PhotonKernelLocalization.l2Multiplier_norm_sq]
  apply PhotonKernelLocalization.localized_mass_le_hardy (retained R)
    (fun y => ‖u y‖ ^ 2) (fun y => ‖y‖) hR (retained_measurable R)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u))
    (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ (retained_nonneg R))
    (ae_of_all _ (retained_le_one R)) hradius
    (ae_of_all _ fun y hy => retained_eq_zero hR hy.le) hweighted hHardy

theorem tail_measurable (n : ℕ) : AEStronglyMeasurable (tail (P := P) n) μ :=
  (continuous_const.sub (retained_smooth (radius n)).continuous).aestronglyMeasurable

theorem discard_measurable (n : ℕ) : AEStronglyMeasurable (discard (P := P) n) μ :=
  (discarded_smooth (radius n)).continuous.aestronglyMeasurable

/-- Actual tail multiplication on the one-photon Hilbert space. -/
noncomputable def tailOperator (n : ℕ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  PhotonKernelLocalization.l2Multiplier (tail n) (tail_measurable n)
    (ae_of_all _ (tail_abs_le_one n))

/-- Actual discarded-mode multiplication on the one-photon Hilbert space. -/
noncomputable def discardOperator (n : ℕ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  PhotonKernelLocalization.l2Multiplier (discard n) (discard_measurable n)
    (ae_of_all _ (discard_abs_le_one n))

theorem tailOperator_strong_zero (u : Lp E 2 μ) :
    Tendsto (fun n => tailOperator n u) atTop (𝓝 0) :=
  PhotonKernelLocalization.l2Multiplier_strong_zero tail (fun y : P => ‖y‖)
    tail_measurable (fun n => ae_of_all _ (tail_abs_le_one n)) tail_vanish u

theorem discardOperator_strong_zero (u : Lp E 2 μ) :
    Tendsto (fun n => discardOperator n u) atTop (𝓝 0) :=
  PhotonKernelLocalization.l2Multiplier_strong_zero discard (fun y : P => ‖y‖)
    discard_measurable (fun n => ae_of_all _ (discard_abs_le_one n)) discard_vanish u

/-- Supply the closure interface with this fixed smooth cutoff family.
Its only remaining Sobolev inputs are a dense compact-support realization,
the multiplier action on that realization, and the uniform operator bound.
All three strong limits and hence the compact kernel error are derived. -/
noncomputable def kernelCutoffFamily
    {Y S : Type*} [TopologicalSpace Y] [NormedAddCommGroup S] [NormedSpace ℝ S]
    (region : ℕ → Set Y) (hcompact : ∀ l, IsCompact (region l))
    (kernel : Y → Lp E 2 μ) (sobolevKernel : Y → S)
    (hkernel : ∀ l, ContinuousOn kernel (region l))
    (hsobolev : ∀ l, ContinuousOn sobolevKernel (region l))
    (realize : (P → E) → S) (hzero : realize 0 = 0)
    (core : Set (P → E)) (hcore : ∀ f ∈ core, HasCompactSupport f)
    (hdense : Dense (realize '' core))
    (negative : ℕ → S →L[ℝ] S) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖negative n‖ ≤ C)
    (hact : ∀ n f, f ∈ core →
      negative n (realize f) = realize (fun y => tail n y • f y)) :
    PhotonLocalization.KernelCutoffFamily Y (Lp E 2 μ) S :=
  PhotonLocalization.KernelCutoffFamily.ofL2Cutoffs μ region hcompact kernel sobolevKernel
    hkernel hsobolev tail discard (fun y : P => ‖y‖) tail_measurable discard_measurable
    (fun n => ae_of_all _ (tail_abs_le_one n))
    (fun n => ae_of_all _ (discard_abs_le_one n)) tail_vanish discard_vanish
    negative hC hbound (realize '' core) hdense
    (fun f _ => negative_strong_zero_of_compact_core realize hzero core hcore hdense
      negative hC hbound hact f)

end Measurable

end GptLean.PhotonLocalizationKernelCutoffs
