import GptLean.PhotonCompactness
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Isometry

/-!
Concrete cutoff tails and the compact-uniform kernel step in photon localization.

The integral theorem proves decay of the actual squared L² cutoff error.
The operator theorems pass convergence from a dense core to the whole space
and then uniformly over compact families of kernels. Thus the compact-uniform
error is a conclusion, rather than an assumed localization estimate.

For the negative homogeneous Sobolev norm the standard Sobolev inputs are
the boundedness of smooth rescaled multiplication and the density of compactly
supported smooth functions. The representation of these multipliers on a
concrete homogeneous Sobolev completion remains an explicit interface.
-/

namespace GptLean.PhotonKernelLocalization

open MeasureTheory Filter Set Topology

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Dominated convergence for an actual cutoff error integral. This applies
both to `1 - θ_R` and to the discarded multiplier `φ_R`. -/
theorem tendsto_cutoff_integral
    (χ : ℕ → Ω → ℝ) (w : Ω → ℝ)
    (hχ : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hw : Integrable w μ) (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y)
    (hχbound : ∀ n, ∀ᵐ y ∂μ, |χ n y| ≤ 1)
    (hχzero : ∀ᵐ y ∂μ, Tendsto (fun n => χ n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, (χ n y) ^ 2 * w y ∂μ) atTop (𝓝 0) := by
  have hdom : ∀ n, ∀ᵐ y ∂μ, ‖(χ n y) ^ 2 * w y‖ ≤ w y := by
    intro n
    filter_upwards [hχbound n, hw0] with y hy hy0
    have hs : (χ n y) ^ 2 ≤ 1 := by
      simpa only [sq_abs] using pow_le_one₀ (abs_nonneg (χ n y)) hy (n := 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hy0)]
    exact (mul_le_mul_of_nonneg_right hs hy0).trans_eq (one_mul _)
  have hlim : ∀ᵐ y ∂μ,
      Tendsto (fun n => (χ n y) ^ 2 * w y) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hχzero] with y hy
    simpa using (hy.pow 2).mul_const (w y)
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n y => (χ n y) ^ 2 * w y) (f := fun _ => (0 : ℝ)) w
    (fun n => ((hχ n).pow 2).mul hw.aestronglyMeasurable) hw hdom hlim
  simpa using h

omit [MeasurableSpace Ω] in
/-- Cutoffs which vanish on an increasing exhaustion have zero pointwise limit. -/
theorem cutoff_tendsto_zero_of_exhaustion
    (χ : ℕ → Ω → ℝ) (radius : Ω → ℝ)
    (hvanish : ∀ (n : ℕ) y, radius y ≤ n → χ n y = 0) (y : Ω) :
    Tendsto (fun n => χ n y) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (radius y)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hvanish n y (hN.trans (by exact_mod_cast hn))).symm

/-- The L² norm of either exterior cutoff tends to zero. The radius can
be `‖y‖` on photon position space, including the polarization variable. -/
theorem tendsto_cutoff_l2_error
    (χ : ℕ → Ω → ℝ) (w radius : Ω → ℝ)
    (hχ : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hw : Integrable w μ) (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y)
    (hχbound : ∀ n, ∀ᵐ y ∂μ, |χ n y| ≤ 1)
    (hvanish : ∀ (n : ℕ) y, radius y ≤ n → χ n y = 0) :
    Tendsto (fun n => Real.sqrt (∫ y, (χ n y) ^ 2 * w y ∂μ))
      atTop (𝓝 0) := by
  have h := tendsto_cutoff_integral χ w hχ hw hw0 hχbound
    (ae_of_all _ (cutoff_tendsto_zero_of_exhaustion χ radius hvanish))
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h

end Integral

section Hardy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The geometric estimate behind the localized photon number bound. -/
theorem cutoff_sq_le_inverse_radius {θ r R : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsupport : 2 * R < r → θ = 0) : θ ^ 2 ≤ 2 * R / r := by
  by_cases h : 2 * R < r
  · rw [hsupport h]
    simpa using div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.le) hr.le
  · have hs := pow_le_one₀ hθ0 hθ1 (n := 2)
    exact hs.trans ((le_div_iff₀ hr).2 (by linarith))

/-- The first one-photon estimate is derived from the standard fractional
Hardy inequality applied to `w = ‖u‖²`. All displayed integrals are actual
Bochner integrals. No localized number estimate is assumed. -/
theorem localized_mass_le_hardy
    (θ w radius : Ω → ℝ) {R CH energy : ℝ}
    (hR : 0 < R) (hθ : AEStronglyMeasurable θ μ)
    (hw : Integrable w μ) (hw0 : ∀ᵐ y ∂μ, 0 ≤ w y)
    (hθ0 : ∀ᵐ y ∂μ, 0 ≤ θ y) (hθ1 : ∀ᵐ y ∂μ, θ y ≤ 1)
    (hradius : ∀ᵐ y ∂μ, 0 < radius y)
    (hsupport : ∀ᵐ y ∂μ, 2 * R < radius y → θ y = 0)
    (hweighted : Integrable (fun y => w y / radius y) μ)
    (hHardy : (∫ y, w y / radius y ∂μ) ≤ CH * energy) :
    (∫ y, θ y ^ 2 * w y ∂μ) ≤ 2 * CH * R * energy := by
  have hdom : ∀ᵐ y ∂μ, ‖θ y ^ 2 * w y‖ ≤ w y := by
    filter_upwards [hw0, hθ0, hθ1] with y hy hy0 hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hy)]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hy0 hy1 (n := 2)) hy).trans_eq (one_mul _)
  have hloc : Integrable (fun y => θ y ^ 2 * w y) μ :=
    hw.mono' ((hθ.pow 2).mul hw.aestronglyMeasurable) hdom
  have hle : (∫ y, θ y ^ 2 * w y ∂μ) ≤
      ∫ y, (2 * R) * (w y / radius y) ∂μ := by
    apply integral_mono_ae hloc (hweighted.const_mul (2 * R))
    filter_upwards [hw0, hθ0, hθ1, hradius, hsupport] with y hy hy0 hy1 hyr hys
    have hp := mul_le_mul_of_nonneg_right
      (cutoff_sq_le_inverse_radius hR hyr hy0 hy1 hys) hy
    convert hp using 1 <;> ring
  rw [integral_const_mul] at hle
  calc (∫ y, θ y ^ 2 * w y ∂μ)
      ≤ 2 * R * (∫ y, w y / radius y ∂μ) := hle
    _ ≤ 2 * R * (CH * energy) := mul_le_mul_of_nonneg_left hHardy (by positivity)
    _ = 2 * CH * R * energy := by ring

end Hardy

section ConcreteL2

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem multiplier_memLp (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ y ∂μ, |χ y| ≤ 1)
    (u : Lp E 2 μ) : MemLp (fun y => χ y • u y) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := 1) (hχ.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hbound] with y hy
  simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs, one_mul] using
    mul_le_mul_of_nonneg_right hy (norm_nonneg (u y))

/-- Actual multiplication by a measurable contraction on the photon L² space. -/
noncomputable def l2Multiplier (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ y ∂μ, |χ y| ≤ 1) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (multiplier_memLp χ hχ hbound u).toLp (fun y => χ y • u y)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound (u + v)),
          MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound u),
          MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound v),
          Lp.coeFn_add u v,
          Lp.coeFn_add ((multiplier_memLp χ hχ hbound u).toLp _)
            ((multiplier_memLp χ hχ hbound v).toLp _)] with y h₁ h₂ h₃ h₄ h₅
        simp only [h₁, h₅, h₄, Pi.add_apply, h₂, h₃, smul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound (c • u)),
          MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound u),
          Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((multiplier_memLp χ hχ hbound u).toLp _)]
          with y h₁ h₂ h₃ h₄
        simp only [h₁, h₄, h₃, h₂, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
    1 (by
      intro u
      change ‖(multiplier_memLp χ hχ hbound u).toLp (fun y => χ y • u y)‖ ≤ 1 * ‖u‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound u), hbound] with y hy hb
      rw [hy, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

theorem l2Multiplier_apply_ae (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ y ∂μ, |χ y| ≤ 1)
    (u : Lp E 2 μ) : l2Multiplier χ hχ hbound u =ᵐ[μ] fun y => χ y • u y :=
  MemLp.coeFn_toLp (multiplier_memLp χ hχ hbound u)

theorem norm_l2Multiplier_le_one (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ y ∂μ, |χ y| ≤ 1) :
    ‖l2Multiplier (E := E) χ hχ hbound‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [l2Multiplier_apply_ae χ hχ hbound u, hbound] with y hy hb
  rw [hy, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem l2_norm_sq_eq_integral (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ y, ‖u y‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The abstract norm is identified with the actual cutoff error integral. -/
theorem l2Multiplier_norm_sq (χ : Ω → ℝ)
    (hχ : AEStronglyMeasurable χ μ) (hbound : ∀ᵐ y ∂μ, |χ y| ≤ 1)
    (u : Lp E 2 μ) :
    ‖l2Multiplier χ hχ hbound u‖ ^ 2 = ∫ y, χ y ^ 2 * ‖u y‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [l2Multiplier_apply_ae χ hχ hbound u] with y hy
  rw [hy, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Strong L² convergence of the concrete exterior multipliers. -/
theorem l2Multiplier_strong_zero (χ : ℕ → Ω → ℝ) (radius : Ω → ℝ)
    (hχ : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hbound : ∀ n, ∀ᵐ y ∂μ, |χ n y| ≤ 1)
    (hvanish : ∀ (n : ℕ) y, radius y ≤ n → χ n y = 0) (u : Lp E 2 μ) :
    Tendsto (fun n => l2Multiplier (χ n) (hχ n) (hbound n) u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_cutoff_l2_error χ (fun y => ‖u y‖ ^ 2) radius hχ
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u))
    (ae_of_all _ fun y => sq_nonneg _) hbound hvanish
  convert h using 1
  ext n
  rw [← l2Multiplier_norm_sq (χ n) (hχ n) (hbound n) u, Real.sqrt_sq (norm_nonneg _)]

end ConcreteL2

section Operators

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Strong convergence of uniformly bounded operators follows from convergence
on any dense core. The compact support core of a smooth cutoff is one instance. -/
theorem strong_zero_of_dense
    (T : ℕ → H →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖T n‖ ≤ C) {D : Set H} (hD : Dense D)
    (hcore : ∀ v ∈ D, Tendsto (fun n => T n v) atTop (𝓝 0)) (u : H) :
    Tendsto (fun n => T n u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, hvD, hv⟩ := hD.exists_dist_lt u (show 0 < ε / (2 * (C + 1)) by positivity)
  have hc := (hcore v hvD).norm
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hv' : C * ‖u - v‖ < ε / 2 := by
    have hdist : ‖u - v‖ < ε / (2 * (C + 1)) := by
      simpa [dist_eq_norm, norm_sub_rev] using hv
    have hh := (mul_lt_mul_of_pos_left hdist (show 0 < C + 1 by positivity))
    have heq : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by field_simp
    rw [heq] at hh
    nlinarith [norm_nonneg (u - v)]
  have hnv : ‖T n v‖ < ε / 2 := by simpa using hN n hn
  have hnu : ‖T n u‖ ≤ C * ‖u - v‖ + ‖T n v‖ := by
    calc ‖T n u‖ = ‖T n (u - v) + T n v‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖T n (u - v)‖ + ‖T n v‖ := norm_add_le _ _
      _ ≤ C * ‖u - v‖ + ‖T n v‖ := by
        gcongr
        exact (T n).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  simpa using (hnu.trans_lt (by linarith : C * ‖u - v‖ + ‖T n v‖ < ε))

/-- The key compactness step for the form factors. Pointwise convergence of
bounded multipliers is uniform on every compact family of kernels. -/
theorem compact_uniform_zero
    (T : ℕ → H →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖T n‖ ≤ C)
    (hstrong : ∀ u, Tendsto (fun n => T n u) atTop (𝓝 0))
    {K : Set H} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u ∈ K, ‖T n u‖ < ε := by
  obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded
    (ε / (2 * (C + 1))) (by positivity)
  have hall : ∀ᶠ n in atTop, ∀ v ∈ s, ‖T n v‖ < ε / 2 := by
    apply (eventually_all_finite hs).2
    intro v hv
    exact (hstrong v).norm.eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hall] with n hn u hu
  obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.1 (hcover hu)
  have huv' : ‖u - v‖ < ε / (2 * (C + 1)) := by simpa [Metric.mem_ball, dist_eq_norm] using huv
  have hh := mul_lt_mul_of_pos_left huv' (show 0 < C + 1 by positivity)
  have heq : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by field_simp
  rw [heq] at hh
  have hsmall : C * ‖u - v‖ < ε / 2 := by nlinarith [norm_nonneg (u - v)]
  calc ‖T n u‖ = ‖T n (u - v) + T n v‖ := by rw [map_sub, sub_add_cancel]
    _ ≤ ‖T n (u - v)‖ + ‖T n v‖ := norm_add_le _ _
    _ ≤ C * ‖u - v‖ + ‖T n v‖ := by
      gcongr
      exact (T n).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
    _ < ε := by linarith [hn v hv]

/-- A continuous family of kernels over a compact electronic region inherits
uniform error decay. Finite polarization labels may be included in `X`. -/
theorem continuous_kernel_uniform_zero
    {X : Type*} [TopologicalSpace X]
    (G : X → H) {K : Set X} (hK : IsCompact K) (hG : ContinuousOn G K)
    (T : ℕ → H →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖T n‖ ≤ C)
    (hstrong : ∀ u, Tendsto (fun n => T n u) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖T n (G x)‖ < ε := by
  filter_upwards [compact_uniform_zero T hC hbound hstrong (hK.image_of_continuousOn hG) hε]
    with n hn x hx
  exact hn _ ⟨x, hx, rfl⟩

end Operators

section ConcreteKernelTails

/-- Compact-uniform decay for the actual L² multiplication operators.
The only analytic hypotheses are continuity of the family of form factors,
the contraction bound, and vanishing on the expanding position balls. -/
theorem l2_kernel_uniform_zero
    {Ω E X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]
    (G : X → Lp E 2 μ) {K : Set X} (hK : IsCompact K) (hG : ContinuousOn G K)
    (χ : ℕ → Ω → ℝ) (radius : Ω → ℝ)
    (hχ : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hbound : ∀ n, ∀ᵐ y ∂μ, |χ n y| ≤ 1)
    (hvanish : ∀ (n : ℕ) y, radius y ≤ n → χ n y = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖l2Multiplier (χ n) (hχ n) (hbound n) (G x)‖ < ε :=
  continuous_kernel_uniform_zero G hK hG _ zero_le_one
    (fun n => norm_l2Multiplier_le_one (χ n) (hχ n) (hbound n))
    (l2Multiplier_strong_zero χ radius hχ hbound hvanish) hε

end ConcreteKernelTails

section UniformError

variable {X : Type*} [TopologicalSpace X] (K : Set X)

/-- A nonnegative version of the supremum used for `ε_L(R)`. Inserting zero
also handles an empty parameter region without an arbitrary supremum value. -/
noncomputable def kernelError (e : ℕ → X → ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (e n '' K))

omit [TopologicalSpace X] in
theorem kernelError_nonneg (e : ℕ → X → ℝ) (n : ℕ)
    (hb : BddAbove (e n '' K)) : 0 ≤ kernelError K e n :=
  le_csSup (hb.insert 0) (mem_insert _ _)

omit [TopologicalSpace X] in
theorem le_kernelError (e : ℕ → X → ℝ) (n : ℕ)
    (hb : BddAbove (e n '' K)) {x : X} (hx : x ∈ K) :
    e n x ≤ kernelError K e n :=
  le_csSup (hb.insert 0) (mem_insert_of_mem _ (mem_image_of_mem _ hx))

/-- Uniform decay gives decay of the precise supremum error. -/
theorem tendsto_kernelError (e : ℕ → X → ℝ)
    (hb : ∀ n, BddAbove (e n '' K))
    (hsmall : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, e n x < ε) :
    Tendsto (kernelError K e) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hsmall (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  have hu : kernelError K e n ≤ ε / 2 := by
    apply csSup_le (insert_nonempty _ _)
    intro z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact (half_pos hε).le
    · exact (hN n hn x hx).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (kernelError_nonneg K e n (hb n))]
  exact hu.trans_lt (half_lt_self hε)

/-- This is the compact-uniform form factor error in the manuscript, with
three possibly different Hilbert/Sobolev realization spaces. The three
strong convergence statements may be obtained by the integral or dense
core theorems above. -/
theorem tendsto_three_kernel_error
    {H₁ H₂ H₃ F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    [NormedAddCommGroup H₃] [NormedSpace ℝ H₃]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (hK : IsCompact K)
    (G₁ : X → H₁) (G₂ : X → H₂) (G₃ : X → H₃)
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K) (hG₃ : ContinuousOn G₃ K)
    (T₁ : ℕ → H₁ →L[ℝ] F₁) (T₂ : ℕ → H₂ →L[ℝ] F₂) (T₃ : ℕ → H₃ →L[ℝ] F₃)
    {C₁ C₂ C₃ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hb₁ : ∀ n, ‖T₁ n‖ ≤ C₁) (hb₂ : ∀ n, ‖T₂ n‖ ≤ C₂) (hb₃ : ∀ n, ‖T₃ n‖ ≤ C₃)
    (hs₁ : ∀ u, Tendsto (fun n => T₁ n u) atTop (𝓝 0))
    (hs₂ : ∀ u, Tendsto (fun n => T₂ n u) atTop (𝓝 0))
    (hs₃ : ∀ u, Tendsto (fun n => T₃ n u) atTop (𝓝 0)) :
    Tendsto (kernelError K (fun n x =>
      ‖T₁ n (G₁ x)‖ + ‖T₂ n (G₂ x)‖ + ‖T₃ n (G₃ x)‖)) atTop (𝓝 0) := by
  apply tendsto_kernelError
  · intro n
    apply hK.bddAbove_image
    exact (((T₁ n).continuous.comp_continuousOn hG₁).norm.add
      ((T₂ n).continuous.comp_continuousOn hG₂).norm).add
      ((T₃ n).continuous.comp_continuousOn hG₃).norm
  · intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    filter_upwards [continuous_kernel_uniform_zero G₁ hK hG₁ T₁ hC₁ hb₁ hs₁ hε3,
      continuous_kernel_uniform_zero G₂ hK hG₂ T₂ hC₂ hb₂ hs₂ hε3,
      continuous_kernel_uniform_zero G₃ hK hG₃ T₃ hC₃ hb₃ hs₃ hε3]
      with n h₁ h₂ h₃ x hx
    linarith [h₁ x hx, h₂ x hx, h₃ x hx]

end UniformError

section LocalCompactness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Bounded finite-rank compressions form a totally bounded family. Here the
subspace is the finite-dimensional corner of the trace-class space. -/
theorem finite_dimensional_compressions_totallyBounded
    (S : Submodule ℝ X) [FiniteDimensional ℝ S]
    (v : ℕ → X) (hmem : ∀ n, v n ∈ S) (hbound : ∀ n, ‖v n‖ ≤ 1) :
    TotallyBounded (Set.range v) := by
  have hc : IsCompact (((↑) : S → X) '' Metric.closedBall (0 : S) 1) :=
    (isCompact_closedBall (0 : S) 1).image continuous_subtype_val
  apply hc.totallyBounded.subset
  rintro _ ⟨n, rfl⟩
  refine ⟨⟨v n, hmem n⟩, ?_, rfl⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hbound n

/-- The three errors are photon-number truncation, the electronic spatial
tail, and a spectral tail in the bounded configuration region. The latter
has the standard spectral Markov bound `energy(L)/(s+1)` after Rellich.

This theorem derives local trace precompactness. Its hypotheses contain no
precompactness assertion. Finite dimensionality of each spectral corner,
the trace compression estimate, and the scalar tail estimates suffice.
The order of choices is number cutoff, electronic radius, spectral cutoff. -/
theorem local_precompactness_of_three_tails
    (ω : ℕ → X)
    (spaces : ℕ → ℕ → ℕ → Submodule ℝ X)
    (hfinite : ∀ L M s, FiniteDimensional ℝ (spaces L M s))
    (compress : ℕ → ℕ → ℕ → ℕ → X)
    (hmem : ∀ L M s n, compress L M s n ∈ spaces L M s)
    (hbound : ∀ L M s n, ‖compress L M s n‖ ≤ 1)
    (numberTail electronicTail : ℕ → ℕ → ℝ)
    (spectralTail : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hcompression : ∀ L M s n,
      dist (ω n) (compress L M s n) ≤
        2 * Real.sqrt (2 * numberTail M n + 2 * electronicTail L n +
          2 * spectralTail L M s n))
    (Cnum : ℝ) (electronicError energy : ℕ → ℝ)
    (hnum : ∀ M n, numberTail M n ≤ Cnum / (M + 1))
    (hel : ∀ L n, electronicTail L n ≤ electronicError L)
    (hspec : ∀ L M s n, spectralTail L M s n ≤ energy L / (s + 1))
    (htight : Tendsto electronicError atTop (𝓝 0)) :
    TotallyBounded (Set.range ω) := by
  apply GptLean.PhotonLoss.totallyBounded_range_of_approx
  intro ε hε
  let δ : ℝ := (ε / 6) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (Cnum / δ)
  have hnumδ : Cnum / (M + 1) < δ := by
    rw [div_lt_iff₀ hδ] at hM
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < M + 1)]
    nlinarith
  obtain ⟨L, hL⟩ := (htight.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨s, hs⟩ := exists_nat_gt (energy L / δ)
  have hspecδ : energy L / (s + 1) < δ := by
    rw [div_lt_iff₀ hδ] at hs
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < s + 1)]
    nlinarith
  letI := hfinite L M s
  refine ⟨Set.range (compress L M s),
    finite_dimensional_compressions_totallyBounded (spaces L M s) _
      (hmem L M s) (hbound L M s), fun n =>
        ⟨compress L M s n, Set.mem_range_self n, ?_⟩⟩
  apply (hcompression L M s n).trans
  have hroot : Real.sqrt (2 * numberTail M n + 2 * electronicTail L n +
      2 * spectralTail L M s n) ≤ ε / 2 := by
    rw [Real.sqrt_le_left (half_pos hε).le]
    have h₁ := (hnum M n).trans hnumδ.le
    have h₂ := (hel L n).trans hL.le
    have h₃ := (hspec L M s n).trans hspecδ.le
    dsimp [δ] at h₁ h₂ h₃
    nlinarith [sq_nonneg ε]
  linarith

end LocalCompactness

end GptLean.PhotonKernelLocalization
