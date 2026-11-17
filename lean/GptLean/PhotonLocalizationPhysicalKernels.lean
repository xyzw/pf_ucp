import GptLean.PhotonLocalizationKernelCutoffs
import GptLean.Gaussian.SpatialField
import GptLean.SymmetricLift.L2Dominated

/-!
The physical form factors and their cutoff errors. The full ultraviolet
kernel is used here, with only its L² and inverse-frequency moments.
Spatial continuity follows by dominated convergence, without bounded
momentum support or differentiability of the ultraviolet cutoff.

Fourier and homogeneous Sobolev realizations remain universal analytic
background. Their multiplier theorem applies to every smooth compactly
supported function at every positive scale. The physical kernel family,
its continuity and its compact-uniform cutoff limit are constructed.
-/

noncomputable section

namespace GptLean.PhotonLocalizationPhysicalKernels

open MeasureTheory Filter Set Topology
open scoped ENNReal InnerProductSpace
open Gaussian PhotonLocalizationKernelCutoffs

section FourierKernels

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The full Fourier form factor, including the physical spatial phase. -/
def momentumKernel (momentum : Ω → FieldSpace) (g : Ω → ℂ)
    (x : FieldSpace) (p : Ω) : ℂ := fieldPhase (momentum p) x * g p

omit [MeasurableSpace Ω] in
theorem norm_momentumKernel (momentum : Ω → FieldSpace) (g : Ω → ℂ)
    (x : FieldSpace) (p : Ω) : ‖momentumKernel momentum g x p‖ = ‖g p‖ := by
  simp [momentumKernel, norm_fieldPhase]

theorem measurable_momentumKernel (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g) (x : FieldSpace) :
    Measurable (momentumKernel momentum g x) := by
  exact ((continuous_fieldPhase.measurable.comp
    (hm.prodMk measurable_const)).mul hg)

theorem momentumKernel_memLp (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) (x : FieldSpace) :
    MemLp (momentumKernel momentum g x) 2 ν := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_momentumKernel momentum hm g hg x).aestronglyMeasurable).2
  simpa only [norm_momentumKernel] using hbase

def momentumKernelL2 (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) (x : FieldSpace) : Lp ℂ 2 ν :=
  (momentumKernel_memLp momentum hm g hg hbase x).toLp (momentumKernel momentum g x)

theorem momentumKernelL2_ae (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) (x : FieldSpace) :
    momentumKernelL2 momentum hm g hg hbase x =ᵐ[ν] momentumKernel momentum g x :=
  MemLp.coeFn_toLp _

theorem continuous_momentumKernelL2 (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) :
    Continuous (momentumKernelL2 momentum hm g hg hbase) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro xn hxn
  apply GptLean.SymmetricLift.tendsto_toLp_two_of_dominated_sq
    (fun n => momentumKernel_memLp momentum hm g hg hbase (xn n))
    (momentumKernel_memLp momentum hm g hg hbase x) hbase
    (fun n => ae_of_all _ fun p => by rw [norm_momentumKernel])
    (ae_of_all _ fun p => by rw [norm_momentumKernel])
  filter_upwards with p
  have hc : Continuous (fun z : FieldSpace => momentumKernel momentum g z p) := by
    unfold momentumKernel fieldPhase
    fun_prop
  exact (hc.tendsto x).comp hxn

theorem momentumKernelL2_norm_sq (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun p => ‖g p‖ ^ 2) ν) (x : FieldSpace) :
    ‖momentumKernelL2 momentum hm g hg hbase x‖ ^ 2 =
      ∫ p, ‖g p‖ ^ 2 ∂ν := by
  rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [momentumKernelL2_ae momentum hm g hg hbase x] with p hp
  rw [hp, norm_momentumKernel]

/-- The inverse square-root frequency is the Fourier coordinate for the
negative homogeneous half-Sobolev norm. -/
def infraredBase (momentum : Ω → FieldSpace) (g : Ω → ℂ) (p : Ω) : ℂ :=
  (Real.sqrt ‖momentum p‖)⁻¹ • g p

omit [MeasurableSpace Ω] in
theorem infraredBase_norm_sq (momentum : Ω → FieldSpace) (g : Ω → ℂ) (p : Ω) :
    ‖infraredBase momentum g p‖ ^ 2 = (1 / ‖momentum p‖) * ‖g p‖ ^ 2 := by
  simp only [infraredBase, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (norm_nonneg _), one_div]

theorem measurable_infraredBase (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (g : Ω → ℂ) (hg : Measurable g) :
    Measurable (infraredBase momentum g) :=
  (hm.norm.sqrt.inv).smul hg

theorem infraredBase_integrable (momentum : Ω → FieldSpace) (g : Ω → ℂ)
    (hIR : Integrable (fun p => (1 / ‖momentum p‖) * ‖g p‖ ^ 2) ν) :
    Integrable (fun p => ‖infraredBase momentum g p‖ ^ 2) ν := by
  simpa only [infraredBase_norm_sq] using hIR

end FourierKernels

section SobolevMultipliers

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Universal homogeneous Sobolev test-function realization and multiplier
theorem. In particular none of these fields mentions a physical kernel,
an electron coordinate, a localization sequence or a source state. -/
structure SobolevMultiplierBackground (S : Type*) [NormedAddCommGroup S]
    [NormedSpace ℝ S] where
  TestFiber : Type*
  [testFiberNorm : NormedAddCommGroup TestFiber]
  [testFiberSpace : NormedSpace ℝ TestFiber]
  tests : Submodule ℝ (FieldSpace → TestFiber)
  compact : ∀ f : tests, HasCompactSupport (f : FieldSpace → TestFiber)
  realize : tests →ₗ[ℝ] S
  dense : Dense (Set.range realize)
  mul_mem : ∀ χ : FieldSpace → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ →
    ∀ f : tests, (fun y => χ y • (f : FieldSpace → TestFiber) y) ∈ tests
  multiplier : (FieldSpace → ℝ) → S →L[ℝ] S
  action : ∀ χ (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (_hc : HasCompactSupport χ) (f : tests),
    multiplier χ (realize f) =
      realize ⟨fun y => χ y • (f : FieldSpace → TestFiber) y, mul_mem χ hχ f⟩
  scaled_bound : ∀ χ : FieldSpace → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ‖multiplier (fun y => χ (R⁻¹ • y))‖ ≤ C

attribute [instance] SobolevMultiplierBackground.testFiberNorm
  SobolevMultiplierBackground.testFiberSpace

theorem retained_compact {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (retained (P := FieldSpace) R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : FieldSpace) (2 * R))
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  have heq := retained_eq_zero (P := FieldSpace) hR
    (y := y) (by linarith)
  exact hy heq

theorem retained_one_compact : HasCompactSupport (retained (P := FieldSpace) 1) :=
  retained_compact zero_lt_one

namespace SobolevMultiplierBackground

variable (B : SobolevMultiplierBackground S)

theorem retained_bound_exists : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
    ‖B.multiplier (retained R)‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := B.scaled_bound (retained 1) (retained_smooth 1) retained_one_compact
  refine ⟨C, hC, fun R hR => ?_⟩
  have heq : (fun y : FieldSpace => retained 1 (R⁻¹ • y)) = retained R := by
    funext y
    simp only [retained, inv_one, one_smul]
  simpa only [heq] using h R hR

def multiplierConstant : ℝ := B.retained_bound_exists.choose

theorem multiplierConstant_nonneg : 0 ≤ B.multiplierConstant :=
  B.retained_bound_exists.choose_spec.1

theorem retained_bound (R : ℝ) (hR : 0 < R) :
    ‖B.multiplier (retained R)‖ ≤ B.multiplierConstant :=
  B.retained_bound_exists.choose_spec.2 R hR

/-- This is multiplication by `1 - retained`, defined on the complete
negative Sobolev space using its universal multiplier realization. -/
def negative (n : ℕ) : S →L[ℝ] S :=
  ContinuousLinearMap.id ℝ S - B.multiplier (retained (radius n))

theorem negative_bound (n : ℕ) : ‖B.negative n‖ ≤ 1 + B.multiplierConstant := by
  exact (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le
    (B.retained_bound (radius n) (radius_pos n)))

theorem negative_core_eventually_zero (f : B.tests) :
    ∀ᶠ n in atTop, B.negative n (B.realize f) = 0 := by
  filter_upwards [tail_smul_eventually_zero (f : FieldSpace → B.TestFiber) (B.compact f)] with n hn
  have heq : (⟨fun y => retained (radius n) y • (f : FieldSpace → B.TestFiber) y,
      B.mul_mem _ (retained_smooth _) f⟩ : B.tests) = f := by
    apply Subtype.ext
    funext y
    have h := congrFun hn y
    change (1 - retained (radius n) y) • (f : FieldSpace → B.TestFiber) y = 0 at h
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm
  change B.realize f - B.multiplier (retained (radius n)) (B.realize f) = 0
  rw [B.action _ (retained_smooth _) (retained_compact (radius_pos n)) f, heq, sub_self]

theorem negative_strong_zero (u : S) :
    Tendsto (fun n => B.negative n u) atTop (𝓝 0) := by
  apply PhotonKernelLocalization.strong_zero_of_dense B.negative
    (by linarith [B.multiplierConstant_nonneg]) B.negative_bound B.dense
  rintro _ ⟨f, rfl⟩
  exact tendsto_const_nhds.congr' ((B.negative_core_eventually_zero f).mono
    fun _ hn => hn.symm)

/-- The energy-coordinate tail is the conjugate of the same negative
Sobolev multiplier, so no additional strong convergence premise occurs. -/
def radiationError {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : V ≃ₗᵢ[ℝ] S) (n : ℕ) (v : V) : V :=
  J.symm (B.negative n (J v))

theorem radiationError_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : V ≃ₗᵢ[ℝ] S) (v : V) :
    Tendsto (fun n => B.radiationError J n v) atTop (𝓝 0) := by
  simpa only [radiationError, Function.comp_def, map_zero] using
    J.symm.continuous.continuousAt.tendsto.comp
    (B.negative_strong_zero (J v))

def radiationFamily {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (J : V ≃ₗᵢ[ℝ] S) (basis : (k : ℕ) → Fin k → V)
    (horth : ∀ k, Orthonormal ℂ (basis k)) : PhotonLocalization.RadiationFamily V :=
  PhotonLocalization.RadiationFamily.ofStrongError basis horth (B.radiationError J)
    (B.radiationError_zero J)

theorem radiationFamily_localized {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (J : V ≃ₗᵢ[ℝ] S) (basis : (k : ℕ) → Fin k → V)
    (horth : ∀ k, Orthonormal ℂ (basis k)) (k n : ℕ) (i : Fin k) :
    (B.radiationFamily J basis horth).localized k n i =
      J.symm (B.multiplier (retained (radius n)) (J (basis k i))) := by
  change basis k i - J.symm (J (basis k i) -
    B.multiplier (retained (radius n)) (J (basis k i))) = _
  rw [map_sub, J.symm_apply_apply]
  abel

end SobolevMultiplierBackground

end SobolevMultipliers

section PhysicalFamily

variable {Ω E S ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι]
  {μ : Measure FieldSpace}

/-- Physical cutoff hypotheses for the finitely many vector components.
The two moments are exactly the ultraviolet L² and infrared field bounds. -/
structure FormFactors (ν : Measure Ω) (ι : Type*) where
  momentum : Ω → FieldSpace
  momentum_measurable : Measurable momentum
  base : ι → Ω → ℂ
  measurable : ∀ i, Measurable (base i)
  ultraviolet : ∀ i, Integrable (fun p => ‖base i p‖ ^ 2) ν
  infrared : ∀ i, Integrable (fun p => (1 / ‖momentum p‖) * ‖base i p‖ ^ 2) ν

namespace FormFactors

variable (F : FormFactors ν ι)

def fourierKernel (z : ι × FieldSpace) : Lp ℂ 2 ν :=
  momentumKernelL2 F.momentum F.momentum_measurable (F.base z.1)
    (F.measurable z.1) (F.ultraviolet z.1) z.2

def weightedFourierKernel (z : ι × FieldSpace) : Lp ℂ 2 ν :=
  momentumKernelL2 F.momentum F.momentum_measurable (infraredBase F.momentum (F.base z.1))
    (measurable_infraredBase F.momentum F.momentum_measurable _ (F.measurable z.1))
    (infraredBase_integrable F.momentum _ (F.infrared z.1)) z.2

omit [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] in
theorem weightedFourierKernel_ae (z : ι × FieldSpace) :
    F.weightedFourierKernel z =ᵐ[ν] fun p =>
      (Real.sqrt ‖F.momentum p‖)⁻¹ • F.fourierKernel z p := by
  filter_upwards [momentumKernelL2_ae F.momentum F.momentum_measurable
    (infraredBase F.momentum (F.base z.1))
    (measurable_infraredBase F.momentum F.momentum_measurable _ (F.measurable z.1))
    (infraredBase_integrable F.momentum _ (F.infrared z.1)) z.2,
    momentumKernelL2_ae F.momentum F.momentum_measurable (F.base z.1)
      (F.measurable z.1) (F.ultraviolet z.1) z.2] with p hp hq
  change (momentumKernelL2 _ _ _ _ _ _ : Ω → ℂ) p = _
  rw [hp]
  change _ = (Real.sqrt ‖F.momentum p‖)⁻¹ •
    (momentumKernelL2 _ _ _ _ _ _ : Ω → ℂ) p
  rw [hq]
  simp only [momentumKernel, infraredBase, mul_smul_comm]

omit [Fintype ι] in
theorem continuous_fourierKernel : Continuous F.fourierKernel := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply continuousAt_prod_of_discrete_left.mpr
  exact (continuous_momentumKernelL2 F.momentum F.momentum_measurable
    (F.base z.1) (F.measurable z.1) (F.ultraviolet z.1)).continuousAt

omit [Fintype ι] in
theorem continuous_weightedFourierKernel : Continuous F.weightedFourierKernel := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply continuousAt_prod_of_discrete_left.mpr
  exact (continuous_momentumKernelL2 F.momentum F.momentum_measurable
    (infraredBase F.momentum (F.base z.1))
    (measurable_infraredBase F.momentum F.momentum_measurable _ (F.measurable z.1))
    (infraredBase_integrable F.momentum _ (F.infrared z.1))).continuousAt

/-- The same full kernel in photon-position L² coordinates. -/
def positionKernel (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ) (z : ι × FieldSpace) : Lp E 2 μ :=
  U (F.fourierKernel z)

/-- The same full kernel in homogeneous negative half-Sobolev coordinates.
`V` is the universal Fourier realization of the weighted L² coordinate. -/
def sobolevKernel (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (z : ι × FieldSpace) : S :=
  V (F.weightedFourierKernel z)

omit [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] in
theorem positionKernel_norm_sq (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ) (z : ι × FieldSpace) :
    ‖F.positionKernel U z‖ ^ 2 = ∫ p, ‖F.base z.1 p‖ ^ 2 ∂ν := by
  rw [positionKernel, U.norm_map]
  exact momentumKernelL2_norm_sq _ _ _ _ _ _

omit [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] in
theorem sobolevKernel_norm_sq (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (z : ι × FieldSpace) :
    ‖F.sobolevKernel V z‖ ^ 2 =
      ∫ p, (1 / ‖F.momentum p‖) * ‖F.base z.1 p‖ ^ 2 ∂ν := by
  rw [sobolevKernel, V.norm_map]
  change ‖momentumKernelL2 _ _ _ _ _ _‖ ^ 2 = _
  rw [momentumKernelL2_norm_sq]
  simp only [infraredBase_norm_sq]

def region (l : ℕ) : Set (ι × FieldSpace) :=
  Set.univ ×ˢ Metric.closedBall 0 (l : ℝ)

omit [DiscreteTopology ι] in
theorem region_compact (l : ℕ) : IsCompact (region (ι := ι) l) :=
  isCompact_univ.prod (isCompact_closedBall _ _)

/-- All family continuity and convergence fields are derived. The input
maps are the universal Fourier realizations, and the multiplier background
is independent of the form factors and the electron region. -/
def cutoffFamily (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S) :
    PhotonLocalization.KernelCutoffFamily (ι × FieldSpace) (Lp E 2 μ) S where
  region := region
  compact := region_compact
  kernel := F.positionKernel U
  sobolevKernel := F.sobolevKernel V
  kernel_cont _ := (U.continuous.comp F.continuous_fourierKernel).continuousOn
  sobolev_cont _ := (V.continuous.comp F.continuous_weightedFourierKernel).continuousOn
  tail := tailOperator
  discard := discardOperator
  negative := B.negative
  tailC := 1
  discardC := 1
  negativeC := 1 + B.multiplierConstant
  tailC_nonneg := zero_le_one
  discardC_nonneg := zero_le_one
  negativeC_nonneg := by linarith [B.multiplierConstant_nonneg]
  tail_bound n := PhotonKernelLocalization.norm_l2Multiplier_le_one _ _ _
  discard_bound n := PhotonKernelLocalization.norm_l2Multiplier_le_one _ _ _
  negative_bound := B.negative_bound
  tail_zero := tailOperator_strong_zero
  discard_zero := discardOperator_strong_zero
  negative_zero := B.negative_strong_zero

theorem cutoff_error_zero (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S) (l : ℕ) :
    Tendsto ((F.cutoffFamily U V B).error l) atTop (𝓝 0) :=
  (F.cutoffFamily U V B).error_zero l

/-- The error components are the actual photon-position cutoff integrals
and the negative Sobolev cutoff norm of the same Fourier form factor. -/
theorem cutoff_pointError_eq (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S)
    (n : ℕ) (z : ι × FieldSpace) :
    (F.cutoffFamily U V B).pointError n z =
      Real.sqrt (∫ y, tail n y ^ 2 * ‖F.positionKernel U z y‖ ^ 2 ∂μ) +
        ‖B.negative n (F.sobolevKernel V z)‖ +
      Real.sqrt (∫ y, discard n y ^ 2 * ‖F.positionKernel U z y‖ ^ 2 ∂μ) := by
  have ht := PhotonKernelLocalization.l2Multiplier_norm_sq (tail n)
    (tail_measurable n) (ae_of_all _ (tail_abs_le_one n)) (F.positionKernel U z)
  have hd := PhotonKernelLocalization.l2Multiplier_norm_sq (discard n)
    (discard_measurable n) (ae_of_all _ (discard_abs_le_one n)) (F.positionKernel U z)
  rw [← ht, ← hd, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem cutoff_component_bounds (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (V : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S)
    {l n : ℕ} {z : ι × FieldSpace} (hz : ‖z.2‖ ≤ l) :
    ‖tailOperator n (F.positionKernel U z)‖ ≤ (F.cutoffFamily U V B).error l n ∧
    ‖B.negative n (F.sobolevKernel V z)‖ ≤ (F.cutoffFamily U V B).error l n ∧
    ‖discardOperator n (F.positionKernel U z)‖ ≤ (F.cutoffFamily U V B).error l n := by
  apply (F.cutoffFamily U V B).component_bounds
  exact ⟨Set.mem_univ _, by simpa [Metric.mem_closedBall, dist_zero_right] using hz⟩

end FormFactors

end PhysicalFamily

end GptLean.PhotonLocalizationPhysicalKernels
