import GptLean.PhotonLocalizationModel
import GptLean.PhotonKernelLocalization

/-!
The cutoff error used by the closure interface is the actual compact
supremum of the two L² field errors and the negative Sobolev field error.
This module connects the compact-uniform cutoff theorem to the Fock form
witnesses. There is no independent assumed scalar error convergence.
-/

namespace GptLean.PhotonLocalization
open Filter Topology MeasureTheory
open scoped InnerProductSpace ENNReal

/-- The two realizations of the same form factor are its L² and negative
Sobolev representatives. The standard Sobolev multiplier theorem supplies
the third strong convergence statement. L² strong convergence is proved
for actual expanding cutoff multipliers in `PhotonKernelLocalization`. -/
structure KernelCutoffFamily (Y L S : Type*) [TopologicalSpace Y]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    [NormedAddCommGroup S] [NormedSpace ℝ S] where
  region : ℕ → Set Y
  compact : ∀ l, IsCompact (region l)
  kernel : Y → L
  sobolevKernel : Y → S
  kernel_cont : ∀ l, ContinuousOn kernel (region l)
  sobolev_cont : ∀ l, ContinuousOn sobolevKernel (region l)
  tail : ℕ → L →L[ℝ] L
  discard : ℕ → L →L[ℝ] L
  negative : ℕ → S →L[ℝ] S
  tailC : ℝ
  discardC : ℝ
  negativeC : ℝ
  tailC_nonneg : 0 ≤ tailC
  discardC_nonneg : 0 ≤ discardC
  negativeC_nonneg : 0 ≤ negativeC
  tail_bound : ∀ m, ‖tail m‖ ≤ tailC
  discard_bound : ∀ m, ‖discard m‖ ≤ discardC
  negative_bound : ∀ m, ‖negative m‖ ≤ negativeC
  tail_zero : ∀ f, Tendsto (fun m => tail m f) atTop (𝓝 0)
  discard_zero : ∀ f, Tendsto (fun m => discard m f) atTop (𝓝 0)
  negative_zero : ∀ f, Tendsto (fun m => negative m f) atTop (𝓝 0)

/-- Build the cutoff family with actual L² multiplication operators.
The negative-Sobolev convergence is derived from a dense core and the
uniform multiplier bound. This is the concrete cutoff entry point. -/
noncomputable def KernelCutoffFamily.ofL2Cutoffs
    {Y Ω E S : Type*} [TopologicalSpace Y] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (region : ℕ → Set Y) (hcompact : ∀ l, IsCompact (region l))
    (kernel : Y → MeasureTheory.Lp E 2 μ) (sobolevKernel : Y → S)
    (hkernel : ∀ l, ContinuousOn kernel (region l))
    (hsobolev : ∀ l, ContinuousOn sobolevKernel (region l))
    (tail discard : ℕ → Ω → ℝ) (radius : Ω → ℝ)
    (htail : ∀ m, MeasureTheory.AEStronglyMeasurable (tail m) μ)
    (hdiscard : ∀ m, MeasureTheory.AEStronglyMeasurable (discard m) μ)
    (htail_bound : ∀ m, ∀ᵐ y ∂μ, |tail m y| ≤ 1)
    (hdiscard_bound : ∀ m, ∀ᵐ y ∂μ, |discard m y| ≤ 1)
    (htail_vanish : ∀ (m : ℕ) y, radius y ≤ m → tail m y = 0)
    (hdiscard_vanish : ∀ (m : ℕ) y, radius y ≤ m → discard m y = 0)
    (negative : ℕ → S →L[ℝ] S) {C : ℝ} (hC : 0 ≤ C)
    (hnegative_bound : ∀ m, ‖negative m‖ ≤ C)
    (core : Set S) (hdense : Dense core)
    (hcore : ∀ f ∈ core, Tendsto (fun m => negative m f) atTop (𝓝 0)) :
    KernelCutoffFamily Y (MeasureTheory.Lp E 2 μ) S where
  region := region
  compact := hcompact
  kernel := kernel
  sobolevKernel := sobolevKernel
  kernel_cont := hkernel
  sobolev_cont := hsobolev
  tail m := PhotonKernelLocalization.l2Multiplier (tail m) (htail m) (htail_bound m)
  discard m := PhotonKernelLocalization.l2Multiplier (discard m) (hdiscard m) (hdiscard_bound m)
  negative := negative
  tailC := 1
  discardC := 1
  negativeC := C
  tailC_nonneg := zero_le_one
  discardC_nonneg := zero_le_one
  negativeC_nonneg := hC
  tail_bound _m := PhotonKernelLocalization.norm_l2Multiplier_le_one _ _ _
  discard_bound _m := PhotonKernelLocalization.norm_l2Multiplier_le_one _ _ _
  negative_bound := hnegative_bound
  tail_zero := PhotonKernelLocalization.l2Multiplier_strong_zero tail radius
    htail htail_bound htail_vanish
  discard_zero := PhotonKernelLocalization.l2Multiplier_strong_zero discard radius
    hdiscard hdiscard_bound hdiscard_vanish
  negative_zero := PhotonKernelLocalization.strong_zero_of_dense negative hC
    hnegative_bound hdense hcore

variable {Y L S : Type*} [TopologicalSpace Y]
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

noncomputable def KernelCutoffFamily.pointError (F : KernelCutoffFamily Y L S)
    (m : ℕ) (x : Y) : ℝ :=
  ‖F.tail m (F.kernel x)‖ + ‖F.negative m (F.sobolevKernel x)‖ +
    ‖F.discard m (F.kernel x)‖

noncomputable def KernelCutoffFamily.error (F : KernelCutoffFamily Y L S)
    (l m : ℕ) : ℝ :=
  PhotonKernelLocalization.kernelError (F.region l) F.pointError m

theorem KernelCutoffFamily.error_bdd (F : KernelCutoffFamily Y L S) (l m : ℕ) :
    BddAbove (F.pointError m '' F.region l) := by
  apply (F.compact l).bddAbove_image
  exact (((F.tail m).continuous.comp_continuousOn (F.kernel_cont l)).norm.add
    ((F.negative m).continuous.comp_continuousOn (F.sobolev_cont l)).norm).add
    ((F.discard m).continuous.comp_continuousOn (F.kernel_cont l)).norm

theorem KernelCutoffFamily.error_nonneg (F : KernelCutoffFamily Y L S) (l m : ℕ) :
    0 ≤ F.error l m :=
  PhotonKernelLocalization.kernelError_nonneg _ _ _ (F.error_bdd l m)

theorem KernelCutoffFamily.error_zero (F : KernelCutoffFamily Y L S) (l : ℕ) :
    Tendsto (F.error l) atTop (𝓝 0) := by
  exact PhotonKernelLocalization.tendsto_three_kernel_error (F.region l) (F.compact l)
    F.kernel F.sobolevKernel F.kernel (F.kernel_cont l) (F.sobolev_cont l)
    (F.kernel_cont l) F.tail F.negative F.discard F.tailC_nonneg F.negativeC_nonneg
    F.discardC_nonneg F.tail_bound F.negative_bound F.discard_bound
    F.tail_zero F.negative_zero F.discard_zero

/-- Every error entering annihilation, CCR, and vacuum variance is bounded
by this same concrete cutoff error. -/
theorem KernelCutoffFamily.component_bounds (F : KernelCutoffFamily Y L S)
    {l m : ℕ} {x : Y} (hx : x ∈ F.region l) :
    ‖F.tail m (F.kernel x)‖ ≤ F.error l m ∧
    ‖F.negative m (F.sobolevKernel x)‖ ≤ F.error l m ∧
    ‖F.discard m (F.kernel x)‖ ≤ F.error l m := by
  have h := PhotonKernelLocalization.le_kernelError (F.region l) F.pointError m
    (F.error_bdd l m) hx
  change ‖F.tail m (F.kernel x)‖ + ‖F.negative m (F.sobolevKernel x)‖ +
    ‖F.discard m (F.kernel x)‖ ≤ F.error l m at h
  have h₁ := norm_nonneg (F.tail m (F.kernel x))
  have h₂ := norm_nonneg (F.negative m (F.sobolevKernel x))
  have h₃ := norm_nonneg (F.discard m (F.kernel x))
  constructor
  · linarith only [h, h₂, h₃]
  constructor
  · linarith only [h, h₁, h₃]
  · linarith only [h, h₁, h₂]

/-- The final closure estimates use the computed kernel error and its
proved limit. Only the form/operator identifications and the separate
coarse compactness inputs are supplied by the physical realization. -/
noncomputable def KernelCutoffFamily.localizationEstimates
    {X Test V H ι : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]
    {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}
    (K : KernelCutoffFamily Y L S) (F : FormData D T V H ι K.error)
    (C : CoarseData D T) : PhotonLoss.LocalizationEstimates D T :=
  F.localizationEstimates C K.error_nonneg K.error_zero

/-- Finite-dimensional compressions with the number, electronic, and
spectral tails needed by the local compactness argument. Rellich and the
trace compression facts supply these inputs. -/
structure CompressionWitness (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] (ω : ℕ → X) where
  spaces : ℕ → ℕ → ℕ → Submodule ℝ X
  finite : ∀ L M s, FiniteDimensional ℝ (spaces L M s)
  compress : ℕ → ℕ → ℕ → ℕ → X
  mem : ∀ L M s n, compress L M s n ∈ spaces L M s
  norm_le : ∀ L M s n, ‖compress L M s n‖ ≤ 1
  numberTail : ℕ → ℕ → ℝ
  electronicTail : ℕ → ℕ → ℝ
  spectralTail : ℕ → ℕ → ℕ → ℕ → ℝ
  compression : ∀ L M s n,
    dist (ω n) (compress L M s n) ≤
      2 * Real.sqrt (2 * numberTail M n + 2 * electronicTail L n +
        2 * spectralTail L M s n)
  Cnum : ℝ
  electronicError : ℕ → ℝ
  energy : ℕ → ℝ
  number_le : ∀ M n, numberTail M n ≤ Cnum / (M + 1)
  electronic_le : ∀ L n, electronicTail L n ≤ electronicError L
  spectral_le : ∀ L M s n, spectralTail L M s n ≤ energy L / (s + 1)
  electronic_zero : Tendsto electronicError atTop (𝓝 0)

theorem CompressionWitness.totallyBounded
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ω : ℕ → X}
    (W : CompressionWitness X ω) : TotallyBounded (Set.range ω) :=
  PhotonKernelLocalization.local_precompactness_of_three_tails ω W.spaces W.finite
    W.compress W.mem W.norm_le W.numberTail W.electronicTail W.spectralTail
    W.compression W.Cnum W.electronicError W.energy W.number_le W.electronic_le
    W.spectral_le W.electronic_zero

/-- The local precompactness field is derived from the actual trace
compressions. The supplied coarse energy bound is independent of the
sharp coefficient-one estimate. -/
noncomputable def CoarseData.ofCompressions
    {X Test : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : PhotonLoss.LocalizationData X} {T : PhotonLoss.TraceData D Test}
    (electronicTight : (ℕ → X) → Prop)
    (witnesses : ∀ (u : ℕ → X) (E : ℝ),
      (∀ n, u n ∈ D.states) → (∀ n, T.energy (u n) ≤ ENNReal.ofReal E) →
      electronicTight u → ∀ m,
        Nonempty (CompressionWitness X (fun n => D.localize m (u n))))
    (rough : ℝ → ℝ)
    (rough_bound : ∀ E m, ∀ x ∈ D.states,
      T.energy x ≤ ENNReal.ofReal E → T.energy (D.localize m x) ≤ ENNReal.ofReal (rough E)) :
    CoarseData D T where
  electronicTight := electronicTight
  precompact u E hu hE htight m := (witnesses u E hu hE htight m).some.totallyBounded
  rough := rough
  rough_bound := rough_bound

end GptLean.PhotonLocalization
