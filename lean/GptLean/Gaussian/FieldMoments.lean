import GptLean.Gaussian.WienerSegal
import GptLean.Gaussian.LocalMoments
import GptLean.PhotonLocalization
import GptLean.CutoffProfile
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
Local field moments for exact soft removal. The kernels below contain the
actual Fourier phase, sharp soft cutoff and derivative momentum factors.
Their weighted norms, the field relative bound, and WIS intertwining give
the conditional moments. Fubini and the scaled spatial Sobolev estimate
then give the local supremum moment.

The standard Fock creation/annihilation identities, the jointly measurable
Gaussian field representatives and the spatial Sobolev estimate are explicit
inputs. Labels remain in a real commuting family. No simultaneous real
multiplication representation of all complex one-photon kernels is postulated.
-/

namespace GptLean.Gaussian

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

abbrev FieldSpace := EuclideanSpace ℝ (Fin 3)

/-- The multiplier for an ordered list of spatial derivatives. -/
def derivativeFactor : List (Fin 3) → FieldSpace → ℂ
  | [], _ => 1
  | j :: ds, p => (-Complex.I * (p j : ℂ)) * derivativeFactor ds p

theorem norm_derivativeFactor_le (ds : List (Fin 3)) {p : FieldSpace} {k : ℝ}
    (hk : 0 ≤ k) (hp : ‖p‖ ≤ k) : ‖derivativeFactor ds p‖ ≤ k ^ ds.length := by
  induction ds with
  | nil => simp [derivativeFactor]
  | cons j ds ih =>
      have hj : ‖p j‖ ≤ k := (PiLp.norm_apply_le p j).trans hp
      simpa [derivativeFactor, norm_mul, pow_succ, mul_comm] using
        mul_le_mul hj ih (norm_nonneg _) hk

/-- The phase has modulus one at every spatial point. -/
def fieldPhase (p x : FieldSpace) : ℂ :=
  Complex.exp (((-inner ℝ p x : ℝ) : ℂ) * Complex.I)

theorem norm_fieldPhase (p x : FieldSpace) : ‖fieldPhase p x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The unphased soft part of a one-photon form factor. -/
def softBase {Ω : Type*} (momentum : Ω → FieldSpace) (k : ℝ) (g : Ω → ℂ)
    (y : Ω) : ℂ := if ‖momentum y‖ < k then g y else 0

/-- The original cutoff integrability assumptions imply integrability of
the sharp soft kernel. -/
theorem softBase_weighted_integrable {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (k : ℝ) (g : Ω → ℂ) (w : Ω → ℝ)
    (hi : Integrable (fun y => w y * ‖g y‖ ^ 2) ν) :
    Integrable (fun y => w y * ‖softBase momentum k g y‖ ^ 2) ν := by
  have heq : (fun y => w y * ‖softBase momentum k g y‖ ^ 2) =
      {y | ‖momentum y‖ < k}.indicator (fun y => w y * ‖g y‖ ^ 2) := by
    ext y
    by_cases hy : ‖momentum y‖ < k <;> simp [softBase, Set.indicator, hy]
  rw [heq]
  exact hi.indicator (hm.norm measurableSet_Iio)

/-- The zeroth kernel moment is exactly the integral on the soft sublevel set. -/
theorem softBase_weighted_integral {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (k : ℝ) (g : Ω → ℂ) (w : Ω → ℝ) :
    (∫ y, w y * ‖softBase momentum k g y‖ ^ 2 ∂ν) =
      ∫ y in {y | ‖momentum y‖ < k}, w y * ‖g y‖ ^ 2 ∂ν := by
  have hs : MeasurableSet {y | ‖momentum y‖ < k} := hm.norm measurableSet_Iio
  calc
    _ = ∫ y, {y | ‖momentum y‖ < k}.indicator (fun y => w y * ‖g y‖ ^ 2) y ∂ν := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : ‖momentum y‖ < k <;> simp [softBase, Set.indicator, hy]
    _ = _ := integral_indicator hs

/-- Identification with the actual cutoff moments. The integrability
assumptions are the untruncated ultraviolet and infrared kernel conditions. -/
theorem softBase_cutoff_moments {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (k : ℝ) (g : Ω → ℂ)
    (hB : Integrable (fun y => ‖g y‖ ^ 2) ν)
    (hA : Integrable (fun y => (1 / ‖momentum y‖) * ‖g y‖ ^ 2) ν) :
    Integrable (fun y => ‖softBase momentum k g y‖ ^ 2) ν ∧
    Integrable (fun y => (1 / ‖momentum y‖) * ‖softBase momentum k g y‖ ^ 2) ν ∧
    (∫ y, ‖softBase momentum k g y‖ ^ 2 ∂ν) =
      GptLean.CutoffProfile.bsq ν (fun y => ‖momentum y‖)
        (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) k ∧
    (∫ y, (1 / ‖momentum y‖) * ‖softBase momentum k g y‖ ^ 2 ∂ν) =
      GptLean.CutoffProfile.asq ν (fun y => ‖momentum y‖)
        (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) k := by
  have hiB := softBase_weighted_integrable momentum hm k g (fun _ => 1)
    (by simpa using hB)
  have hiA := softBase_weighted_integrable momentum hm k g (fun y => 1 / ‖momentum y‖) hA
  refine ⟨by simpa using hiB, hiA, ?_, ?_⟩
  · have heq := softBase_weighted_integral (ν := ν) momentum hm k g (fun _ => 1)
    simp only [one_mul] at heq
    rw [heq]
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun y => sq_nonneg ‖g y‖)) hB.aestronglyMeasurable.restrict
  · rw [softBase_weighted_integral momentum hm]
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun y => mul_nonneg (by positivity) (sq_nonneg ‖g y‖)))
      hA.aestronglyMeasurable.restrict]
    unfold GptLean.CutoffProfile.asq
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / ‖momentum y‖)]
    exact mul_comm _ _

/-- The explicit derivative of the soft Fourier form factor. -/
def softDerivativeKernel {Ω : Type*} (momentum : Ω → FieldSpace)
    (ds : List (Fin 3)) (k : ℝ) (x : FieldSpace) (g : Ω → ℂ) (y : Ω) : ℂ :=
  derivativeFactor ds (momentum y) * fieldPhase (momentum y) x *
    softBase momentum k g y

/-- The undifferentiated soft kernel norm is exactly independent of position. -/
theorem norm_softDerivativeKernel_nil {Ω : Type*} (momentum : Ω → FieldSpace)
    (k : ℝ) (x : FieldSpace) (g : Ω → ℂ) (y : Ω) :
    ‖softDerivativeKernel momentum [] k x g y‖ = ‖softBase momentum k g y‖ := by
  simp [softDerivativeKernel, derivativeFactor, norm_fieldPhase]

theorem norm_softDerivativeKernel_le {Ω : Type*} (momentum : Ω → FieldSpace)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (x : FieldSpace) (g : Ω → ℂ)
    (y : Ω) :
    ‖softDerivativeKernel momentum ds k x g y‖ ≤
      k ^ ds.length * ‖softBase momentum k g y‖ := by
  by_cases hy : ‖momentum y‖ < k
  · simp only [softDerivativeKernel, norm_mul, norm_fieldPhase, mul_one]
    exact mul_le_mul_of_nonneg_right (norm_derivativeFactor_le ds hk hy.le)
      (norm_nonneg _)
  · simp [softDerivativeKernel, softBase, hy]

/-- Derivative kernel moments follow from the zeroth kernel moment. -/
theorem softDerivativeKernel_moment {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (momentum : Ω → FieldSpace) (ds : List (Fin 3))
    {k : ℝ} (hk : 0 ≤ k) (x : FieldSpace) (g : Ω → ℂ) (w : Ω → ℝ)
    (hw : ∀ y, 0 ≤ w y)
    (hbase : Integrable (fun y => w y * ‖softBase momentum k g y‖ ^ 2) ν)
    (hm : AEStronglyMeasurable
      (fun y => w y * ‖softDerivativeKernel momentum ds k x g y‖ ^ 2) ν) :
    Integrable (fun y => w y * ‖softDerivativeKernel momentum ds k x g y‖ ^ 2) ν ∧
    (∫ y, w y * ‖softDerivativeKernel momentum ds k x g y‖ ^ 2 ∂ν) ≤
      k ^ (2 * ds.length) * (∫ y, w y * ‖softBase momentum k g y‖ ^ 2 ∂ν) := by
  have hb (y : Ω) : w y * ‖softDerivativeKernel momentum ds k x g y‖ ^ 2 ≤
      k ^ (2 * ds.length) * (w y * ‖softBase momentum k g y‖ ^ 2) := by
    have h := norm_softDerivativeKernel_le momentum ds hk x g y
    have hs : ‖softDerivativeKernel momentum ds k x g y‖ ^ 2 ≤
        (k ^ ds.length * ‖softBase momentum k g y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    calc
      _ ≤ w y * (k ^ ds.length * ‖softBase momentum k g y‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (hw y)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
  have hi := (hbase.const_mul (k ^ (2 * ds.length))).mono' hm (by
    filter_upwards with y
    simpa only [Real.norm_of_nonneg (mul_nonneg (hw y) (sq_nonneg _))] using hb y)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, k ^ (2 * ds.length) * (w y * ‖softBase momentum k g y‖ ^ 2) ∂ν :=
      integral_mono hi (hbase.const_mul _) hb
    _ = _ := integral_const_mul _ _

namespace WienerSegalData

variable {Q H K G : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedSpace ℝ K]
  (W : WienerSegalData Q H K G μ)

/-- The conditional trace of the source mixture, expressed by its WIS fibres. -/
def sourceMass (ψ : ℕ → H) (q : Q) : ℝ := ∑' n, ‖W.toFiber (ψ n) q‖ ^ 2

theorem sourceMass_nonneg (ψ : ℕ → H) (q : Q) : 0 ≤ W.sourceMass ψ q :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem fiber_norm_sq_integral (ψ : H) :
    ∫ q, ‖W.toFiber ψ q‖ ^ 2 ∂μ = ‖ψ‖ ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun q => sq_nonneg ‖W.toFiber ψ q‖))
    ((W.measurable_fiber ψ).norm.pow 2), W.norm_sq, ENNReal.toReal_ofReal]
  exact sq_nonneg _

theorem sourceMass_integrable {ψ : ℕ → H} (hψ : Summable (fun n => ‖ψ n‖ ^ 2)) :
    Integrable (W.sourceMass ψ) μ := by
  apply integrable_series (F := fun n q => ‖W.toFiber (ψ n) q‖ ^ 2)
    (fun n => (W.measurable_fiber (ψ n)).norm.pow 2)
  simp only [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _), W.norm_sq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖ψ n‖) hψ]
  exact ENNReal.ofReal_ne_top

theorem integral_sourceMass {ψ : ℕ → H} (hψ : Summable (fun n => ‖ψ n‖ ^ 2)) :
    ∫ q, W.sourceMass ψ q ∂μ = ∑' n, ‖ψ n‖ ^ 2 := by
  have hf : ∑' n, ∫⁻ q, ‖‖W.toFiber (ψ n) q‖ ^ 2‖ₑ ∂μ ≠ ⊤ := by
    simp only [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _), W.norm_sq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖ψ n‖) hψ]
    exact ENNReal.ofReal_ne_top
  change (∫ q, ∑' n, ‖W.toFiber (ψ n) q‖ ^ 2 ∂μ) = _
  rw [bochner_series_integral (F := fun n q => ‖W.toFiber (ψ n) q‖ ^ 2)
    (fun n => (W.measurable_fiber (ψ n)).norm.pow 2) hf]
  simp only [W.fiber_norm_sq_integral]

/-- The moment weight is the trace of the already constructed conditional
density, rather than a separately chosen nonnegative function. -/
theorem trace_density_eq_sourceMass {T : Type*} [NormedAddCommGroup T]
    [NormedSpace ℝ T] [CompleteSpace T] (R : RankOneData K T)
    {ψ : ℕ → H} (hψ : Summable (fun n => ‖ψ n‖ ^ 2)) :
    (fun q => R.trace (R.density (fun n => W.toFiber (ψ n)) q)) =ᵐ[μ]
      W.sourceMass ψ := by
  apply R.trace_density_ae (fun n => W.measurable_fiber (ψ n))
  apply W.finite_fiber_mass
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖ψ n‖) hψ]
  exact ENNReal.ofReal_ne_top

/-- The weighted conditional second moment is a proved integrable function.
In particular its real integral cannot vanish merely from nonintegrability. -/
theorem source_field_second_moment (g : G) (ψ : ℕ → H)
    (hdom : ∀ n, W.fieldDomain g (ψ n))
    (hfield : Summable (fun n => ‖W.field g (ψ n)‖ ^ 2)) :
    Integrable (fun q => W.sourceMass ψ q * (W.coordinate g q) ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * (W.coordinate g q) ^ 2 ∂μ) =
      ∑' n, ‖W.field g (ψ n)‖ ^ 2 := by
  have hae : W.sourceMass (fun n => W.field g (ψ n)) =ᵐ[μ]
      fun q => W.sourceMass ψ q * (W.coordinate g q) ^ 2 := by
    filter_upwards [ae_all_iff.mpr (fun n => W.intertwining g (ψ n) (hdom n))] with q hq
    simp only [sourceMass, hq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      tsum_mul_left]
    exact mul_comm _ _
  exact ⟨(W.sourceMass_integrable hfield).congr hae,
    (integral_congr_ae hae).symm.trans (W.integral_sourceMass hfield)⟩

end WienerSegalData

/-- Standard field facts for a real commuting family of labels with explicit
one-photon kernels. `radiation` is the radiation square-root on its domain. -/
structure KernelFieldData {Q H K G Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
    {μ : Measure Q} (ν : Measure Ω) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (W : WienerSegalData Q H K G μ) (w : Ω → ℝ) where
  kernel : G → Ω → ℂ
  weight_nonneg : ∀ y, 0 ≤ w y
  radiationDomain : H → Prop
  radiation : H → H
  ann : G → H → H
  cre : G → H → H
  field_domain : ∀ g ψ, radiationDomain ψ →
    Integrable (fun y => ‖kernel g y‖ ^ 2) ν →
    Integrable (fun y => w y * ‖kernel g y‖ ^ 2) ν → W.fieldDomain g ψ
  field_eq : ∀ g ψ, W.fieldDomain g ψ → W.field g ψ = ann g ψ + cre g ψ
  annihilation_bound : ∀ g ψ, W.fieldDomain g ψ → radiationDomain ψ →
    Integrable (fun y => w y * ‖kernel g y‖ ^ 2) ν →
    ‖ann g ψ‖ ≤ Real.sqrt (∫ y, w y * ‖kernel g y‖ ^ 2 ∂ν) * ‖radiation ψ‖
  creation_norm_sq : ∀ g ψ, W.fieldDomain g ψ →
    Integrable (fun y => ‖kernel g y‖ ^ 2) ν →
    ‖cre g ψ‖ ^ 2 = ‖ann g ψ‖ ^ 2 + (∫ y, ‖kernel g y‖ ^ 2 ∂ν) * ‖ψ‖ ^ 2

namespace KernelFieldData

variable {Q H K G Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

/-- Vacuum fluctuation is the actual kernel norm. Its spatial constancy for
the soft Fourier kernel follows from `norm_softDerivativeKernel_nil`. -/
theorem vacuum_field_norm_sq (g : G) (Ω₀ : H) (hΩ : ‖Ω₀‖ = 1)
    (hdom : W.fieldDomain g Ω₀) (hrad : D.radiationDomain Ω₀)
    (hzero : D.radiation Ω₀ = 0)
    (hiA : Integrable (fun y => w y * ‖D.kernel g y‖ ^ 2) ν)
    (hiB : Integrable (fun y => ‖D.kernel g y‖ ^ 2) ν) :
    ‖W.field g Ω₀‖ ^ 2 = ∫ y, ‖D.kernel g y‖ ^ 2 ∂ν := by
  have ha : D.ann g Ω₀ = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hzero, norm_zero, mul_zero] using D.annihilation_bound g Ω₀ hdom hrad hiA
  rw [D.field_eq g Ω₀ hdom, ha, zero_add, D.creation_norm_sq g Ω₀ hdom hiB]
  simp [ha, hΩ]

/-- The vacuum variance of the actual soft field is the same at every
spatial point. No variance formula is assumed. -/
theorem vacuum_soft_field_variance (momentum : Ω → FieldSpace) (k : ℝ)
    (base : Ω → ℂ) (label : FieldSpace → G)
    (hkernel : ∀ x, D.kernel (label x) = softDerivativeKernel momentum [] k x base)
    (hbaseA : Integrable (fun y => w y * ‖softBase momentum k base y‖ ^ 2) ν)
    (hbaseB : Integrable (fun y => ‖softBase momentum k base y‖ ^ 2) ν)
    (Ω₀ : H) (hΩ : ‖Ω₀‖ = 1) (hrad : D.radiationDomain Ω₀)
    (hzero : D.radiation Ω₀ = 0) (x : FieldSpace) :
    ‖W.field (label x) Ω₀‖ ^ 2 = ∫ y, ‖softBase momentum k base y‖ ^ 2 ∂ν := by
  have hnorm (y : Ω) : ‖D.kernel (label x) y‖ = ‖softBase momentum k base y‖ := by
    rw [hkernel x, norm_softDerivativeKernel_nil]
  have hiA : Integrable (fun y => w y * ‖D.kernel (label x) y‖ ^ 2) ν := by
    simpa only [hnorm] using hbaseA
  have hiB : Integrable (fun y => ‖D.kernel (label x) y‖ ^ 2) ν := by
    simpa only [hnorm] using hbaseB
  rw [D.vacuum_field_norm_sq (label x) Ω₀ hΩ
    (D.field_domain (label x) Ω₀ hrad hiB hiA) hrad hzero hiA hiB]
  apply integral_congr_ae
  filter_upwards with y
  rw [hnorm]

theorem field_norm_sq_le (g : G) (ψ : H) (hdom : W.fieldDomain g ψ)
    (hrad : D.radiationDomain ψ)
    (hiA : Integrable (fun y => w y * ‖D.kernel g y‖ ^ 2) ν)
    (hiB : Integrable (fun y => ‖D.kernel g y‖ ^ 2) ν) :
    ‖W.field g ψ‖ ^ 2 ≤
      8 * (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν) * ‖D.radiation ψ‖ ^ 2 +
      2 * (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν) * ‖ψ‖ ^ 2 := by
  have hA : 0 ≤ ∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν :=
    integral_nonneg (fun y => mul_nonneg (D.weight_nonneg y) (sq_nonneg _))
  have hB : 0 ≤ ∫ y, ‖D.kernel g y‖ ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  have h := GptLean.PhotonLocalization.field_norm_le (D.ann g ψ) (D.cre g ψ)
    (q := Real.sqrt (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν))
    (g := Real.sqrt (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν))
    (r := ‖D.radiation ψ‖) (s := ‖ψ‖)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (D.annihilation_bound g ψ hdom hrad hiA) (by
      simpa only [Real.sq_sqrt hB] using D.creation_norm_sq g ψ hdom hiB)
  rw [← D.field_eq g ψ hdom] at h
  calc
    _ ≤ (2 * Real.sqrt (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν) * ‖D.radiation ψ‖ +
        Real.sqrt (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν) * ‖ψ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := by
      have hs := GptLean.RemovalEstimates.sq_two_mul_add_le
        (Real.sqrt (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν))
        (Real.sqrt (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν)) ‖D.radiation ψ‖ ‖ψ‖
      have hsA := congrArg (fun t : ℝ => t * ‖D.radiation ψ‖ ^ 2) (Real.sq_sqrt hA)
      have hsB := congrArg (fun t : ℝ => t * ‖ψ‖ ^ 2) (Real.sq_sqrt hB)
      nlinarith only [hs, hsA, hsB]

/-- The mixed-state field moment follows from source radiation and mass sums,
the annihilation bound, CCR and actual WIS intertwining. -/
theorem source_moment_le (g : G) (ψ : ℕ → H)
    (hdom : ∀ n, W.fieldDomain g (ψ n))
    (hrad : ∀ n, D.radiationDomain (ψ n))
    (hiA : Integrable (fun y => w y * ‖D.kernel g y‖ ^ 2) ν)
    (hiB : Integrable (fun y => ‖D.kernel g y‖ ^ 2) ν)
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2)) :
    Integrable (fun q => W.sourceMass ψ q * (W.coordinate g q) ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * (W.coordinate g q) ^ 2 ∂μ) ≤
      8 * (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν) * (∑' n, ‖D.radiation (ψ n)‖ ^ 2) +
      2 * (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν) * (∑' n, ‖ψ n‖ ^ 2) := by
  have hmajor := (hE.mul_left (8 * ∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν)).add
    (hP.mul_left (2 * ∫ y, ‖D.kernel g y‖ ^ 2 ∂ν))
  have hs := hmajor.of_nonneg_of_le (fun n => sq_nonneg ‖W.field g (ψ n)‖)
    (fun n => D.field_norm_sq_le g (ψ n) (hdom n) (hrad n) hiA hiB)
  obtain ⟨hi, heq⟩ := W.source_field_second_moment g ψ hdom hs
  refine ⟨hi, ?_⟩
  rw [heq]
  calc
    _ ≤ ∑' n, (8 * (∫ y, w y * ‖D.kernel g y‖ ^ 2 ∂ν) * ‖D.radiation (ψ n)‖ ^ 2 +
        2 * (∫ y, ‖D.kernel g y‖ ^ 2 ∂ν) * ‖ψ n‖ ^ 2) :=
      hs.tsum_le_tsum (fun n => D.field_norm_sq_le g (ψ n) (hdom n) (hrad n) hiA hiB) hmajor
    _ = _ := by rw [Summable.tsum_add (hE.mul_left _) (hP.mul_left _)]; simp [tsum_mul_left]

/-- The label is tied to an explicit derivative cutoff kernel. The moment
estimate is uniform in its spatial centre because the Fourier phase has norm one. -/
theorem derivative_source_moment_le (momentum : Ω → FieldSpace) (ds : List (Fin 3))
    {k : ℝ} (hk : 0 ≤ k) (x : FieldSpace) (base : Ω → ℂ) (g : G)
    (hkernel : D.kernel g = softDerivativeKernel momentum ds k x base)
    (hbaseA : Integrable (fun y => w y * ‖softBase momentum k base y‖ ^ 2) ν)
    (hbaseB : Integrable (fun y => ‖softBase momentum k base y‖ ^ 2) ν)
    (hmA : AEStronglyMeasurable (fun y => w y * ‖D.kernel g y‖ ^ 2) ν)
    (hmB : AEStronglyMeasurable (fun y => ‖D.kernel g y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2)) :
    Integrable (fun q => W.sourceMass ψ q * (W.coordinate g q) ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * (W.coordinate g q) ^ 2 ∂μ) ≤
      k ^ (2 * ds.length) *
        (8 * (∫ y, w y * ‖softBase momentum k base y‖ ^ 2 ∂ν) *
          (∑' n, ‖D.radiation (ψ n)‖ ^ 2) +
         2 * (∫ y, ‖softBase momentum k base y‖ ^ 2 ∂ν) * (∑' n, ‖ψ n‖ ^ 2)) := by
  obtain ⟨hiA, hbA⟩ := softDerivativeKernel_moment momentum ds hk x base w
    D.weight_nonneg hbaseA (by simpa only [← hkernel] using hmA)
  obtain ⟨hiB, hbB⟩ := softDerivativeKernel_moment momentum ds hk x base (fun _ => 1)
    (fun _ => zero_le_one) (by simpa using hbaseB) (by simpa only [one_mul, ← hkernel] using hmB)
  simp only [one_mul, ← hkernel] at hiA hiB hbA hbB
  obtain ⟨hi, hb⟩ := D.source_moment_le g ψ
    (fun n => D.field_domain g (ψ n) (hdom n) hiB hiA) hdom hiA hiB hE hP
  refine ⟨hi, hb.trans ?_⟩
  have hE0 : 0 ≤ ∑' n, ‖D.radiation (ψ n)‖ ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
  have hP0 : 0 ≤ ∑' n, ‖ψ n‖ ^ 2 := tsum_nonneg (fun n => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right hbA hE0
  have h2 := mul_le_mul_of_nonneg_right hbB hP0
  nlinarith

end KernelFieldData

/-- Uniform pointwise second moments give integrability on the product and
the integrated spatial moment. Both conclusions precede Fubini. -/
theorem spatial_moment_integrable_and_le {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] {σ : Measure X} {μ : Measure Q}
    [IsFiniteMeasure σ] [SFinite μ] (f : X → Q → ℝ) {B : ℝ} (_hB : 0 ≤ B)
    (hm : AEStronglyMeasurable (Function.uncurry f) (σ.prod μ))
    (h0 : ∀ x q, 0 ≤ f x q)
    (hi : ∀ x, Integrable (f x) μ) (hb : ∀ x, ∫ q, f x q ∂μ ≤ B) :
    Integrable (Function.uncurry f) (σ.prod μ) ∧
    Integrable (fun q => ∫ x, f x q ∂σ) μ ∧
    (∫ q, ∫ x, f x q ∂σ ∂μ) ≤ σ.real Set.univ * B := by
  have hn : Integrable (fun x => ∫ q, ‖f x q‖ ∂μ) σ := by
    apply (integrable_const B).mono' hm.norm.integral_prod_right'
    filter_upwards with x
    change ‖∫ q, ‖f x q‖ ∂μ‖ ≤ B
    have hn_eq : (fun q => ‖f x q‖) = f x :=
      funext (fun q => Real.norm_of_nonneg (h0 x q))
    rw [hn_eq, Real.norm_of_nonneg (integral_nonneg (h0 x))]
    exact hb x
  have hprod : Integrable (Function.uncurry f) (σ.prod μ) :=
    (integrable_prod_iff hm).mpr ⟨Eventually.of_forall hi, hn⟩
  refine ⟨hprod, hprod.integral_prod_right, ?_⟩
  calc
    _ = ∫ x, ∫ q, f x q ∂μ ∂σ := (integral_integral_swap hprod).symm
    _ ≤ ∫ _x, B ∂σ := integral_mono hprod.integral_prod_left (integrable_const B) hb
    _ = _ := by rw [integral_const, smul_eq_mul]

/-- The volume factor is independent of the cluster centre. -/
theorem field_ball_volume (x : FieldSpace) {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (volume.restrict (Metric.ball x (L * R))).real Set.univ =
      (Real.pi * 4 / 3) * L ^ 3 * R ^ (3 : ℤ) := by
  rw [measureReal_restrict_apply_univ, measureReal_def,
    EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg hL hR),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  norm_num
  ring

namespace KernelFieldData

variable {Q H K G Ω ι : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
  {μ : Measure Q} {ν : Measure Ω} [SFinite μ] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {W : WienerSegalData Q H K G μ} {w : Ω → ℝ} (D : KernelFieldData ν W w)

/-- The coefficient consists only of cutoff kernel norms and the original
mixture's radiation form and mass. -/
def cutoffSourceCoefficient (momentum : Ω → FieldSpace) (k : ℝ)
    (base : Ω → ℂ) (ψ : ℕ → H) : ℝ :=
  8 * (∫ y, w y * ‖softBase momentum k base y‖ ^ 2 ∂ν) *
    (∑' n, ‖D.radiation (ψ n)‖ ^ 2) +
  2 * (∫ y, ‖softBase momentum k base y‖ ^ 2 ∂ν) * (∑' n, ‖ψ n‖ ^ 2)

omit [SFinite μ] in
theorem cutoffSourceCoefficient_nonneg (momentum : Ω → FieldSpace) (k : ℝ)
    (base : Ω → ℂ) (ψ : ℕ → H) :
    0 ≤ D.cutoffSourceCoefficient momentum k base ψ := by
  unfold cutoffSourceCoefficient
  have hA : 0 ≤ ∫ y, w y * ‖softBase momentum k base y‖ ^ 2 ∂ν :=
    integral_nonneg (fun y => mul_nonneg (D.weight_nonneg y) (sq_nonneg _))
  have hB : 0 ≤ ∫ y, ‖softBase momentum k base y‖ ^ 2 ∂ν :=
    integral_nonneg (fun y => sq_nonneg _)
  positivity

/-- Actual spatial field moments on a cluster ball, including product
integrability and the centre-independent volume factor. -/
theorem derivative_ball_moment (momentum : Ω → FieldSpace) (ds : List (Fin 3))
    {k L R : ℝ} (hk : 0 ≤ k) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (centre : FieldSpace) (base : Ω → ℂ) (label : FieldSpace → G)
    (hkernel : ∀ x, D.kernel (label x) = softDerivativeKernel momentum ds k x base)
    (hbaseA : Integrable (fun y => w y * ‖softBase momentum k base y‖ ^ 2) ν)
    (hbaseB : Integrable (fun y => ‖softBase momentum k base y‖ ^ 2) ν)
    (hmA : ∀ x, AEStronglyMeasurable (fun y => w y * ‖D.kernel (label x) y‖ ^ 2) ν)
    (hmB : ∀ x, AEStronglyMeasurable (fun y => ‖D.kernel (label x) y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (hm : AEStronglyMeasurable
      (fun z : FieldSpace × Q => W.coordinate (label z.1) z.2)
      ((volume.restrict (Metric.ball centre (L * R))).prod μ)) :
    Integrable (fun q => ∫ x in Metric.ball centre (L * R),
      W.sourceMass ψ q * (W.coordinate (label x) q) ^ 2) μ ∧
    (∫ q, (∫ x in Metric.ball centre (L * R),
      W.sourceMass ψ q * (W.coordinate (label x) q) ^ 2) ∂μ) ≤
        R ^ (3 : ℤ) * k ^ (2 * ds.length) *
          ((Real.pi * 4 / 3) * L ^ 3 * D.cutoffSourceCoefficient momentum k base ψ) := by
  let σ : Measure FieldSpace := volume.restrict (Metric.ball centre (L * R))
  let : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpoint (x : FieldSpace) := D.derivative_source_moment_le momentum ds hk x base
    (label x) (hkernel x) hbaseA hbaseB (hmA x) (hmB x) ψ hdom hE hP
  have hcoef := D.cutoffSourceCoefficient_nonneg momentum k base ψ
  obtain ⟨_, hi, hb⟩ := spatial_moment_integrable_and_le (σ := σ) (μ := μ)
    (fun x q => W.sourceMass ψ q * (W.coordinate (label x) q) ^ 2)
    (B := k ^ (2 * ds.length) * D.cutoffSourceCoefficient momentum k base ψ)
    (mul_nonneg (pow_nonneg hk _) hcoef)
    (by
      convert (((W.sourceMass_integrable hP).aestronglyMeasurable.comp_snd).mul (hm.pow 2))
        using 1
      rfl)
    (fun x q => mul_nonneg (W.sourceMass_nonneg ψ q) (sq_nonneg _))
    (fun x => (hpoint x).1) (fun x => (hpoint x).2)
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [σ]
  rw [field_ball_volume centre hL hR]
  ring

/-- The Step 3 local supremum moment is now derived from actual kernels and
source energies. Only the local spatial Sobolev estimate is supplied. Each
index represents one component, derivative and cluster ball. No conditional
integrated field moment occurs among the hypotheses. -/
theorem local_sobolev_moment_from_kernels
    (momentum : Ω → FieldSpace) (ord : ι → ℕ) (ds : ι → List (Fin 3))
    (hord : ∀ i, (ds i).length = ord i + 1)
    {k L R C : ℝ} (hk : 0 ≤ k) (hL : 0 ≤ L) (hR : 0 < R) (hC : 0 ≤ C)
    (hkR : k * R ≤ 1) (centre : ι → FieldSpace) (base : ι → Ω → ℂ)
    (label : ι → FieldSpace → G)
    (hkernel : ∀ i x, D.kernel (label i x) = softDerivativeKernel momentum (ds i) k x (base i))
    (hbaseA : ∀ i, Integrable (fun y => w y * ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hbaseB : ∀ i, Integrable (fun y => ‖softBase momentum k (base i) y‖ ^ 2) ν)
    (hmA : ∀ i x, AEStronglyMeasurable (fun y => w y * ‖D.kernel (label i x) y‖ ^ 2) ν)
    (hmB : ∀ i x, AEStronglyMeasurable (fun y => ‖D.kernel (label i x) y‖ ^ 2) ν)
    (ψ : ℕ → H) (hdom : ∀ n, D.radiationDomain (ψ n))
    (hE : Summable (fun n => ‖D.radiation (ψ n)‖ ^ 2))
    (hP : Summable (fun n => ‖ψ n‖ ^ 2))
    (hm : ∀ i, AEStronglyMeasurable
      (fun z : FieldSpace × Q => W.coordinate (label i z.1) z.2)
      ((volume.restrict (Metric.ball (centre i) (L * R))).prod μ))
    (Z : Q → ℝ) (hZm : AEStronglyMeasurable Z μ)
    (hSob : ∀ᵐ q ∂μ, W.sourceMass ψ q * Z q ^ 2 ≤
      C * ∑ i, R ^ (2 * (ord i : ℤ) - 3) *
        (∫ x in Metric.ball (centre i) (L * R),
          W.sourceMass ψ q * (W.coordinate (label i x) q) ^ 2)) :
    Integrable (fun q => W.sourceMass ψ q * Z q ^ 2) μ ∧
    (∫ q, W.sourceMass ψ q * Z q ^ 2 ∂μ) ≤
      C * (Fintype.card ι : ℝ) * k ^ 2 *
        ((Real.pi * 4 / 3) * L ^ 3 *
          ∑ i, D.cutoffSourceCoefficient momentum k (base i) ψ) := by
  classical
  let A : ℝ := (Real.pi * 4 / 3) * L ^ 3
  let B : ℝ := A * ∑ i, D.cutoffSourceCoefficient momentum k (base i) ψ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoef := fun i => D.cutoffSourceCoefficient_nonneg momentum k (base i) ψ
  have hB : 0 ≤ B := mul_nonneg hA (Finset.sum_nonneg (fun i _ => hcoef i))
  have hball (i : ι) := D.derivative_ball_moment momentum (ds i) hk hL hR.le
    (centre i) (base i) (label i) (hkernel i) (hbaseA i) (hbaseB i) (hmA i) (hmB i)
    ψ hdom hE hP (hm i)
  apply integrated_scaled_sobolev ord
    (fun i q => ∫ x in Metric.ball (centre i) (L * R),
      W.sourceMass ψ q * (W.coordinate (label i x) q) ^ 2)
    hC hR hB (mul_nonneg hk hR.le) hkR
    ((W.sourceMass_integrable hP).aestronglyMeasurable.mul (hZm.pow 2))
    (Eventually.of_forall (fun q => mul_nonneg (W.sourceMass_nonneg ψ q) (sq_nonneg _)))
    (fun i => (hball i).1) hSob
  intro i
  have hterm : D.cutoffSourceCoefficient momentum k (base i) ψ ≤
      ∑ j, D.cutoffSourceCoefficient momentum k (base j) ψ :=
    Finset.single_le_sum (fun j _ => hcoef j) (Finset.mem_univ i)
  have hbound := (hball i).2
  rw [hord i, show 2 * (ord i + 1) = 2 * ord i + 2 by omega] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hterm hA)
    (mul_nonneg (zpow_nonneg hR.le _) (pow_nonneg hk _)))

end KernelFieldData

end

end GptLean.Gaussian
