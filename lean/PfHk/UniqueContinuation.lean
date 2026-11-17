import PfHk.InfiniteOrder
import PfHk.CarlemanWeights
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
The continuation argument after a local Carleman estimate. This module proves
inner error decay, removal of an inner cutoff by Fatou's lemma, exponential
separation, and propagation of local almost-everywhere vanishing.
The differential-operator estimate itself is a separate input.
-/

noncomputable section
namespace PfHk.UniqueContinuation

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- Strict increase of the cylinder phase on the whole small-radius region. -/
theorem weight_strictMonoOn {α : ℝ} (hα : 0 < α) :
    StrictMonoOn (CarlemanWeights.weight α) (Ici 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 2)
  · intro t ht
    have ht2 : 2 ≤ t := ht
    exact (CarlemanWeights.weight_hasDerivAt α (by linarith : 0 < t)).continuousAt.continuousWithinAt
  · intro t ht
    have ht2 : 2 ≤ t := interior_subset ht
    rw [(CarlemanWeights.weight_hasDerivAt α (by linarith : 0 < t)).deriv]
    exact (CarlemanWeights.weightPrime_pos_le_one hα ht2).1

/-- The strict phase gap between nested radii, with all logarithm signs
accounted for. -/
theorem radial_weight_gap {α r R : ℝ} (hα : 0 < α)
    (hr : 0 < r) (hrR : r < R) (hR : R ≤ Real.exp (-2)) :
    CarlemanWeights.weight α (-Real.log R) <
      CarlemanWeights.weight α (-Real.log r) := by
  have hRpos : 0 < R := hr.trans hrR
  have hlogR := Real.log_le_log hRpos hR
  rw [Real.log_exp] at hlogR
  have hlog := Real.log_lt_log hr hrR
  exact weight_strictMonoOn hα (by change 2 ≤ -Real.log R; linarith) (by change 2 ≤ -Real.log r; linarith)
    (by linarith)

/-- After shrinking the ball, the actual coefficient `β(-log r) r⁻²`
is bounded below by one. This follows from the proved radius supremum limit. -/
theorem exists_radius_mass_coefficient (α : ℝ) (hα : 0 < α) :
    ∃ R : ℝ, 0 < R ∧ R < Real.exp (-2) ∧
      ∀ r : ℝ, 0 < r → r ≤ R →
        1 ≤ CarlemanWeights.beta α (-Real.log r) * r ^ (-2 : ℝ) := by
  obtain ⟨R, hR, hRsmall, hratio⟩ := CarlemanWeights.exists_radius_small α
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 1)
  refine ⟨R, hR, hRsmall, ?_⟩
  intro r hr hrR
  have hlog := Real.log_lt_log hr (hrR.trans_lt hRsmall)
  rw [Real.log_exp] at hlog
  have hβ := CarlemanWeights.beta_pos hα (by linarith : 0 < -Real.log r)
  have hh := (div_lt_one hβ).mp (hratio r hr hrR)
  rw [Real.rpow_two] at hh
  rw [Real.rpow_neg hr.le, Real.rpow_two, ← div_eq_mul_inv]
  exact (one_le_div (sq_pos_of_pos hr)).mpr hh.le

/-- Flatness beats every fixed negative power of the cutoff radius. -/
theorem flat_mul_rpow_tendsto {U : ℝ → ℝ}
    (hU : ∀ r, 0 < r → 0 ≤ U r) (hflat : InfiniteOrder.FlatAtZero U) (p : ℝ) :
    Tendsto (fun r => r ^ p * U r) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, R, hR, hbound⟩ := hflat.real_order (1 - p)
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hrR : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds |>.mono fun _ h => h.le
  apply squeeze_zero' (hrpos.mono fun r hr => mul_nonneg (Real.rpow_nonneg hr.le _) (hU r hr))
  · filter_upwards [hrpos, hrR] with r hr hrR'
    calc
      r ^ p * U r ≤ r ^ p * (C * r ^ (1 - p)) :=
        mul_le_mul_of_nonneg_left (hbound r hr hrR') (Real.rpow_nonneg hr.le _)
      _ = C * r := by
        rw [mul_left_comm, ← Real.rpow_add hr]
        simp
  · simpa using (tendsto_const_nhds.mul (nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r)
      (𝓝[>] 0) (𝓝 0)) : Tendsto (fun r : ℝ => C * r) (𝓝[>] 0) (𝓝 (C * 0)))

/-- Rescaling a flat mass preserves flatness, with a positive scale. -/
theorem flat_rescale {U : ℝ → ℝ} (hflat : InfiniteOrder.FlatAtZero U)
    {a : ℝ} (ha : 0 < a) : InfiniteOrder.FlatAtZero (fun r => U (a * r)) := by
  intro m
  obtain ⟨C, hC, R, hR, hbound⟩ := hflat m
  refine ⟨C * a ^ m, by positivity, R / a, div_pos hR ha, ?_⟩
  intro r hr hrR
  calc
    U (a * r) ≤ C * (a * r) ^ m :=
      hbound _ (mul_pos ha hr) (by nlinarith [(le_div_iff₀ ha).mp hrR])
    _ = (C * a ^ m) * r ^ m := by rw [mul_pow]; ring

/-- The logarithmic correction in the paper costs only a fixed constant for
each fixed Carleman parameter. -/
theorem cutoff_weight_le {α τ r : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ)
    (hr : 0 < r) (hsmall : r ≤ Real.exp (-1)) :
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) ≤
      Real.exp (2 * τ) * r ^ (-2 * τ) := by
  have ht : 1 ≤ -Real.log r := by
    have hlog := Real.log_le_log hr hsmall
    rw [Real.log_exp] at hlog
    linarith
  have hcorr : (-Real.log r) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr hα)
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [CarlemanWeights.weight]
  nlinarith

/-- The actual radial inner-commutator bound tends to zero. Both mass and
covariant-energy integrals may be substituted for `M` and `K`. -/
theorem inner_error_tendsto {M K : ℝ → ℝ}
    (hM : ∀ r, 0 < r → 0 ≤ M r) (hK : ∀ r, 0 < r → 0 ≤ K r)
    (hMf : InfiniteOrder.FlatAtZero M) (hKf : InfiniteOrder.FlatAtZero K)
    {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) :
    Tendsto (fun r => Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) *
      (r ^ (-2 : ℝ) * M (2 * r) + K (2 * r))) (𝓝[>] 0) (𝓝 0) := by
  have hMr := flat_rescale hMf (by norm_num : (0 : ℝ) < 2)
  have hKr := flat_rescale hKf (by norm_num : (0 : ℝ) < 2)
  have hlimM := flat_mul_rpow_tendsto (fun r hr => hM _ (by linarith)) hMr (-2 * τ - 2)
  have hlimK := flat_mul_rpow_tendsto (fun r hr => hK _ (by linarith)) hKr (-2 * τ)
  have hlim := (hlimM.add hlimK).const_mul (Real.exp (2 * τ))
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ Real.exp (-1) :=
    (eventually_lt_nhds (Real.exp_pos (-1))).filter_mono nhdsWithin_le_nhds |>.mono fun _ h => h.le
  apply squeeze_zero'
  · filter_upwards [hrpos] with r hr
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (hM _ (by linarith))) (hK _ (by linarith)))
  · filter_upwards [hrpos, hrsmall] with r hr hrs
    calc
      _ ≤ (Real.exp (2 * τ) * r ^ (-2 * τ)) *
          (r ^ (-2 : ℝ) * M (2 * r) + K (2 * r)) :=
        mul_le_mul_of_nonneg_right (cutoff_weight_le hα hτ hr hrs)
          (add_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (hM _ (by linarith)))
            (hK _ (by linarith)))
      _ = Real.exp (2 * τ) * (r ^ (-2 * τ - 2) * M (2 * r) +
          r ^ (-2 * τ) * K (2 * r)) := by
        rw [sub_eq_add_neg, Real.rpow_add hr]
        ring
  · simpa using hlim

/-- Fatou removes an inner cutoff. The integrands are allowed to be infinite
in the limit, so integrability at the singular center is not presumed. -/
theorem cutoff_removal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞} {error : ℕ → ℝ} {B : ℝ}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal (B + error n))
    (herror : Tendsto error atTop (𝓝 0)) :
    ∫⁻ x, f x ∂μ ≤ ENNReal.ofReal B := by
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with x hx using hx.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop := lintegral_liminf_le' hF
    _ ≤ liminf (fun n => ENNReal.ofReal (B + error n)) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    _ = ENNReal.ofReal B := by
      exact (ENNReal.continuous_ofReal.tendsto B |>.comp
        (by simpa using tendsto_const_nhds.add herror)).liminf_eq

/-- A finite Fatou bound supplies integrability of the singular limiting
weight and the corresponding real integral bound. -/
theorem integrable_and_integral_le_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ) (hpos : 0 ≤ᵐ[μ] f) (hB : 0 ≤ B)
    (hbound : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hf hpos).mp hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hpos hf]
  simpa only [ENNReal.toReal_ofReal hB] using
    (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hbound

/-- Exponentially separated weights force a fixed nonnegative mass to vanish.
The factor `τ³` can be discarded for `τ ≥ 1`. -/
theorem mass_eq_zero_of_exponential_separation {m C a b τ₀ : ℝ}
    (hm : 0 ≤ m) (hab : a < b)
    (hbound : ∀ τ : ℝ, max τ₀ 1 ≤ τ →
      τ ^ 3 * Real.exp (2 * τ * b) * m ≤ C * Real.exp (2 * τ * a)) :
    m = 0 := by
  have hlim : Tendsto (fun τ : ℝ => C * Real.exp (-(2 * (b - a)) * τ))
      atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by linarith : 0 < 2 * (b - a)))
    convert h.const_mul C using 1
    · ext τ
      dsimp
      congr 2
      ring
    · simp
  apply le_antisymm _ hm
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (max τ₀ 1)] with τ hτ
  have hτ1 : 1 ≤ τ := le_trans (le_max_right _ _) hτ
  have hτ3 : 1 ≤ τ ^ 3 := one_le_pow₀ hτ1
  have hfirst : Real.exp (2 * τ * b) * m ≤ C * Real.exp (2 * τ * a) :=
    (by nlinarith [mul_nonneg (Real.exp_pos (2 * τ * b)).le hm] :
      Real.exp (2 * τ * b) * m ≤ τ ^ 3 * Real.exp (2 * τ * b) * m).trans (hbound τ hτ)
  have hd := (le_div_iff₀ (Real.exp_pos (2 * τ * b))).mpr (by simpa [mul_comm] using hfirst)
  convert hd using 1
  rw [mul_div_assoc, ← Real.exp_sub]
  congr 2
  ring

section WeightedIntegral

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    {μ : Measure X}

/-- The real weighted squared norm in the Carleman mass term. -/
def weightedNormSq (w φ : X → ℝ) (ψ : X → H) (τ : ℝ) (x : X) : ℝ :=
  w x * Real.exp (2 * τ * φ x) * ‖ψ x‖ ^ 2

/-- The paper's mass integrand in the physical radial coordinate. -/
def radialMassIntegrand (r : X → ℝ) (ψ : X → H) (α τ : ℝ) (x : X) : ℝ :=
  τ ^ 3 * weightedNormSq
    (fun y => CarlemanWeights.beta α (-Real.log (r y)) * (r y) ^ (-2 : ℝ))
    (fun y => CarlemanWeights.weight α (-Real.log (r y))) ψ τ x

/-- The exact weighted mass integral after removal of the inner cutoff.
The input is the cutoff Carleman inequality with its radial commutator bound.
No integrability at the center is needed. -/
theorem remove_flat_inner_cutoff [NormedSpace ℝ H]
    {r : X → ℝ} {ψ : X → H} {η : ℕ → X → ℝ} {ε : ℕ → ℝ}
    {M K : ℝ → ℝ} {α τ B C : ℝ}
    (hr : ∀ᵐ x ∂μ, 0 < r x)
    (hε : Tendsto ε atTop (𝓝[>] 0))
    (hη : ∀ n x, 2 * ε n ≤ r x → η n x = 1)
    (hM : ∀ s, 0 < s → 0 ≤ M s) (hK : ∀ s, 0 < s → 0 ≤ K s)
    (hMf : InfiniteOrder.FlatAtZero M) (hKf : InfiniteOrder.FlatAtZero K)
    (hα : 0 ≤ α) (hτ : 0 ≤ τ)
    (hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal
      (radialMassIntegrand r (fun y => η n y • ψ y) α τ x)) μ)
    (hbound : ∀ n,
      (∫⁻ x, ENNReal.ofReal (radialMassIntegrand r (fun y => η n y • ψ y) α τ x) ∂μ) ≤
        ENNReal.ofReal (B + C * (Real.exp
          (2 * τ * CarlemanWeights.weight α (-Real.log (ε n))) *
            ((ε n) ^ (-2 : ℝ) * M (2 * ε n) + K (2 * ε n))))) :
    (∫⁻ x, ENNReal.ofReal (radialMassIntegrand r ψ α τ x) ∂μ) ≤ ENNReal.ofReal B := by
  refine cutoff_removal hmeas ?_ hbound ?_
  · filter_upwards [hr] with x hx
    have he : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
      simpa using (hε.mono_right nhdsWithin_le_nhds).const_mul 2
    have heta : ∀ᶠ n in atTop, η n x = 1 :=
      (he.eventually (eventually_lt_nhds hx)).mono fun n hn => hη n x hn.le
    apply tendsto_const_nhds.congr'
    filter_upwards [heta] with n hn
    simp only [radialMassIntegrand, weightedNormSq, hn, one_smul]
  · simpa using ((inner_error_tendsto hM hK hMf hKf hα hτ).comp hε).const_mul C

/-- Actual weighted-integral exponential separation. The measure can already
be restricted to an inner ball. The outer-error estimate and the two pointwise
weight bounds imply almost-everywhere vanishing of the Hilbert-valued field. -/
theorem ae_zero_of_weighted_estimate {ψ : X → H} {w φ : X → ℝ}
    {c C a b τ₀ : ℝ} (hc : 0 < c) (hab : a < b)
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hw : ∀ᵐ x ∂μ, c ≤ w x) (hφ : ∀ᵐ x ∂μ, b ≤ φ x)
    (hint : ∀ τ, max τ₀ 1 ≤ τ → Integrable (weightedNormSq w φ ψ τ) μ)
    (hbound : ∀ τ, max τ₀ 1 ≤ τ →
      τ ^ 3 * (∫ x, weightedNormSq w φ ψ τ x ∂μ) ≤ C * Real.exp (2 * τ * a)) :
    ∀ᵐ x ∂μ, ψ x = 0 := by
  have hmass : 0 ≤ ∫ x, ‖ψ x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hzero : c * (∫ x, ‖ψ x‖ ^ 2 ∂μ) = 0 :=
    mass_eq_zero_of_exponential_separation (mul_nonneg hc.le hmass) hab (by
      intro τ hτ
      have hτ0 : 0 ≤ τ := le_trans zero_le_one ((le_max_right _ _).trans hτ)
      have hlow : c * Real.exp (2 * τ * b) * (∫ x, ‖ψ x‖ ^ 2 ∂μ) ≤
          ∫ x, weightedNormSq w φ ψ τ x ∂μ := by
        rw [← integral_const_mul]
        apply integral_mono_ae (hψ.const_mul _) (hint τ hτ)
        filter_upwards [hw, hφ] with x hwx hφx
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hwx (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hφx (by positivity)))
            (Real.exp_pos _).le (hc.le.trans hwx)) (sq_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hlow (pow_nonneg hτ0 3)
      calc
        τ ^ 3 * Real.exp (2 * τ * b) * (c * ∫ x, ‖ψ x‖ ^ 2 ∂μ) =
            τ ^ 3 * (c * Real.exp (2 * τ * b) * ∫ x, ‖ψ x‖ ^ 2 ∂μ) := by ring
        _ ≤ τ ^ 3 * (∫ x, weightedNormSq w φ ψ τ x ∂μ) := hmul
        _ ≤ C * Real.exp (2 * τ * a) := hbound τ hτ)
  have hnorm : (fun x => ‖ψ x‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hψ).mp
      ((mul_eq_zero.mp hzero).resolve_left hc.ne')
  filter_upwards [hnorm] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Specialization to the paper's logarithmic phase and its actual radial
mass coefficient. The measure is the restriction to the inner ball. -/
theorem ae_zero_of_radial_outer_error {ψ : X → H} {r : X → ℝ}
    {α inner outer C τ₀ : ℝ} (hα : 0 < α)
    (hinner : 0 < inner) (hio : inner < outer) (houter : outer ≤ Real.exp (-2))
    (hr : ∀ᵐ x ∂μ, 0 < r x ∧ r x < inner)
    (hcoef : ∀ s, 0 < s → s ≤ inner →
      1 ≤ CarlemanWeights.beta α (-Real.log s) * s ^ (-2 : ℝ))
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hint : ∀ τ, max τ₀ 1 ≤ τ → Integrable (fun x =>
      CarlemanWeights.beta α (-Real.log (r x)) * (r x) ^ (-2 : ℝ) *
        Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (r x))) * ‖ψ x‖ ^ 2) μ)
    (hbound : ∀ τ, max τ₀ 1 ≤ τ →
      τ ^ 3 * (∫ x,
        CarlemanWeights.beta α (-Real.log (r x)) * (r x) ^ (-2 : ℝ) *
          Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log (r x))) * ‖ψ x‖ ^ 2 ∂μ) ≤
        C * Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log outer))) :
    ∀ᵐ x ∂μ, ψ x = 0 := by
  refine ae_zero_of_weighted_estimate (c := 1) (by norm_num)
    (radial_weight_gap hα hinner hio houter) hψ ?_ ?_ hint hbound
  · filter_upwards [hr] with x hx using hcoef (r x) hx.1 hx.2.le
  · filter_upwards [hr] with x hx
    exact (radial_weight_gap hα hx.1 hx.2 (hio.le.trans houter)).le

end WeightedIntegral

section Propagation

variable {X H : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [Zero H] {μ : Measure X} {ψ : X → H}

/-- Points with a neighborhood on which the field is zero almost everywhere. -/
def zeroNeighborhoods (μ : Measure X) (ψ : X → H) : Set X :=
  {x | ∃ r : ℝ, 0 < r ∧ ∀ᵐ y ∂μ.restrict (Metric.ball x r), ψ y = 0}

theorem zeroNeighborhoods_isOpen : IsOpen (zeroNeighborhoods μ ψ) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r, hr, hz⟩
  refine ⟨r / 2, by positivity, ?_⟩
  intro y hy
  refine ⟨r / 2, by positivity, ae_restrict_of_ae_restrict_of_subset ?_ hz⟩
  intro z hz'
  have := dist_triangle z y x
  dsimp [Metric.ball] at *
  linarith

/-- A uniform local vanishing radius near each point closes the open zero
set. This is the center-uniformity required in the paper's propagation step. -/
theorem zeroNeighborhoods_propagate {U : Set X} (hU : IsPreconnected U)
    (hstart : (U ∩ zeroNeighborhoods μ ψ).Nonempty)
    (hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ zeroNeighborhoods μ ψ, dist x y < r / 2 →
        ∀ᵐ z ∂μ.restrict (Metric.ball y r), ψ z = 0) :
    U ⊆ zeroNeighborhoods μ ψ := by
  apply hU.subset_of_closure_inter_subset zeroNeighborhoods_isOpen hstart
  rintro x ⟨hxcl, hxU⟩
  obtain ⟨r, hr, hball⟩ := hlocal x hxU
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hxcl (r / 2) (by positivity)
  refine ⟨r / 2, by positivity,
    ae_restrict_of_ae_restrict_of_subset ?_ (hball y hy hxy)⟩
  intro z hz
  have := dist_triangle z x y
  dsimp [Metric.ball] at *
  linarith

/-- A countable subcover turns local almost-everywhere zero statements into a
single almost-everywhere statement on the whole zero-neighborhood set. -/
theorem ae_zero_on_zeroNeighborhoods [SecondCountableTopology X] :
    ∀ᵐ x ∂μ.restrict (zeroNeighborhoods μ ψ), ψ x = 0 := by
  classical
  let Z := zeroNeighborhoods μ ψ
  choose r hr hz using (show ∀ x : Z, ∃ r : ℝ, 0 < r ∧
    ∀ᵐ y ∂μ.restrict (Metric.ball (x : X) r), ψ y = 0 from fun x => x.property)
  obtain ⟨S, hSc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover
    (fun x : Z => Metric.ball (x : X) (r x)) (fun _ => Metric.isOpen_ball)
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  apply ae_restrict_of_ae_restrict_of_subset hcover
  apply (ae_restrict_biUnion_iff _ hSc _).mpr
  intro x _
  exact hz x

/-- Propagation on a connected full-measure region yields zero in the full
Hilbert-space representative, without any positivity-preserving argument. -/
theorem ae_zero_of_local_propagation [SecondCountableTopology X]
    {U : Set X} (hU : IsPreconnected U) (hfull : ∀ᵐ x ∂μ, x ∈ U)
    (hstart : (U ∩ zeroNeighborhoods μ ψ).Nonempty)
    (hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ zeroNeighborhoods μ ψ, dist x y < r / 2 →
        ∀ᵐ z ∂μ.restrict (Metric.ball y r), ψ z = 0) :
    ∀ᵐ x ∂μ, ψ x = 0 := by
  have hsub := zeroNeighborhoods_propagate hU hstart hlocal
  have hfullZ : ∀ᵐ x ∂μ, x ∈ zeroNeighborhoods μ ψ := hfull.mono fun _ hx => hsub hx
  have hz := ae_zero_on_zeroNeighborhoods (μ := μ) (ψ := ψ)
  rwa [Measure.restrict_eq_self_of_ae_mem hfullZ] at hz

end Propagation

end PfHk.UniqueContinuation
