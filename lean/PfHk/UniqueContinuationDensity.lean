import PfHk.UniqueContinuation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The zero-density-point step. Hölder's inequality supplies the measure of the
nonzero set, and standard Sobolev and localized-energy bounds then give the
small doubling coefficient for the actual local squared-norm integral.
-/

noncomputable section
namespace PfHk.UniqueContinuationDensity

open Filter MeasureTheory Set
open scoped Topology ENNReal

section Holder

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Hölder's inequality with the actual measure of a set supporting `f`.
The Sobolev application uses `f = (η ‖ψ‖)²` and conjugate exponents
`p = d/(d-2)` and `q = d/2`. -/
theorem integral_le_support_measure {f : X → ℝ} {s : Set X} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hfpos : ∀ x, 0 ≤ f x)
    (_hs : MeasurableSet s) (hsfin : μ s < ∞)
    (hsupp : ∀ x, x ∉ s → f x = 0)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫ x, f x ∂μ) ≤ (μ s).toReal ^ (1 / q) * (∫ x, f x ^ p ∂μ) ^ (1 / p) := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hsfin⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hfpos : 0 ≤ᵐ[μ.restrict s] f)
    (Eventually.of_forall (fun _ => zero_le_one) : 0 ≤ᵐ[μ.restrict s] fun _ => (1 : ℝ))
    (hf.restrict s) (memLp_const (1 : ℝ))
  have heq : (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  have hpoweq : (∫ x in s, f x ^ p ∂μ) = ∫ x, f x ^ p ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hsupp x hx, Real.zero_rpow hpq.pos.ne']
  simpa only [mul_one, Real.one_rpow, setIntegral_const, smul_eq_mul,
    mul_one, one_mul, heq, hpoweq, Measure.real, mul_comm] using h

end Holder

section DensityFactor

/-- A density ratio normalized by `r^(2q)` gives exactly the small coefficient
needed after the `r⁻²` Caccioppoli scaling. -/
theorem density_factor_tendsto {v : ℝ → ℝ} {q : ℝ} (hq : 0 < q)
    (hv : ∀ r, 0 < r → 0 ≤ v r)
    (hdensity : Tendsto (fun r => v r / r ^ (2 * q)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => (v (2 * r)) ^ (1 / q) / r ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hscale : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    refine ⟨by simpa using hid.const_mul 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (show 0 < 2 * r from mul_pos (by norm_num) hr)
  have hlim := ((hdensity.comp hscale).rpow_const_nhds_zero (by positivity : 0 < 1 / q)).const_mul 4
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  have h2r : 0 < 2 * r := by positivity
  dsimp only [Function.comp_def]
  rw [Real.div_rpow (hv _ h2r) (Real.rpow_nonneg h2r.le _),
    ← Real.rpow_mul h2r.le]
  have he : 2 * q * (1 / q) = 2 := by field_simp
  rw [he, Real.rpow_two]
  field_simp
  ring

end DensityFactor

section LocalMass

variable {X H : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X}

def localMass (ψ : X → H) (x₀ : X) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball x₀ r, ‖ψ x‖ ^ 2 ∂μ

def nonzeroRegion (ψ : X → H) (x₀ : X) (r : ℝ) : Set X :=
  Metric.ball x₀ r ∩ {x | ψ x ≠ 0}

theorem localMass_nonneg (ψ : X → H) (x₀ : X) (r : ℝ) :
    0 ≤ localMass (μ := μ) ψ x₀ r := integral_nonneg fun _ => sq_nonneg _

theorem localMass_monotone {ψ : X → H} (x₀ : X)
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ) :
    Monotone (localMass (μ := μ) ψ x₀) := by
  intro r R hrR
  exact setIntegral_mono_set (hψ.integrableOn) (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall (Metric.ball_subset_ball hrR))

/-- Local zero neighborhoods supply infinite-order vanishing of the actual
mass. This connects the propagation argument to the analytic flatness input. -/
theorem flat_of_zeroNeighborhood {ψ : X → H} {x₀ : X}
    (hzero : x₀ ∈ UniqueContinuation.zeroNeighborhoods μ ψ) :
    InfiniteOrder.FlatAtZero (localMass (μ := μ) ψ x₀) := by
  obtain ⟨R, hR, hz⟩ := hzero
  intro m
  refine ⟨1, zero_lt_one, R, hR, ?_⟩
  intro r hr hrR
  have hzr := ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR) hz
  have hm : localMass (μ := μ) ψ x₀ r = 0 := by
    unfold localMass
    calc
      _ = ∫ _ in Metric.ball x₀ r, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hzr] with x hx
        simp [hx]
      _ = 0 := integral_zero _ _
  rw [hm]
  positivity

/-- The actual local-mass recurrence follows from Hölder, a scalar Sobolev
bound, and the localized Caccioppoli bound. The recurrence is a conclusion,
not an assumed property of an abstract mass function. -/
theorem local_mass_recurrence [BorelSpace X] {ψ : X → H} {x₀ : X} {η : X → ℝ}
    {r p q S K G : ℝ} (_hr : 0 < r) (hpq : p.HolderConjugate q)
    (hS : 0 ≤ S)
    (hs : MeasurableSet (nonzeroRegion ψ x₀ (2 * r)))
    (hsfin : μ (nonzeroRegion ψ x₀ (2 * r)) < ∞)
    (hηone : ∀ x ∈ Metric.ball x₀ r, η x = 1)
    (hηsupp : ∀ x, x ∉ Metric.ball x₀ (2 * r) → η x = 0)
    (hloc : Integrable (fun x => (η x * ‖ψ x‖) ^ 2) μ)
    (hlp : MemLp (fun x => (η x * ‖ψ x‖) ^ 2) (ENNReal.ofReal p) μ)
    (hsob : (∫ x, ((η x * ‖ψ x‖) ^ 2) ^ p ∂μ) ^ (1 / p) ≤ S * G)
    (henergy : G ≤ K / r ^ 2 * localMass (μ := μ) ψ x₀ (2 * r)) :
    localMass (μ := μ) ψ x₀ r ≤
      (S * K * ((μ (nonzeroRegion ψ x₀ (2 * r))).toReal ^ (1 / q) / r ^ 2)) *
        localMass (μ := μ) ψ x₀ (2 * r) := by
  have hholder := integral_le_support_measure hpq (fun x => sq_nonneg (η x * ‖ψ x‖))
    hs hsfin (f := fun x => (η x * ‖ψ x‖) ^ 2) (by
      intro x hx
      by_cases hxb : x ∈ Metric.ball x₀ (2 * r)
      · have hz : ψ x = 0 := by
          by_contra hz
          exact hx ⟨hxb, hz⟩
        simp [hz]
      · simp [hηsupp x hxb]) hlp
  have hstart : localMass (μ := μ) ψ x₀ r ≤ ∫ x, (η x * ‖ψ x‖) ^ 2 ∂μ := by
    calc
      _ = ∫ x in Metric.ball x₀ r, (η x * ‖ψ x‖) ^ 2 ∂μ := by
        apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
        intro x hx
        simp [hηone x hx]
      _ ≤ _ := setIntegral_le_integral hloc (Eventually.of_forall fun x => sq_nonneg _)
  have hfac : 0 ≤ (μ (nonzeroRegion ψ x₀ (2 * r))).toReal ^ (1 / q) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc
    _ ≤ _ := hstart.trans hholder
    _ ≤ (μ (nonzeroRegion ψ x₀ (2 * r))).toReal ^ (1 / q) * (S * G) :=
      mul_le_mul_of_nonneg_left hsob hfac
    _ ≤ (μ (nonzeroRegion ψ x₀ (2 * r))).toReal ^ (1 / q) *
        (S * (K / r ^ 2 * localMass (μ := μ) ψ x₀ (2 * r))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy hS) hfac
    _ = _ := by ring

/-- At a density point of the zero set, the standard scalar Sobolev estimate
and the localized energy estimate force infinite-order vanishing of the
physical squared-norm mass. Density is normalized by `r^(2q)`, proportional to
ball volume in dimension `2q`. -/
theorem flat_at_zero_density_point [BorelSpace X]
    {ψ : X → H} {x₀ : X} {η : ℝ → X → ℝ} {G : ℝ → ℝ}
    {p q S K R₀ : ℝ} (hpq : p.HolderConjugate q) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ)
    (hdensity : Tendsto (fun r => (μ (nonzeroRegion ψ x₀ r)).toReal / r ^ (2 * q))
      (𝓝[>] 0) (𝓝 0))
    (hs : ∀ r, MeasurableSet (nonzeroRegion ψ x₀ r))
    (hsfin : ∀ r, μ (nonzeroRegion ψ x₀ r) < ∞)
    (hηone : ∀ r, 0 < r → r ≤ R₀ → ∀ x ∈ Metric.ball x₀ r, η r x = 1)
    (hηsupp : ∀ r, 0 < r → r ≤ R₀ → ∀ x, x ∉ Metric.ball x₀ (2 * r) → η r x = 0)
    (hloc : ∀ r, 0 < r → r ≤ R₀ → Integrable (fun x => (η r x * ‖ψ x‖) ^ 2) μ)
    (hlp : ∀ r, 0 < r → r ≤ R₀ →
      MemLp (fun x => (η r x * ‖ψ x‖) ^ 2) (ENNReal.ofReal p) μ)
    (hsob : ∀ r, 0 < r → r ≤ R₀ →
      (∫ x, ((η r x * ‖ψ x‖) ^ 2) ^ p ∂μ) ^ (1 / p) ≤ S * G r)
    (henergy : ∀ r, 0 < r → r ≤ R₀ →
      G r ≤ K / r ^ 2 * localMass (μ := μ) ψ x₀ (2 * r)) :
    InfiniteOrder.FlatAtZero (localMass (μ := μ) ψ x₀) := by
  have hlim := (density_factor_tendsto hpq.symm.pos
    (fun _ _ => ENNReal.toReal_nonneg) hdensity).const_mul (S * K)
  simp only [mul_zero] at hlim
  apply InfiniteOrder.flat_of_small_doubling
    (fun r _ => localMass_nonneg ψ x₀ r) (localMass_monotone x₀ hψ)
  intro δ hδ
  obtain ⟨R, hR, hsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (hlim.eventually (eventually_lt_nhds hδ))
  refine ⟨min R R₀, lt_min hR hR₀, ?_⟩
  intro r hr hrsmall
  have hrR : r ≤ R := hrsmall.trans (min_le_left _ _)
  have hrR₀ : r ≤ R₀ := hrsmall.trans (min_le_right _ _)
  have hc := hsmall (show r ∈ Ioc 0 R from ⟨hr, hrR⟩)
  change S * K * ((μ (nonzeroRegion ψ x₀ (2 * r))).toReal ^ (1 / q) / r ^ 2) < δ at hc
  have hrec := local_mass_recurrence hr hpq hS (hs (2 * r)) (hsfin (2 * r))
    (hηone r hr hrR₀) (hηsupp r hr hrR₀) (hloc r hr hrR₀)
    (hlp r hr hrR₀) (hsob r hr hrR₀) (henergy r hr hrR₀)
  calc
    localMass (μ := μ) ψ x₀ r ≤ _ := hrec
    _ ≤ δ * localMass (μ := μ) ψ x₀ (2 * r) :=
      mul_le_mul_of_nonneg_right (by simpa only [mul_div_assoc] using (le_of_lt hc))
        (localMass_nonneg ψ x₀ (2 * r))

end LocalMass

section DensityPoints

variable {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    {ψ : EuclideanSpace ℝ ι → H}

/-- Lebesgue differentiation gives the precise radius-normalized density
input used above at almost every zero of the Hilbert-valued field. -/
theorem ae_zero_density
    (hZ : MeasurableSet {x | ψ x ≠ 0}) :
    ∀ᵐ x ∂volume, ψ x = 0 →
      Tendsto (fun r => (volume (nonzeroRegion ψ x r)).toReal / r ^ (Fintype.card ι))
        (𝓝[>] 0) (𝓝 0) := by
  let E := EuclideanSpace ℝ ι
  let Z : Set E := {x | ψ x ≠ 0}
  let f : E → ℝ := Z.indicator (fun _ => 1)
  have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hZ
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1] with x hx
  intro hxzero
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [one_mul, Metric.mem_closedBall, dist_self]
    exact (show 0 < r from hr).le
  have hlim := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have hfx : f x = 0 := by simp [f, Z, hxzero]
  rw [hfx] at hlim
  let C : ℝ := volume.real (Metric.ball (0 : E) 1)
  have hC : 0 < C := ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne
  have havg (r : ℝ) : (⨍ y in Metric.closedBall x r, f y ∂volume) =
      volume.real (Z ∩ Metric.closedBall x r) / volume.real (Metric.closedBall x r) := by
    rw [setAverage_eq]
    change (volume.real (Metric.closedBall x r))⁻¹ •
      (∫ y in Metric.closedBall x r, Z.indicator (fun _ => (1 : ℝ)) y ∂volume) = _
    rw [integral_indicator_const 1 hZ]
    simp [Measure.real, Measure.restrict_apply hZ, div_eq_mul_inv, mul_comm, Z]
    exact Or.inl rfl
  have hclosed : Tendsto (fun r => volume.real (Z ∩ Metric.closedBall x r) / r ^ (Fintype.card ι))
      (𝓝[>] 0) (𝓝 0) := by
    have hh := hlim.mul_const C
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [havg, Measure.addHaar_real_closedBall volume x (show 0 ≤ r from hr.le)]
    simp only [finrank_euclideanSpace]
    change volume.real (Z ∩ Metric.closedBall x r) / (r ^ (Fintype.card ι) * C) * C = _
    field_simp [hC.ne']
  apply squeeze_zero' _ _ hclosed
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg (show 0 ≤ r from hr.le) _)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := hr
    apply div_le_div_of_nonneg_right _ (pow_nonneg hrpos.le _)
    apply measureReal_mono _ (lt_of_le_of_lt (measure_mono inter_subset_right) measure_closedBall_lt_top).ne
    intro y hy
    exact ⟨hy.2, Metric.ball_subset_closedBall hy.1⟩

/-- If the zero set has positive measure, a zero-density point exists in
every full-measure region, in particular in regular configuration space. -/
theorem exists_zero_density_point
    (hZ : MeasurableSet {x | ψ x ≠ 0})
    (hpositive : 0 < volume {x | ψ x = 0})
    {U : Set (EuclideanSpace ℝ ι)} (hU : ∀ᵐ x ∂volume, x ∈ U) :
    ∃ x ∈ U, ψ x = 0 ∧
      Tendsto (fun r => (volume (nonzeroRegion ψ x r)).toReal / r ^ (Fintype.card ι))
        (𝓝[>] 0) (𝓝 0) := by
  have hgood := hU.and (ae_zero_density hZ)
  have hex : ∃ x, ψ x = 0 ∧ x ∈ U ∧
      (ψ x = 0 → Tendsto (fun r => (volume (nonzeroRegion ψ x r)).toReal / r ^ (Fintype.card ι))
        (𝓝[>] 0) (𝓝 0)) := by
    by_contra h
    have hnull : ∀ᵐ x ∂volume, ψ x ≠ 0 := by
      filter_upwards [hgood] with x hx
      intro hz
      exact h ⟨x, hz, hx.1, hx.2⟩
    have : volume {x | ψ x = 0} = 0 := by simpa only [ae_iff, not_not] using hnull
    exact hpositive.ne' this
  obtain ⟨x, hxzero, hxU, hxdensity⟩ := hex
  exact ⟨x, hxU, hxzero, hxdensity hxzero⟩

end DensityPoints

end PfHk.UniqueContinuationDensity
