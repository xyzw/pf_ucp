import GptLean.PhysicalFockSoftTagVariance
import GptLean.PhysicalPhotonTraceForm
import GptLean.PhysicalPhotonMarginalMoments
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
The soft modes of `thm-many-electron-soft-purification`, and hard support
of a density matrix without soft photons.

For `κ > 0` the modes are the normalized indicators of the disjoint radial
shells `{κ/2 + κ 2^{-n-2} < |k| < κ/2 + κ 2^{-n-1}}` in one polarization,
as in `RepresentabilityAnnularModes`. Their supports are disjoint and lie
below `κ`, so they form a tag family below `κ`.

If the soft photon energy `∑ₙ ∫ ⟨vₙ(x), dΓ(ω 1_{ω<κ}) vₙ(x)⟩ dx` of a
spectral source vanishes, then every `vₙ(x)` is supported on hard photon
momenta. This uses that the dispersion is positive almost everywhere.
-/

noncomputable section

namespace GptLean.PhysicalSoftTagModes

open MeasureTheory Filter PhysicalFock PhysicalFock.SoftTag Gaussian PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Shells

/-- Decreasing endpoints from the outer radius towards half of it. -/
def endpoint (r : ℝ) (n : ℕ) : ℝ := r / 2 + (r / 2) * (1 / 2 : ℝ) ^ n

theorem endpoint_strictAnti {r : ℝ} (hr : 0 < r) : StrictAnti (endpoint r) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hp : 0 < (r / 2) * (1 / 2 : ℝ) ^ n := by positivity
  simp only [endpoint, pow_succ]
  nlinarith

theorem endpoint_lower {r : ℝ} (hr : 0 < r) (n : ℕ) : r / 2 < endpoint r n := by
  have hp : 0 < (r / 2) * (1 / 2 : ℝ) ^ n := by positivity
  exact lt_add_of_pos_right _ hp

theorem endpoint_upper {r : ℝ} (hr : 0 < r) (n : ℕ) : endpoint r n ≤ r := by
  have h := (endpoint_strictAnti hr).antitone (Nat.zero_le n)
  simpa [endpoint] using h

def shell (r : ℝ) (n : ℕ) : Set FieldSpace :=
  {k | endpoint r (n + 1) < ‖k‖ ∧ ‖k‖ < endpoint r n}

theorem shell_open (r : ℝ) (n : ℕ) : IsOpen (shell r n) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem shell_nonempty {r : ℝ} (hr : 0 < r) (n : ℕ) : (shell r n).Nonempty := by
  have hlt := endpoint_strictAnti hr (Nat.lt_succ_self n)
  have hlo := endpoint_lower hr (n + 1)
  let a := (endpoint r (n + 1) + endpoint r n) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨EuclideanSpace.single 0 a, ?_⟩
  have hn : ‖(EuclideanSpace.single 0 a : FieldSpace)‖ = a := by
    simp [Real.norm_eq_abs, abs_of_pos ha]
  change endpoint r (n + 1) < ‖(EuclideanSpace.single 0 a : FieldSpace)‖ ∧
    ‖(EuclideanSpace.single 0 a : FieldSpace)‖ < endpoint r n
  rw [hn]
  dsimp [a]
  constructor <;> linarith

theorem shell_subset {r : ℝ} (hr : 0 < r) (n : ℕ) {k : FieldSpace}
    (hk : k ∈ shell r n) : r / 2 < ‖k‖ ∧ ‖k‖ < r :=
  ⟨(endpoint_lower hr (n + 1)).trans hk.1, hk.2.trans_le (endpoint_upper hr n)⟩

theorem shell_pairwiseDisjoint {r : ℝ} (hr : 0 < r) :
    Pairwise (fun n m => Disjoint (shell r n) (shell r m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro k hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have he := (endpoint_strictAnti hr).antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (he.trans hn.1.le)) hm.2
  · have he := (endpoint_strictAnti hr).antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (he.trans hm.1.le)) hn.2

theorem shell_measure_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < volume (shell r n) := (shell_open r n).measure_pos volume (shell_nonempty hr n)

theorem shell_measure_ne_top {r : ℝ} (hr : 0 < r) (n : ℕ) :
    volume (shell r n) ≠ ∞ := by
  apply ne_of_lt
  apply (Metric.isBounded_ball.subset (t := Metric.ball (0 : FieldSpace) r) ?_).measure_lt_top
  intro k hk
  simpa only [Metric.mem_ball, dist_zero_right] using (shell_subset hr n hk).2

/-- One polarization for every mode. -/
def cell (r : ℝ) (n : ℕ) : Set PhotonMode := shell r n ×ˢ {(0 : Fin 2)}

theorem cell_measurable (r : ℝ) (n : ℕ) : MeasurableSet (cell r n) :=
  (shell_open r n).measurableSet.prod (measurableSet_singleton 0)

theorem cell_measure (r : ℝ) (n : ℕ) : photonMeasure (cell r n) = volume (shell r n) := by
  simp [photonMeasure, cell, Measure.prod_prod]

theorem cell_measure_ne_top {r : ℝ} (hr : 0 < r) (n : ℕ) :
    photonMeasure (cell r n) ≠ ∞ := by
  rw [cell_measure]
  exact shell_measure_ne_top hr n

def indicator {r : ℝ} (hr : 0 < r) (n : ℕ) : Lp ℂ 2 photonMeasure :=
  indicatorConstLp 2 (cell_measurable r n) (cell_measure_ne_top hr n) 1

theorem indicator_ne_zero {r : ℝ} (hr : 0 < r) (n : ℕ) : indicator hr n ≠ 0 := by
  have hp : 0 < photonMeasure.real (cell r n) :=
    ENNReal.toReal_pos (by rw [cell_measure]; exact (shell_measure_pos hr n).ne')
      (cell_measure_ne_top hr n)
  apply norm_pos_iff.mp
  rw [indicator, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul]
  exact Real.rpow_pos_of_pos hp _

/-- The normalized indicator of a shell. -/
def mode {r : ℝ} (hr : 0 < r) (n : ℕ) : Lp ℂ 2 photonMeasure :=
  (‖indicator hr n‖⁻¹ : ℂ) • indicator hr n

theorem mode_norm {r : ℝ} (hr : 0 < r) (n : ℕ) : ‖mode hr n‖ = 1 :=
  norm_smul_inv_norm (indicator_ne_zero hr n)

theorem mode_support {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∀ᵐ p ∂photonMeasure, p ∉ cell r n → mode hr n p = 0 := by
  filter_upwards [Lp.coeFn_smul (‖indicator hr n‖⁻¹ : ℂ) (indicator hr n),
    @indicatorConstLp_coeFn_notMem _ _ _ 2 photonMeasure _ (cell r n)
      (cell_measurable r n) (cell_measure_ne_top hr n) (1 : ℂ)] with p hs hi
  intro hp
  rw [mode, hs]
  change (‖indicator hr n‖⁻¹ : ℂ) • indicator hr n p = 0
  rw [show indicator hr n p = 0 from hi hp, smul_zero]

theorem mode_disjoint {r : ℝ} (hr : 0 < r) {n m : ℕ} (hnm : n ≠ m) :
    ∀ᵐ p ∂photonMeasure, mode hr n p = 0 ∨ mode hr m p = 0 := by
  filter_upwards [mode_support hr n, mode_support hr m] with p hn hm
  by_cases hp : p ∈ cell r n
  · right
    apply hm
    intro hpm
    exact Set.disjoint_left.mp (shell_pairwiseDisjoint hr hnm) hp.1 hpm.1
  · left
    exact hn hp

end Shells

theorem inner_eq_zero_of_disjoint (F G : Lp ℂ 2 photonMeasure)
    (h : ∀ᵐ p ∂photonMeasure, F p = 0 ∨ G p = 0) : ⟪F, G⟫_ℂ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [h] with p hp
  rcases hp with hp | hp
  · change ⟪F p, G p⟫_ℂ = 0
    rw [hp, inner_zero_left]
  · change ⟪F p, G p⟫_ℂ = 0
    rw [hp, inner_zero_right]

/-- **The shell modes form a tag family below `κ`.** -/
theorem tagFamily {κ : ℝ} (hκ : 0 < κ) : TagFamily κ (mode hκ) where
  soft n := by
    apply (MomentumSplit.mem_supported_iff photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) (mode hκ n)).mpr
    filter_upwards [mode_support hκ n] with p hp hs
    apply hp
    intro hc
    exact hs (shell_subset hκ n hc.1).2
  unit n := mode_norm hκ n
  orthogonal n m hnm := inner_eq_zero_of_disjoint _ _ (mode_disjoint hκ hnm)
  weighted R n m hnm := by
    apply inner_eq_zero_of_disjoint
    filter_upwards [mode_disjoint hκ hnm,
      oneMultiplier_ae (R : ℝ) (Nat.cast_nonneg R) (mode hκ m)] with p hp hM
    rcases hp with hp | hp
    · exact Or.inl hp
    · right
      rw [hM, hp, smul_zero]

section HardSupport

/-- **Zero soft moment forces hard support.** -/
theorem hardSupported_of_photonMoment (κ : ℝ) (u : PhotonFock)
    (h : photonMoment (NormalPhoton.softWeight κ) u = 0) : HardSupported κ u := by
  intro n
  have hn : sectorPhotonMoment (NormalPhoton.softWeight κ) n (u n) = 0 :=
    ENNReal.tsum_eq_zero.mp h n
  unfold sectorPhotonMoment at hn
  have hmeas : AEMeasurable (fun k : Fin n → PhotonMode =>
      (∑ i, NormalPhoton.softWeight κ (k i)) * ENNReal.ofReal (‖(u n).val k‖ ^ 2))
      (SectorMeasure photonMeasure n) :=
    (Finset.measurable_sum _ fun i _ =>
      (NormalPhoton.softWeight_measurable κ).comp (measurable_pi_apply i)).aemeasurable.mul
      ((Lp.stronglyMeasurable (u n).val).measurable.norm.pow_const 2).ennreal_ofReal.aemeasurable
  have hz := (lintegral_eq_zero_iff' hmeas).mp hn
  have hpos : ∀ᵐ k ∂SectorMeasure photonMeasure n, ∀ i, 0 < NormalPhoton.frequency (k i) :=
    ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => photonMeasure)
      (i := i)).eventually (p := fun p => 0 < NormalPhoton.frequency p)
      NormalPhoton.frequency_positive
  filter_upwards [hz, hpos] with k hk hk' hne i
  have hpos2 : ENNReal.ofReal (‖(u n).val k‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hsum : ∑ i, NormalPhoton.softWeight κ (k i) = 0 :=
    (mul_eq_zero.mp hk).resolve_right hpos2
  have hi : NormalPhoton.softWeight κ (k i) = 0 :=
    (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  by_contra hle
  have hlt := lt_of_not_ge hle
  have hmem : k i ∈ {p : PhotonMode | NormalPhoton.frequency p < κ} := hlt
  rw [NormalPhoton.softWeight, Set.indicator_of_mem hmem, ENNReal.ofReal_eq_zero] at hi
  exact absurd hi (not_le.mpr (hk' i))

theorem measurable_photonMoment {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (q : PhotonMode → ℝ≥0∞) (hq : Measurable q) (v : Lp PhotonFock 2 μ) :
    Measurable (fun x => photonMoment q (v x)) := by
  have hm (M : ℕ) : Measurable (fun x => ENNReal.ofReal
      (⟪v x, (cappedWeight q hq M).operator (Nat.cast_nonneg M) (v x)⟫_ℂ).re) :=
    (Complex.continuous_re.comp_stronglyMeasurable ((Lp.stronglyMeasurable v).inner
      (((cappedWeight q hq M).operator (Nat.cast_nonneg M)).continuous.comp_stronglyMeasurable
        (Lp.stronglyMeasurable v)))).measurable.ennreal_ofReal
  have he : (fun x => photonMoment q (v x)) = fun x => ⨆ M : ℕ, ENNReal.ofReal
      (⟪v x, (cappedWeight q hq M).operator (Nat.cast_nonneg M) (v x)⟫_ℂ).re :=
    funext fun x => (cappedWeight_recovery q hq (v x)).symm
  rw [he]
  exact Measurable.iSup hm

/-- **A spectral source without soft photon energy is hard.** -/
theorem source_hardSupported (B : StandardNormalTraceBackground)
    {X : Type} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ] (κ : ℝ)
    {v : ℕ → Lp PhotonFock 2 μ} {x : B.Trace (Lp PhotonFock 2 μ)}
    (hv : HasSum (fun n => (B.realization (Lp PhotonFock 2 μ)).rank.rankOne (v n)) x)
    (h0 : (NormalPhoton.softEnergyForm B.normal (B.realization PhotonFock).functional κ).expectation
      (PhysicalPhotonMarginal.marginal B μ x) = 0) (n : ℕ) :
    ∀ᵐ y ∂μ, HardSupported κ (v n y) := by
  have hs := PhysicalPhotonMarginal.fullMomentumForm_source B μ (NormalPhoton.softWeight κ)
    (NormalPhoton.softWeight_measurable κ) hv
  have h0' : (PhysicalPhotonMarginal.fullMomentumForm B μ (NormalPhoton.softWeight κ)
      (NormalPhoton.softWeight_measurable κ)).expectation x = 0 := h0
  have h1 : (∑' n, ∫⁻ y, photonMoment (NormalPhoton.softWeight κ) (v n y) ∂μ) = 0 :=
    hs.symm.trans h0'
  have h2 := ENNReal.tsum_eq_zero.mp h1 n
  have h3 := (lintegral_eq_zero_iff (measurable_photonMoment _
    (NormalPhoton.softWeight_measurable κ) (v n))).mp h2
  filter_upwards [h3] with y hy
  exact hardSupported_of_photonMoment κ (v n y) hy

end HardSupport

end GptLean.PhysicalSoftTagModes
