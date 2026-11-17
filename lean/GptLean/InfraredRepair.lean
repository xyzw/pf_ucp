import GptLean.AttainmentConstruction
import GptLean.SoftRemoval

/-!
The local repaired-cluster costs imply the infrared gain used in Theorem 4.8.
The cutoff scale and gain constant are chosen from the actual finite infrared
integrals. The state construction, its local form estimates and the photon
marginal identity remain explicit inputs. No soft-gain inequality is assumed.
-/

namespace GptLean.InfraredRepair

open Filter Topology MeasureTheory Set
open scoped ENNReal

/-- The optimized removal estimate implies the gain after a stronger,
but available, infrared smallness choice. -/
theorem gain_of_optimized_removal {energy repaired soft C e a b κ : ℝ}
    (hs : 0 ≤ soft) (hC : 0 ≤ C) (he : 0 ≤ e)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : C * e ^ 2 * a ^ 2 ≤ 1 / 4) (hbound : a ^ 2 ≤ 1)
    (hrepair : repaired ≤ energy - soft +
      C * SoftPurification.removalError e κ a b soft) :
    repaired ≤ energy - soft / 2 +
      (C + C * e / 2 + C ^ 2 * e ^ 2) * κ ^ 2 +
      (2 * C * e ^ 2 + C * e / 2) * b ^ 2 := by
  apply Attainment.raw_fixed_scale_soft_energy_gain hs hC he ha hb hκ hsmall hbound
  have hk2 : κ ^ 2 ≤ 1 := by nlinarith
  have hinner : 0 ≤ a ^ 2 * soft + b ^ 2 := by positivity
  have hscale : e ^ 2 * κ ^ 2 * (a ^ 2 * soft + b ^ 2) ≤
      e ^ 2 * (a ^ 2 * soft + b ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hk2 (mul_nonneg (sq_nonneg e) hinner)]
  have hscaled := mul_le_mul_of_nonneg_left hscale hC
  unfold SoftPurification.removalError at hrepair
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {ω : Ω → ℝ} {w : Ω → ℝ≥0∞}

/-- A common cutoff and constant work for all state energies and soft
energies. Their existence follows from the actual weighted cutoff decay. -/
theorem exists_profile_gain (hω : Measurable ω) (hpos : ∀ᵐ x ∂μ, 0 < ω x)
    (hA : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤)
    {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e) :
    ∃ κ₀ G : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 ∧ 0 ≤ G ∧
      ∀ κ energy repaired soft : ℝ, 0 < κ → κ ≤ κ₀ → 0 ≤ soft →
        repaired ≤ energy - soft + C * SoftPurification.removalError e κ
          (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)) soft →
        repaired ≤ energy - soft / 2 + G * (κ ^ 2 + CutoffProfile.bsq μ ω w κ) := by
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (CutoffProfile.eventually_fixed_scale_small hω hpos hA C e)
  let K := min δ 1
  let G := max (C + C * e / 2 + C ^ 2 * e ^ 2) (2 * C * e ^ 2 + C * e / 2)
  refine ⟨K, G, lt_min hδ zero_lt_one, min_le_right _ _, ?_, ?_⟩
  · exact (by positivity : 0 ≤ C + C * e / 2 + C ^ 2 * e ^ 2).trans (le_max_left _ _)
  · intro κ energy repaired soft hκ hκK hs hrepair
    have hκδ : κ ≤ δ := hκK.trans (min_le_left _ _)
    obtain ⟨hsmallκ, hboundκ⟩ := hsmall ⟨hκ, hκδ⟩
    have hg := gain_of_optimized_removal hs hC he (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hκ.le (hκK.trans (min_le_right _ _)) hsmallκ hboundκ hrepair
    rw [Real.sq_sqrt (CutoffProfile.bsq_nonneg κ)] at hg
    have h1 := mul_le_mul_of_nonneg_right
      (le_max_left (C + C * e / 2 + C ^ 2 * e ^ 2) (2 * C * e ^ 2 + C * e / 2))
      (sq_nonneg κ)
    have h2 := mul_le_mul_of_nonneg_right
      (le_max_right (C + C * e / 2 + C ^ 2 * e ^ 2) (2 * C * e ^ 2 + C * e / 2))
      (CutoffProfile.bsq_nonneg (μ := μ) (ω := ω) (w := w) κ)
    dsimp [G]
    nlinarith

variable {State Pair : Type*}

/-- Trace-to-momentum moment data, separated from any repair theorem. -/
structure InfraredMoments (A : DFT.StateModel State Pair)
    (number : State → ℝ≥0∞) (μ : Measure Ω) (ω : Ω → ℝ) (w : Ω → ℝ≥0∞) where
  dispersion_measurable : Measurable ω
  dispersion_positive : ∀ᵐ x ∂μ, 0 < ω x
  cutoff_measurable : Measurable w
  cutoff_finite : ∫⁻ x, w x ∂μ < ⊤
  weighted_finite : ∫⁻ x, w x * ENNReal.ofReal (1 / ω x) ∂μ < ⊤
  photonDensity : State → Ω → ℝ≥0∞
  hardNumber : State → ℝ → ℝ
  softEnergy : State → ℝ → ℝ
  radiationEnergy : State → ℝ
  moments : ∀ s, HardLayerCake.HasPhotonDensity μ ω (photonDensity s)
    (hardNumber s) (softEnergy s) (radiationEnergy s)
  radiation_le : ∀ s, radiationEnergy s ≤ A.energy s
  number_eq : ∀ s, number s = ∫⁻ x, photonDensity s x ∂μ

/-- Finite radiation energy proves that every positive-cutoff hard moment
is finite. Thus the real hard-number field retains the whole moment. -/
theorem InfraredMoments.ofReal_hardNumber_eq {A : DFT.StateModel State Pair}
    {number : State → ℝ≥0∞} (P : InfraredMoments A number μ ω w)
    (s : State) {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal (P.hardNumber s κ) =
      ∫⁻ x in {x | κ ≤ ω x}, P.photonDensity s x ∂μ := by
  have hset : MeasurableSet {x | κ ≤ ω x} :=
    measurableSet_le measurable_const P.dispersion_measurable
  have hmeas : Measurable (fun x => ENNReal.ofReal (ω x) * P.photonDensity s x) :=
    P.dispersion_measurable.ennreal_ofReal.mul (P.moments s).measurable
  have hb : (∫⁻ x in {x | κ ≤ ω x}, P.photonDensity s x ∂μ) ≤
      ENNReal.ofReal (1 / κ) *
        ∫⁻ x, ENNReal.ofReal (ω x) * P.photonDensity s x ∂μ := by
    rw [← lintegral_const_mul _ hmeas, ← lintegral_indicator hset]
    refine lintegral_mono fun x => ?_
    by_cases hx : κ ≤ ω x
    · rw [indicator_of_mem (by exact hx), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / κ)]
      have hratio : 1 ≤ 1 / κ * ω x := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hκ]
        simpa using hx
      calc P.photonDensity s x = 1 * P.photonDensity s x := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (ENNReal.one_le_ofReal.mpr hratio) le_rfl
    · rw [indicator_of_notMem (by exact hx)]
      exact bot_le
  have hfin : (∫⁻ x in {x | κ ≤ ω x}, P.photonDensity s x ∂μ) < ⊤ :=
    hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (P.moments s).finite)
  rw [(P.moments s).numHard_eq, ENNReal.ofReal_toReal hfin.ne]

/-- Local IMS and repaired-cluster estimates construct the entire gain
interface. The hard-vacuum marginal implication is the explicit Fock
identification used to transfer number to the same repaired output. -/
theorem exists_data_of_localized {A : DFT.StateModel State Pair}
    {number : State → ℝ≥0∞} {PhotonMarginal : Type*}
    (P : InfraredMoments A number μ ω w)
    (marginal : ℝ → State → PhotonMarginal)
    (target : State → ℝ → PhotonMarginal) {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hlocal : ∀ s κ R, 0 < κ → κ ≤ 1 → 1 ≤ R → κ * R ≤ 1 →
      SoftRemoval.LocalizedOutput A s (marginal κ) (target s κ) (P.softEnergy s κ)
        C e κ R (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)))
    (hmarginal : ∀ s κ r, 0 < κ → marginal κ r = target s κ →
      number r ≤ ENNReal.ofReal (P.hardNumber s κ)) :
    Nonempty (AttainmentConstruction.InfraredRepairData A number μ ω w) := by
  obtain ⟨κ₀, G, hκ₀, hκ₀1, hG, hgain⟩ := exists_profile_gain
    P.dispersion_measurable P.dispersion_positive P.weighted_finite
    (show 0 ≤ 3 * C by positivity) he
  refine ⟨{
    κ₀ := κ₀
    C := G
    κ₀_pos := hκ₀
    C_nonneg := hG
    dispersion_measurable := P.dispersion_measurable
    dispersion_positive := P.dispersion_positive
    cutoff_measurable := P.cutoff_measurable
    cutoff_finite := P.cutoff_finite
    weighted_finite := P.weighted_finite
    photonDensity := P.photonDensity
    hardNumber := P.hardNumber
    softEnergy := P.softEnergy
    radiationEnergy := P.radiationEnergy
    moments := P.moments
    radiation_le := P.radiation_le
    number_eq := P.number_eq
    repair := ?_ }⟩
  intro s κ hκ hκK
  have hκ1 := hκK.trans hκ₀1
  have hs : 0 ≤ P.softEnergy s κ := by
    rw [(P.moments s).Esoft_eq]
    exact ENNReal.toReal_nonneg
  obtain ⟨r, hrpair, hrmarginal, hrenergy⟩ := SoftRemoval.optimized_output s
    (marginal κ) (target s κ) hC he hκ hκ1 hs (hlocal s κ · hκ hκ1)
  exact ⟨r, hrpair, hgain κ (A.energy s) (A.energy r) (P.softEnergy s κ)
    hκ hκK hs hrenergy, hmarginal s κ r hκ hrmarginal⟩

/-- A noncomputable constructor from the local state estimates. -/
noncomputable def dataOfLocalized {A : DFT.StateModel State Pair}
    {number : State → ℝ≥0∞} {PhotonMarginal : Type*}
    (P : InfraredMoments A number μ ω w)
    (marginal : ℝ → State → PhotonMarginal)
    (target : State → ℝ → PhotonMarginal) {C e : ℝ} (hC : 0 ≤ C) (he : 0 ≤ e)
    (hlocal : ∀ s κ R, 0 < κ → κ ≤ 1 → 1 ≤ R → κ * R ≤ 1 →
      SoftRemoval.LocalizedOutput A s (marginal κ) (target s κ) (P.softEnergy s κ)
        C e κ R (Real.sqrt (CutoffProfile.asq μ ω w κ))
          (Real.sqrt (CutoffProfile.bsq μ ω w κ)))
    (hmarginal : ∀ s κ r, 0 < κ → marginal κ r = target s κ →
      number r ≤ ENNReal.ofReal (P.hardNumber s κ)) :
    AttainmentConstruction.InfraredRepairData A number μ ω w :=
  Classical.choice (exists_data_of_localized P marginal target hC he hlocal hmarginal)

end GptLean.InfraredRepair
