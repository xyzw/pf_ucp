import GptLean.PhysicalFockMultipliers
import GptLean.PhysicalPhotonMoments
import GptLean.PhysicalNormalTrace
import GptLean.PositiveForm
import GptLean.PhotonLocalizationChannelMeasurement
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
Every nonnegative measurable one-photon weight defines an actual positive
normal trace form on the fixed symmetric momentum Fock space. Its bounded
operators multiply every sector by the capped sum of the one-photon weights.
Monotone convergence identifies their supremum with the occupation moment,
including infinite moments and arbitrary positive spectral decompositions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel RemovalState PhysicalNormalTrace
open scoped ENNReal InnerProductSpace

variable (q : PhotonMode → ℝ≥0∞) (hq : Measurable q)

def sectorWeight (n : ℕ) (k : Fin n → PhotonMode) : ℝ≥0∞ := ∑ i, q (k i)

include hq in
theorem sectorWeight_measurable (n : ℕ) : Measurable (sectorWeight q n) :=
  Finset.measurable_sum _ fun i _ => hq.comp (measurable_pi_apply i)

theorem sectorWeight_permutation (n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    sectorWeight q n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      sectorWeight q n k := by
  unfold sectorWeight
  rw [← Equiv.sum_comp π (fun i => q
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) i))]
  simp only [MeasurableEquiv.piCongrLeft_apply_apply]

def cappedSectorWeight (M n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  (min (M : ℝ≥0∞) (sectorWeight q n k)).toReal

theorem cappedSectorWeight_nonneg (M n : ℕ) (k : Fin n → PhotonMode) :
    0 ≤ cappedSectorWeight q M n k := ENNReal.toReal_nonneg

theorem cappedSectorWeight_bound (M n : ℕ) (k : Fin n → PhotonMode) :
    |cappedSectorWeight q M n k| ≤ M := by
  rw [abs_of_nonneg (cappedSectorWeight_nonneg q M n k)]
  exact (ENNReal.toReal_mono (by simp) (min_le_left (M : ℝ≥0∞) _)).trans_eq (by simp)

theorem cappedSectorWeight_ofReal (M n : ℕ) (k : Fin n → PhotonMode) :
    ENNReal.ofReal (cappedSectorWeight q M n k) = min (M : ℝ≥0∞) (sectorWeight q n k) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_left _ _))

theorem cappedSectorWeight_mono (n : ℕ) (k : Fin n → PhotonMode) :
    Monotone (fun M => cappedSectorWeight q M n k) := by
  intro M L hML
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (min_le_left _ _))
    (min_le_min_right _ (by exact_mod_cast hML))

def cappedWeight (M : ℕ) : BoundedSymmetricWeight photonMeasure (M : ℝ) where
  value := cappedSectorWeight q M
  measurable n := (measurable_const.min (sectorWeight_measurable q hq n)).ennreal_toReal.aestronglyMeasurable
  bound := cappedSectorWeight_bound q M
  symmetric n π k := by simp only [cappedSectorWeight, sectorWeight_permutation]

theorem cappedWeight_ofReal (M n : ℕ) (k : Fin n → PhotonMode) :
    ENNReal.ofReal ((cappedWeight q hq M).value n k) = min (M : ℝ≥0∞) (sectorWeight q n k) :=
  cappedSectorWeight_ofReal q M n k

private theorem iSup_cap (x : ℝ≥0∞) : (⨆ M : ℕ, min (M : ℝ≥0∞) x) = x := by
  rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]

private theorem iSup_tsum_of_monotone (f : ℕ → ℕ → ℝ≥0∞)
    (hf : ∀ n, Monotone (fun M => f M n)) :
    (⨆ M, ∑' n, f M n) = ∑' n, ⨆ M, f M n := by
  simpa only [lintegral_count] using
    (lintegral_iSup (μ := Measure.count) (fun M => measurable_of_countable (f M))
      (fun M L hML n => hf n hML)).symm

/-- Capping the actual sector momentum multiplier recovers its full form. -/
theorem cappedWeight_recovery (u : PhotonFock) :
    (⨆ M, ENNReal.ofReal (⟪u, (cappedWeight q hq M).operator (Nat.cast_nonneg M) u⟫_ℂ).re) =
      photonMoment q u := by
  simp_rw [(cappedWeight q hq _).operator_inner_ofReal (Nat.cast_nonneg _)
    (cappedSectorWeight_nonneg q _), cappedWeight_ofReal]
  rw [iSup_tsum_of_monotone (fun M n => ∫⁻ k, min (M : ℝ≥0∞) (sectorWeight q n k) *
    ENNReal.ofReal (‖(u n).val k‖ ^ 2) ∂SectorMeasure photonMeasure n)
    (fun n M L hML => lintegral_mono fun k =>
      mul_le_mul_of_nonneg_right (min_le_min_right _ (by exact_mod_cast hML)) bot_le)]
  apply tsum_congr
  intro n
  have hm (M : ℕ) : AEMeasurable (fun k => min (M : ℝ≥0∞) (sectorWeight q n k) *
      ENNReal.ofReal (‖(u n).val k‖ ^ 2)) (SectorMeasure photonMeasure n) :=
    (measurable_const.min (sectorWeight_measurable q hq n)).aemeasurable.mul
      (((Lp.aestronglyMeasurable (u n).val).norm.pow 2).aemeasurable.ennreal_ofReal)
  rw [← lintegral_iSup' hm (ae_of_all _ fun k M L hML =>
    mul_le_mul_of_nonneg_right (min_le_min_right _ (by exact_mod_cast hML)) bot_le)]
  apply lintegral_congr
  intro k
  rw [← ENNReal.iSup_mul, iSup_cap]
  rfl

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}

def momentumTruncation (F : NormalFunctionalData R) (M : ℕ) : T →L[ℝ] ℝ :=
  Complex.reCLM.comp (((ContinuousLinearMap.apply ℂ ℂ
    ((cappedWeight q hq M).operator (Nat.cast_nonneg M))).restrictScalars ℝ).comp F.repr)

omit [CompleteSpace T] in
@[simp] theorem momentumTruncation_rankOne (F : NormalFunctionalData R) (M : ℕ) (u : PhotonFock) :
    momentumTruncation q hq F M (R.rankOne u) =
      (⟪u, (cappedWeight q hq M).operator (Nat.cast_nonneg M) u⟫_ℂ).re := by
  change (F.repr (R.rankOne u) _).re = _
  rw [F.rankOne]

def secondQuantizedPositiveForm (normal : NormalTraceData R) (F : NormalFunctionalData R) :
    PositiveForm (positiveTrace normal F) where
  truncation := momentumTruncation q hq F
  nonneg M x hx := normal.observable_nonneg _ (fun u => by
    rw [momentumTruncation_rankOne]
    exact (cappedWeight q hq M).operator_inner_nonneg (Nat.cast_nonneg M)
      (cappedSectorWeight_nonneg q M) u) hx
  monotone x hx M L hML := by
    have h := normal.observable_nonneg (momentumTruncation q hq F L - momentumTruncation q hq F M)
      (fun u => by
        simp only [sub_apply, momentumTruncation_rankOne]
        exact sub_nonneg.mpr ((cappedWeight q hq M).operator_inner_mono (cappedWeight q hq L)
          (Nat.cast_nonneg M) (Nat.cast_nonneg L) (fun n k => cappedSectorWeight_mono q n k hML) u)) hx
    exact sub_nonneg.mp h

/-- The normal form is evaluated on the actual Fock vector, with no assumed rank-one moment law. -/
theorem secondQuantizedPositiveForm_rankOne (normal : NormalTraceData R) (F : NormalFunctionalData R)
    (u : PhotonFock) :
    (secondQuantizedPositiveForm q hq normal F).expectation (R.rankOne u) = photonMoment q u := by
  change (⨆ M, ENNReal.ofReal (momentumTruncation q hq F M (R.rankOne u))) = _
  simp only [momentumTruncation_rankOne]
  exact cappedWeight_recovery q hq u

theorem secondQuantizedPositiveForm_source (normal : NormalTraceData R) (F : NormalFunctionalData R)
    {v : ℕ → PhotonFock} {x : T} (hv : HasSum (fun n => R.rankOne (v n)) x) :
    (secondQuantizedPositiveForm q hq normal F).expectation x = ∑' n, photonMoment q (v n) := by
  rw [← hv.tsum_eq, (secondQuantizedPositiveForm q hq normal F).expectation_tsum hv.summable
    (fun n => R.rankOne_positive (v n))]
  exact tsum_congr fun n => secondQuantizedPositiveForm_rankOne q hq normal F (v n)

/-- Every decomposition of the same normal state gives its same occupation moment. -/
theorem secondQuantizedPositiveForm_occupation (normal : NormalTraceData R) (F : NormalFunctionalData R)
    {v : ℕ → PhotonFock} {x : T} (hv : HasSum (fun n => R.rankOne (v n)) x) :
    (secondQuantizedPositiveForm q hq normal F).expectation x =
      ∫⁻ p, q p * ensemblePhotonDensity v p ∂photonMeasure := by
  rw [secondQuantizedPositiveForm_source q hq normal F hv, ensemblePhotonDensity_moment q hq]

/-- The momentum density is independent of the chosen positive source,
including states with infinite expected photon number. -/
theorem ensemblePhotonDensity_independent (normal : NormalTraceData R) (F : NormalFunctionalData R)
    {v w : ℕ → PhotonFock} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x)
    (hw : HasSum (fun n => R.rankOne (w n)) x) :
    ensemblePhotonDensity v =ᵐ[photonMeasure] ensemblePhotonDensity w := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (ensemblePhotonDensity_measurable v) (ensemblePhotonDensity_measurable w)
  intro s hs _
  let q : PhotonMode → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hq : Measurable q := measurable_const.indicator hs
  have he := (secondQuantizedPositiveForm_occupation q hq normal F hv).symm.trans
    (secondQuantizedPositiveForm_occupation q hq normal F hw)
  have hi (f : PhotonMode → ℝ≥0∞) : (fun p => q p * f p) = s.indicator f := by
    funext p
    simp only [q, ← Set.indicator_mul_left, one_mul]
  simpa only [hi, lintegral_indicator hs] using he

end GptLean.PhysicalFock
