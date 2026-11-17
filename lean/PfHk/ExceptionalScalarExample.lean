import PfHk.PhysicalOpenRegularity
import PfHk.SmoothVectorTruncation
import GptLean.TransformationsPotentials
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! The singular scalar example in the exceptional-set remark.
A compact cutoff times |x|^(-3/2) is globally in L^(3/2) and locally
bounded off zero, but belongs to no local Lp class with p > 2 at zero.
The actual potential therefore satisfies the open-set regularity package
with zero vector potential while failing its global counterpart. -/

noncomputable section
namespace PfHk.ExceptionalScalarExample

open MeasureTheory Filter Set GptLean.PhysicalPairDuality
  GptLean.TransformationsPotentials GptLean.PhysicalSourceCoordinates
  PfHk.PhysicalOpenUCPCoefficients
open scoped ENNReal Topology

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000

def raw (η : Position → ℝ) (x : Position) : ℝ :=
  η x * ‖x‖ ^ (-(3 / 2 : ℝ))

theorem power_memLp_ball {p : ℝ} (hp : 0 < p) (hp2 : p < 2)
    (o : Position) (r : ℝ) :
    MemLp (fun x : Position => ‖x‖ ^ (-(3 / 2 : ℝ))) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball o r)) := by
  have hm : AEStronglyMeasurable (fun x : Position => ‖x‖ ^ (-(3 / 2 : ℝ))) volume :=
    (measurable_norm.pow_const _).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm.restrict
    (ENNReal.ofReal_ne_zero_iff.mpr hp) (by simp)).mp
  have hi : LocallyIntegrable (fun x : Position => ‖x‖ ^ (-(3 / 2 : ℝ) * p)) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := (3 / 2 : ℝ) * p)
      (by norm_num [Position, finrank_euclideanSpace]) ?_ ?_ ?_
    · simp only [Position, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
      linarith
    · exact ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),
          one_mul, neg_mul, le_refl]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hib := (hi.integrableOn_isCompact (isCompact_closedBall o r)).mono_set
    Metric.ball_subset_closedBall
  apply hib.congr
  filter_upwards with x
  rw [ENNReal.toReal_ofReal hp.le, Real.norm_rpow_of_nonneg (norm_nonneg x), norm_norm,
    ← Real.rpow_mul (norm_nonneg x)]

theorem raw_memLp_three_halves {η : Position → ℝ}
    (hη : Continuous η) (hηs : HasCompactSupport η) :
    MemLp (raw η) (3 / 2) volume := by
  obtain ⟨R, hR, hsupport⟩ := hηs.isBounded.exists_pos_norm_lt
  have hp := power_memLp_ball (p := (3 / 2 : ℝ)) (by norm_num) (by norm_num) 0 R
  have hexp : ENNReal.ofReal ((3 : ℝ) / 2) = (3 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hexp] at hp
  exact SmoothVectorTruncation.compact_mul_memLp 0 R η _ hη hηs
    (fun x hx => Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hsupport x hx)) hp

theorem raw_continuousOn_compl_zero {η : Position → ℝ} (hη : Continuous η) :
    ContinuousOn (raw η) ({0}ᶜ : Set Position) := by
  apply hη.continuousOn.mul
  apply continuous_norm.continuousOn.rpow_const
  intro x hx
  exact Or.inl (norm_ne_zero_iff.mpr hx)

/-- On every compact set away from zero the example belongs to every Lp,
including L-infinity. -/
theorem raw_memLp_compact_away_zero {η : Position → ℝ} (hη : Continuous η)
    (K : Set Position) (hK : IsCompact K) (hK0 : K ⊆ ({0}ᶜ : Set Position))
    (p : ℝ≥0∞) : MemLp (raw η) p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have hc := (raw_continuousOn_compl_zero hη).mono hK0
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (raw η) volume :=
    (hη.measurable.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have ht : MemLp (raw η) ∞ (volume.restrict K) :=
    memLp_top_of_bound hm.restrict M ((ae_restrict_mem hK.measurableSet).mono fun x hx => hM x hx)
  exact ht.mono_exponent le_top

/-- Every neighborhood of zero fails the local Lp requirement for p > 2. -/
theorem raw_not_memLp_ball {η : Position → ℝ} {r₀ p r : ℝ}
    (hr₀ : 0 < r₀) (hηone : ∀ x ∈ Metric.ball (0 : Position) r₀, η x = 1)
    (hp : 2 < p) (hr : 0 < r) :
    ¬ MemLp (raw η) (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 r)) := by
  intro hm
  let δ := min r r₀
  have hδ : 0 < δ := lt_min hr hr₀
  have hmδ := hm.mono_measure
    (Measure.restrict_mono (Metric.ball_subset_ball (min_le_left r r₀)) le_rfl)
  have hbase : MemLp (fun x : Position => ‖x‖ ^ (-(3 / 2 : ℝ))) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball 0 δ)) := by
    apply hmδ.ae_eq
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [raw, hηone x (Metric.ball_subset_ball (min_le_right r r₀) hx), one_mul]
  have hi := hbase.integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr (by linarith : 0 < p)) (by simp)
  have hpower : IntegrableOn (fun x : Position => ‖x‖ ^ (-(3 / 2 : ℝ) * p))
      (Metric.ball 0 δ) volume := by
    apply hi.congr
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p),
      Real.norm_rpow_of_nonneg (norm_nonneg x), norm_norm,
      ← Real.rpow_mul (norm_nonneg x)]
  have hradial := (integrableOn_fun_norm_addHaar (volume : Measure Position)
    (f := fun t : ℝ => t ^ (-(3 / 2 : ℝ) * p)) (r := δ)).mp hpower
  have hreal : IntegrableOn (fun t : ℝ => t ^ (2 - (3 / 2 : ℝ) * p)) (Ioo 0 δ) := by
    apply hradial.congr_fun _ measurableSet_Ioo
    intro t ht
    simp only [Position, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
      smul_eq_mul]
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht.1]
    congr 1
    ring
  have hexponent := (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp hreal
  linarith

def scalar (η : Position → ℝ) (hη : Continuous η) (hηs : HasCompactSupport η) :
    ScalarPotential :=
  ofParts 0 ((raw_memLp_three_halves hη hηs).toLp (raw η))

theorem scalar_ae (η : Position → ℝ) (hη : Continuous η) (hηs : HasCompactSupport η) :
    ((scalar η hη hηs).val : Position → ℝ) =ᵐ[volume] raw η := by
  filter_upwards [coeFn_ofParts (0 : Lp ℝ ∞ (volume : Measure Position))
      ((raw_memLp_three_halves hη hηs).toLp (raw η)),
    Lp.coeFn_zero ℝ ∞ (volume : Measure Position),
    (raw_memLp_three_halves hη hηs).coeFn_toLp] with x hs hz hr
  change (scalar η hη hηs).val x = _ at hs ⊢
  rw [hs, hz, hr, Pi.zero_apply, zero_add]

private theorem zero_vector_val (x : Position) : (0 : VectorPotential).val x = 0 := by
  change (0 : Position →ₘ[volume] Position) x = 0
  simp

/-- The example satisfies the article's coefficient regularity on punctured
space, with p = 3 and zero vector potential. -/
def regularityOn (η : Position → ℝ) (hη : Continuous η) (hηs : HasCompactSupport η) :
    RegularityOn (0 : VectorPotential) (scalar η hη hηs) ({0}ᶜ : Set Position) where
  exponent := 3
  exponent_gt_two := by norm_num
  divergence := fun _ => 0
  vector_local := by
    intro j K _ _
    simpa only [zero_vector_val, PiLp.zero_apply] using
      (MemLp.zero' : MemLp (fun _ : Position => (0 : ℝ)) 6 (volume.restrict K))
  scalar_local := by
    intro K hK hK0
    apply (raw_memLp_compact_away_zero hη K hK hK0 (ENNReal.ofReal 3)).ae_eq
    filter_upwards [ae_restrict_of_ae (scalar_ae η hη hηs)] with x hx
    exact hx.symm
  divergence_local := fun _ _ _ => MemLp.zero'
  weak_divergence := by
    intro φ _ _ _
    simp only [zero_vector_val, PiLp.zero_apply, zero_mul, integral_zero,
      Finset.sum_const_zero, neg_zero]

theorem scalar_not_memLp_ball (η : Position → ℝ) (hη : Continuous η)
    (hηs : HasCompactSupport η) {r₀ p r : ℝ} (hr₀ : 0 < r₀)
    (hηone : ∀ x ∈ Metric.ball (0 : Position) r₀, η x = 1)
    (hp : 2 < p) (hr : 0 < r) :
    ¬ MemLp ((scalar η hη hηs).val : Position → ℝ) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball 0 r)) := by
  intro hm
  exact raw_not_memLp_ball hr₀ hηone hp hr
    (hm.ae_eq (ae_restrict_of_ae (scalar_ae η hη hηs)))

/-- A smooth cutoff equal to one on the unit ball and zero outside radius two. -/
def cutoff : ContDiffBump (0 : Position) := ⟨1, 2, by norm_num, by norm_num⟩

def singularPotential : ScalarPotential := scalar cutoff cutoff.continuous cutoff.hasCompactSupport

def singularPotential_regularityOn :
    RegularityOn (0 : VectorPotential) singularPotential ({0}ᶜ : Set Position) :=
  regularityOn cutoff cutoff.continuous cutoff.hasCompactSupport

theorem singularPotential_not_memLp_ball {p r : ℝ} (hp : 2 < p) (hr : 0 < r) :
    ¬ MemLp (singularPotential.val : Position → ℝ) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball 0 r)) :=
  scalar_not_memLp_ball cutoff cutoff.continuous cutoff.hasCompactSupport (r₀ := 1)
    (by norm_num) (fun _ hx => cutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)) hp hr

theorem singularPotential_no_global_regularity :
    ¬ Nonempty (PhysicalFermionicCoefficients.Regularity (0 : VectorPotential) singularPotential) := by
  rintro ⟨h⟩
  exact singularPotential_not_memLp_ball h.exponent_gt_two (by norm_num : (0 : ℝ) < 1)
    (h.scalar_local 0 1 (by norm_num))

theorem punctured_isOpen : IsOpen ({0}ᶜ : Set Position) :=
  isClosed_singleton.isOpen_compl

theorem punctured_isConnected : IsConnected ({0}ᶜ : Set Position) :=
  isConnected_compl_singleton_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank (by norm_num [Position, finrank_euclideanSpace])) 0

theorem punctured_ae : ∀ᵐ x : Position ∂volume, x ∈ ({0}ᶜ : Set Position) := by
  exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : Position))

theorem singularPotential_memLp_three_halves :
    MemLp (singularPotential.val : Position → ℝ) (3 / 2) volume :=
  (raw_memLp_three_halves cutoff.continuous cutoff.hasCompactSupport).ae_eq
    (scalar_ae cutoff cutoff.continuous cutoff.hasCompactSupport).symm

end PfHk.ExceptionalScalarExample
