import GptLean.PhysicalEnsembleSource
import GptLean.PhotonLocalizationPosition
import GptLean.RemovalPhysicalPair

/-!
The constructed ensemble source has the scalar multiplication traces of
the original mixed state. Its configuration density is independent of
the positive rank-one decomposition. No density observable formula for
the mixed state is assumed.
-/

noncomputable section

namespace GptLean.PhysicalEnsembleSource

open MeasureTheory Filter Repair PhotonLocalization PhotonLocalizationChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
theorem ensemble_squares_summable_ae (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) :
    ∀ᵐ x ∂μ, Summable (fun n => ‖v n x‖ ^ 2) := by
  filter_upwards [ensemble_represents_ae v hv] with x hx
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble v hv x))).mp (Lp.memLp (ensemble v hv x))
  have hs := integrable_count_iff.mp hi
  simpa only [norm_pow, norm_norm, hx] using hs

omit [CompleteSpace H] in
theorem ensemble_tested_mass_hasSum (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) (a : X → ℝ)
    (ha : AEStronglyMeasurable a μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    HasSum (fun n => ∫ x, a x * ‖v n x‖ ^ 2 ∂μ)
      (∫ x, a x * ‖ensemble v hv x‖ ^ 2 ∂μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble v hv))).mp (Lp.memLp (ensemble v hv))
  have hs := ensemble_squares_summable_ae v hv
  have hn := ensemble_norm_sq_ae v hv
  apply hasSum_integral_of_dominated_convergence (fun n x => C * ‖v n x‖ ^ 2)
  · intro n
    exact ha.mul ((Lp.aestronglyMeasurable (v n)).norm.pow 2)
  · intro n
    filter_upwards [hb] with x hx
    simpa only [norm_mul, norm_pow, norm_norm] using
      mul_le_mul_of_nonneg_right hx (sq_nonneg ‖v n x‖)
  · filter_upwards [hs] with x hx
    exact hx.mul_left C
  · have heq : (fun x => C * ‖ensemble v hv x‖ ^ 2) =ᵐ[μ]
        (fun x => ∑' n, C * ‖v n x‖ ^ 2) := by
      filter_upwards [hn] with x hx
      rw [hx, tsum_mul_left]
    exact (hi.const_mul C).congr heq
  · filter_upwards [hs, hn] with x hx hnx
    rw [hnx]
    exact hx.hasSum.mul_left (a x)

omit [SFinite μ] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem scalar_trace_rankOne (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, |a x| ≤ C) (v : Lp H 2 μ) :
    (inner ℂ v (realL2Multiplier a ha C hb v)).re = ∫ x, a x * ‖v x‖ ^ 2 ∂μ := by
  rw [L2.inner_def]
  have hre := Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (𝕜 := ℂ) v (realL2Multiplier a ha C hb v))
  change (∫ z, inner ℂ (v z) (realL2Multiplier a ha C hb v z) ∂μ).re = _
  rw [← show (∫ z, (inner ℂ (v z) (realL2Multiplier a ha C hb v z)).re ∂μ) =
    (∫ z, inner ℂ (v z) (realL2Multiplier a ha C hb v z) ∂μ).re from hre]
  apply integral_congr_ae
  filter_upwards [realL2Multiplier_apply a ha C hb v] with x hx
  rw [hx, inner_smul_right_eq_smul]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData (Lp H 2 μ) T}

omit [SFinite μ] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [InnerProductSpace ℂ H] [CompleteSpace T] in
theorem spectral_mass_hasSum {v : ℕ → Lp H 2 μ} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x) :
    HasSum (fun n => ‖v n‖ ^ 2) (R.trace x) := by
  simpa only [R.trace_rankOne] using R.trace.hasSum hv

omit [CompleteSpace T] in
theorem ensemble_scalar_trace (F : NormalFunctionalData R)
    {v : ℕ → Lp H 2 μ} {x : T} (hv : HasSum (fun n => R.rankOne (v n)) x)
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hb : ∀ᵐ z ∂μ, |a z| ≤ C) :
    (F.repr x (realL2Multiplier a ha C hb)).re =
      ∫ z, a z * ‖ensemble v (spectral_mass_hasSum hv).summable z‖ ^ 2 ∂μ := by
  have htrace := Complex.reCLM.hasSum (F.observable_hasSum hv (realL2Multiplier a ha C hb))
  have hsource := ensemble_tested_mass_hasSum v (spectral_mass_hasSum hv).summable a ha
    (by simpa only [Real.norm_eq_abs] using hb)
  simp only [Complex.reCLM_apply, scalar_trace_rankOne] at htrace
  exact htrace.unique hsource

omit [CompleteSpace T] in
/-- The spectral choice cannot change the configuration-space density. -/
theorem ensemble_density_independent (F : NormalFunctionalData R)
    {v w : ℕ → Lp H 2 μ} {x : T}
    (hv : HasSum (fun n => R.rankOne (v n)) x)
    (hw : HasSum (fun n => R.rankOne (w n)) x) :
    (fun z => ‖ensemble v (spectral_mass_hasSum hv).summable z‖ ^ 2) =ᵐ[μ]
      (fun z => ‖ensemble w (spectral_mass_hasSum hw).summable z‖ ^ 2) := by
  apply RemovalConstraints.ae_eq_of_boundedSpatialTests
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
  intro t
  have hb : ∀ᵐ z ∂μ, |t.weight z| ≤ 1 :=
    ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using t.bounded z
  exact (ensemble_scalar_trace F hv t.weight t.measurable hb).symm.trans
    (ensemble_scalar_trace F hw t.weight t.measurable hb)

end GptLean.PhysicalEnsembleSource
