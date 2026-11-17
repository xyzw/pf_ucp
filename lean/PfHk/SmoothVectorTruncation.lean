import PfHk.LocalWeakDivergence
import PfHk.CoordinateCoefficientLocalization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth localization of a rough one-body vector field. The cutoff equals
one on the inner ball and has support strictly inside the ball on which the
coefficient norms are given. Its divergence includes the actual cutoff
derivative term, at exponent `min ell 6`. -/

noncomputable section
namespace PfHk.SmoothVectorTruncation

open MeasureTheory GptLean.PhysicalSourceCoordinates
open PfHk.FriedrichsDivergenceBackground PfHk.CoordinateCoefficientLocalization
open scoped ENNReal Topology ContDiff

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 30000

def cutoff (o : Position) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump o :=
  ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩

theorem cutoff_support (o : Position) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (cutoff o ρ hρ) ⊆ Metric.ball o ρ := by
  rw [(cutoff o ρ hρ).tsupport_eq]
  intro x hx
  have hdist := Metric.mem_closedBall.mp hx
  change dist x o ≤ 3 * ρ / 4 at hdist
  exact Metric.mem_ball.mpr (by linarith only [hdist, hρ])

theorem cutoff_one (o : Position) {ρ : ℝ} (hρ : 0 < ρ) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) : cutoff o ρ hρ x = 1 := by
  apply (cutoff o ρ hρ).one_of_mem_closedBall
  exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le

theorem cutoff_partial_zero (o : Position) {ρ : ℝ} (hρ : 0 < ρ) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) (i : Fin 3) :
    coordinatePartial (cutoff o ρ hρ) i x = 0 := by
  have he := (cutoff o ρ hρ).eventuallyEq_one_of_mem_ball hx
  unfold coordinatePartial
  rw [he.fderiv_eq]
  simp

theorem compact_mul_memLp {q : ℝ≥0∞} (o : Position) (ρ : ℝ)
    (χ b : Position → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.ball o ρ)
    (hb : MemLp b q (volume.restrict (Metric.ball o ρ))) :
    MemLp (fun x => χ x * b x) q volume := by
  have hm : MemLp (fun x => χ x * zeroExtension o ρ b x) q volume :=
    (zeroExtension_memLp o ρ b hb).mul' (hχ.memLp_top_of_hasCompactSupport hc volume)
  apply hm.ae_eq
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ Metric.ball o ρ
    · simp [zeroExtension, hx]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp [hz]

theorem compact_mul_memLp_lower {p q : ℝ≥0∞} (hqp : q ≤ p)
    (o : Position) (ρ : ℝ) (χ b : Position → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.ball o ρ)
    (hb : MemLp b p (volume.restrict (Metric.ball o ρ))) :
    MemLp (fun x => χ x * b x) q volume := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball o ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  exact compact_mul_memLp o ρ χ b hχ hc hs (hb.mono_exponent hqp)

theorem vector_memLp (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (A : Fin 3 → Position → ℝ)
    (hA : ∀ i, MemLp (A i) 6 (volume.restrict (Metric.ball o ρ))) (i : Fin 3) :
    MemLp (truncatedVector (cutoff o ρ hρ) A i) 6 volume :=
  compact_mul_memLp o ρ _ _ (cutoff o ρ hρ).continuous
    (cutoff o ρ hρ).hasCompactSupport (cutoff_support o hρ) (hA i)

theorem divergence_memLp (o : Position) {ρ ℓ : ℝ} (hρ : 0 < ρ)
    (A : Fin 3 → Position → ℝ) (d : Position → ℝ)
    (hA : ∀ i, MemLp (A i) 6 (volume.restrict (Metric.ball o ρ)))
    (hd : MemLp d (ENNReal.ofReal ℓ) (volume.restrict (Metric.ball o ρ))) :
    MemLp (truncatedDivergence (cutoff o ρ hρ) A d)
      (ENNReal.ofReal (min ℓ 6)) volume := by
  have hqℓ : ENNReal.ofReal (min ℓ 6) ≤ ENNReal.ofReal ℓ := ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hq6 : ENNReal.ofReal (min ℓ 6) ≤ 6 := by
    exact (ENNReal.ofReal_le_ofReal (min_le_right ℓ 6)).trans_eq (by norm_num)
  have hv := compact_mul_memLp_lower hqℓ o ρ _ d (cutoff o ρ hρ).continuous
    (cutoff o ρ hρ).hasCompactSupport (cutoff_support o hρ) hd
  have hg (i : Fin 3) : MemLp (fun x => coordinatePartial (cutoff o ρ hρ) i x * A i x)
      (ENNReal.ofReal (min ℓ 6)) volume := by
    apply compact_mul_memLp_lower hq6 o ρ _ _
      (coordinatePartial_continuous (cutoff o ρ hρ).contDiff i)
      ((cutoff o ρ hρ).hasCompactSupport.fderiv_apply ℝ _)
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (cutoff_support o hρ)
    · exact hA i
  exact hv.add (memLp_finsetSum Finset.univ (fun i _ => hg i))

theorem divergence_exponent {ℓ : ℝ} (hℓ : 2 < ℓ) : 2 < min ℓ 6 :=
  lt_min hℓ (by norm_num)

theorem weakDivergence (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    {A : Fin 3 → Position → ℝ} {d : Position → ℝ}
    (hdiv : WeakDivergence A d) (hA : ∀ i, LocallyIntegrable (A i) volume)
    (hd : LocallyIntegrable d volume) :
    WeakDivergence (truncatedVector (cutoff o ρ hρ) A)
      (truncatedDivergence (cutoff o ρ hρ) A d) :=
  hdiv.smooth_mul hA hd (cutoff o ρ hρ).contDiff

theorem weakDivergence_local (o : Position) {ρ ℓ : ℝ} (hρ : 0 < ρ) (hℓ : 2 < ℓ)
    {A : Fin 3 → Position → ℝ} {d : Position → ℝ}
    (hdiv : WeakDivergenceOn (Metric.ball o ρ) A d)
    (hA : ∀ i, MemLp (A i) 6 (volume.restrict (Metric.ball o ρ)))
    (hd : MemLp d (ENNReal.ofReal ℓ) (volume.restrict (Metric.ball o ρ))) :
    WeakDivergence (truncatedVector (cutoff o ρ hρ) A)
      (truncatedDivergence (cutoff o ρ hρ) A d) := by
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ℓ := by
    exact (by norm_num : (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ)).le.trans
      (ENNReal.ofReal_le_ofReal (by linarith only [hℓ]))
  exact hdiv.smooth_mul_ball (by norm_num) hq hA hd
    (cutoff o ρ hρ).contDiff (cutoff_support o hρ)

theorem vector_eq (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (A : Fin 3 → Position → ℝ) (i : Fin 3) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) : truncatedVector (cutoff o ρ hρ) A i x = A i x := by
  simp only [truncatedVector, cutoff_one o hρ hx, one_mul]

theorem divergence_eq (o : Position) {ρ : ℝ} (hρ : 0 < ρ)
    (A : Fin 3 → Position → ℝ) (d : Position → ℝ) {x : Position}
    (hx : x ∈ Metric.ball o (ρ / 2)) : truncatedDivergence (cutoff o ρ hρ) A d x = d x := by
  simp only [truncatedDivergence, cutoff_one o hρ hx, one_mul,
    cutoff_partial_zero o hρ hx, zero_mul, Finset.sum_const_zero, add_zero]

end PfHk.SmoothVectorTruncation
