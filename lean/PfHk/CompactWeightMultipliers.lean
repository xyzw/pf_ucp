import GptLean.PhotonLocalizationLocalForms
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Bounded L2 multipliers obtained by truncating continuous weights to a
compact set. Their norms are the actual weighted integrals. Electronic
support is closed under strong L2 convergence. -/

noncomputable section
namespace PfHk.CompactWeightMultipliers

open MeasureTheory Filter Set GptLean.PhotonLocalization
open scoped Topology

set_option Elab.async false
set_option maxHeartbeats 100000

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem truncate_bound (s : Set X) :
    ∀ᵐ x ∂μ, |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := ae_of_all _ fun x => by
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, abs_one, le_refl]
  · simp only [indicator_of_notMem hx, abs_zero, zero_le_one]

def truncate (s : Set X) (hs : MeasurableSet s) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  realL2Multiplier (s.indicator fun _ => (1 : ℝ))
    (aestronglyMeasurable_const.indicator hs) 1 (truncate_bound s)

theorem truncate_ae (s : Set X) (hs : MeasurableSet s) (u : Lp H 2 μ) :
    truncate s hs u =ᵐ[μ] s.indicator (fun x => u x) := by
  filter_upwards [realL2Multiplier_apply (s.indicator fun _ => (1 : ℝ))
    (aestronglyMeasurable_const.indicator hs) 1 (truncate_bound s) u] with x hx
  by_cases hxs : x ∈ s
  · simpa only [truncate, indicator_of_mem hxs, one_smul] using hx
  · simpa only [truncate, indicator_of_notMem hxs, zero_smul] using hx

theorem truncate_eq_self_iff (s : Set X) (hs : MeasurableSet s) (u : Lp H 2 μ) :
    truncate s hs u = u ↔ ∀ᵐ x ∂μ, x ∉ s → u x = 0 := by
  constructor
  · intro h
    have ha := truncate_ae s hs u
    rw [h] at ha
    filter_upwards [ha] with x hx hxs
    exact hx.trans (indicator_of_notMem hxs _)
  · intro h
    apply Lp.ext
    filter_upwards [truncate_ae s hs u, h] with x hx hz
    by_cases hxs : x ∈ s
    · exact hx.trans (indicator_of_mem hxs _)
    · exact hx.trans ((indicator_of_notMem hxs _).trans (hz hxs).symm)

theorem supported_limit (s : Set X) (hs : MeasurableSet s)
    {u : ℕ → Lp H 2 μ} {v : Lp H 2 μ}
    (hu : ∀ n, ∀ᵐ x ∂μ, x ∉ s → u n x = 0)
    (h : Tendsto u atTop (𝓝 v)) : ∀ᵐ x ∂μ, x ∉ s → v x = 0 := by
  apply (truncate_eq_self_iff s hs v).mp
  have hmap := ((truncate s hs).continuous.tendsto v).comp h
  have heq : (fun n => truncate s hs (u n)) = u :=
    funext fun n => (truncate_eq_self_iff s hs (u n)).mpr (hu n)
  dsimp only [Function.comp_def] at hmap
  rw [heq] at hmap
  exact tendsto_nhds_unique hmap h

section Compact
variable [TopologicalSpace X] [OpensMeasurableSpace X]

private theorem exists_indicator_bound (s : Set X) (hs : IsCompact s)
    (w : X → ℝ) (hw : ContinuousOn w s) :
    ∃ B : ℝ, ∀ x, |s.indicator w x| ≤ B := by
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hw
  refine ⟨max B 0, fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx]
    exact (hB x hx).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx, abs_zero]
    exact le_max_right _ _

def bound (s : Set X) (hs : IsCompact s) (w : X → ℝ) (hw : ContinuousOn w s) : ℝ :=
  Classical.choose (exists_indicator_bound s hs w hw)

theorem bounded (s : Set X) (hs : IsCompact s) (w : X → ℝ) (hw : ContinuousOn w s) :
    ∀ x, |s.indicator w x| ≤ bound s hs w hw :=
  Classical.choose_spec (exists_indicator_bound s hs w hw)

theorem indicator_measurable (s : Set X) (hs : IsCompact s) (hsm : MeasurableSet s)
    (w : X → ℝ) (hw : ContinuousOn w s) : AEStronglyMeasurable (s.indicator w) μ :=
  (aestronglyMeasurable_indicator_iff hsm).mpr
    (hw.aestronglyMeasurable_of_isCompact hs hsm)

def multiplier (s : Set X) (hs : IsCompact s) (hsm : MeasurableSet s)
    (w : X → ℝ) (hw : ContinuousOn w s) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  realL2Multiplier (s.indicator w) (indicator_measurable s hs hsm w hw)
    (bound s hs w hw) (ae_of_all _ (bounded s hs w hw))

theorem multiplier_ae (s : Set X) (hs : IsCompact s) (hsm : MeasurableSet s)
    (w : X → ℝ) (hw : ContinuousOn w s) (u : Lp H 2 μ) :
    multiplier s hs hsm w hw u =ᵐ[μ] fun x => s.indicator w x • u x :=
  realL2Multiplier_apply _ _ _ _ _

def sqrtMultiplier (s : Set X) (hs : IsCompact s) (hsm : MeasurableSet s)
    (w : X → ℝ) (hw : ContinuousOn w s) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  multiplier s hs hsm (fun x => Real.sqrt (w x)) (Real.continuous_sqrt.comp_continuousOn hw)

theorem sqrtMultiplier_norm_sq (s : Set X) (hs : IsCompact s) (hsm : MeasurableSet s)
    (w : X → ℝ) (hw : ContinuousOn w s) (hw0 : ∀ x ∈ s, 0 ≤ w x)
    (u : Lp H 2 μ) :
    ‖sqrtMultiplier s hs hsm w hw u‖ ^ 2 = ∫ x in s, w x * ‖u x‖ ^ 2 ∂μ := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [GptLean.PhotonKernelLocalization.l2_norm_sq_eq_integral, ← integral_indicator hsm]
  apply integral_congr_ae
  filter_upwards [multiplier_ae s hs hsm (fun x => Real.sqrt (w x))
    (Real.continuous_sqrt.comp_continuousOn hw) u] with x hx
  change ‖multiplier s hs hsm (fun x => Real.sqrt (w x))
    (Real.continuous_sqrt.comp_continuousOn hw) u x‖ ^ 2 = _
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs, indicator_of_mem hxs, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, Real.sq_sqrt (hw0 x hxs)]
  · rw [indicator_of_notMem hxs, indicator_of_notMem hxs, zero_smul, norm_zero, zero_pow]
    norm_num

theorem sqrtMultiplier_norm_sq_supported (s : Set X) (hs : IsCompact s)
    (hsm : MeasurableSet s) (w : X → ℝ) (hw : ContinuousOn w s)
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (u : Lp H 2 μ)
    (hu : ∀ᵐ x ∂μ, x ∉ s → u x = 0) :
    ‖sqrtMultiplier s hs hsm w hw u‖ ^ 2 = ∫ x, w x * ‖u x‖ ^ 2 ∂μ := by
  rw [sqrtMultiplier_norm_sq s hs hsm w hw hw0 u]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hu] with x hx hxs
  rw [hx hxs, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]

end Compact
end PfHk.CompactWeightMultipliers
