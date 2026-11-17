import GptLean.SymmetricLift.L2Dominated
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.MeanValue

/-! Differentiating actual Bochner L2 vectors from pointwise derivatives
and a local square-integrable slope bound. This is used to lift physical
field form calculations from photon fibers to the sphere Hilbert space. -/

noncomputable section
namespace PfHk.L2ParameterDerivative

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem tendsto_toLp_of_eventually_dominated_sq
    {f : ℕ → X → E} {g : X → E} {b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hb : Integrable b μ)
    (hfb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖f n x‖ ^ 2 ≤ b x)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfb
  apply (tendsto_add_atTop_iff_nat N).mp
  exact tendsto_toLp_two_of_dominated_sq (fun n => hf (n + N)) hg hb
    (fun n => hN (n + N) (Nat.le_add_left _ _)) hgb
    (hlim.mono fun x hx => hx.comp (tendsto_add_atTop_nat N))

/-- Local domination of difference quotients suffices. No derivative of a
choice of representatives in L2 is assumed. -/
theorem hasDerivAt_toLp {f : ℝ → X → E} {g : X → E} {b : X → ℝ} {t : ℝ}
    (hf : ∀ s, MemLp (f s) 2 μ) (hg : MemLp g 2 μ) (hb : Integrable b μ)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun s => f s x) (g x) t)
    (hfb : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖h⁻¹ • (f (t + h) x - f t x)‖ ^ 2 ≤ b x)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x) :
    HasDerivAt (fun s => (hf s).toLp (f s)) (hg.toLp g) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro sn hsn
  let slope : ℕ → X → E := fun n x => (sn n)⁻¹ • (f (t + sn n) x - f t x)
  have hslope : ∀ n, MemLp (slope n) 2 μ := fun n =>
    ((hf (t + sn n)).sub (hf t)).const_smul ((sn n)⁻¹)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, ‖slope n x‖ ^ 2 ≤ b x := hsn.eventually hfb
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => slope n x) atTop (𝓝 (g x)) :=
    hd.mono fun x hx => hx.tendsto_slope_zero.comp hsn
  have h := tendsto_toLp_of_eventually_dominated_sq hslope hg hb hbound hgb hlim
  convert h using 1
  funext n
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul ((sn n)⁻¹)
      ((hf (t + sn n)).toLp (f (t + sn n)) - (hf t).toLp (f t)),
    Lp.coeFn_sub ((hf (t + sn n)).toLp (f (t + sn n))) ((hf t).toLp (f t)),
    (hf (t + sn n)).coeFn_toLp, (hf t).coeFn_toLp, (hslope n).coeFn_toLp]
    with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.smul_apply, Pi.sub_apply] at h₁ h₂
  simp only [Function.comp_apply]
  rw [h₁, h₂, h₃, h₄, h₅]

/-- A uniform local derivative bound controls the difference quotients
needed by the L2 theorem, including the zero increment. -/
theorem local_slope_norm_le {f df : ℝ → E} {t D h : ℝ} (hD : 0 ≤ D)
    (hd : ∀ s ∈ Set.Icc (t - 1) (t + 1), HasDerivAt f (df s) s)
    (hbound : ∀ s ∈ Set.Icc (t - 1) (t + 1), ‖df s‖ ≤ D)
    (hh : |h| ≤ 1) : ‖h⁻¹ • (f (t + h) - f t)‖ ≤ D := by
  have ht : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hth : t + h ∈ Set.Icc (t - 1) (t + 1) := by
    obtain ⟨hl, hu⟩ := abs_le.mp hh
    exact ⟨by linarith, by linarith⟩
  have hb : ∀ s ∈ Set.Icc (t - 1) (t + 1), ‖deriv f s‖ ≤ D := by
    intro s hs
    rw [(hd s hs).deriv]
    exact hbound s hs
  have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hb (convex_Icc (t - 1) (t + 1)) ht hth
  simp only [add_sub_cancel_left] at hdiff
  by_cases hz : h = 0
  · simp only [hz, inv_zero, zero_smul, norm_zero]
    exact hD
  · rw [norm_smul, norm_inv]
    calc
      _ ≤ ‖h‖⁻¹ * (D * ‖h‖) := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
      _ = D := by field_simp

end PfHk.L2ParameterDerivative
