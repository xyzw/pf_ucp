import PfHk.CenteredRadialGauge
import PfHk.RadialGaugeEnergyLabel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual square-root-frequency Weyl label at an arbitrary center.
All constants are independent of the center. -/

noncomputable section
namespace PfHk.CenteredRadialGauge
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open PfHk.RadialGauge (EnergyLabel energyKernel energyComponent energyKernel_continuous)
open scoped ENNReal InnerProductSpace Interval
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)
  (O : Configuration N)

def energyRay (θ : Configuration N) (r : ℝ) : EnergyLabel :=
  ∑ j : Fin N × Fin 3, θ j • ((-e) • energyKernel F χ hUV j.2 (particle (O + r • θ) j.1))

theorem energyRay_continuous (θ : Configuration N) : Continuous (energyRay F χ hUV e O θ) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : ℝ => θ j)).smul
    ((continuous_const : Continuous (fun _ : ℝ => (-e : ℝ))).smul
      ((energyKernel_continuous F χ hUV j.2).comp
        ((particleLinear j.1).continuous_of_finiteDimensional.comp
          (continuous_const.add (continuous_id.smul continuous_const)))))

def energyLabel (X : Configuration N) : EnergyLabel :=
  ∫ s in (0 : ℝ)..1, energyRay F χ hUV e O X s

def sqrtLabel (X : Configuration N) : Lp ℂ 2 photonMeasure :=
  energyComponent true (energyLabel F χ hUV e O X)

theorem energyRay_fst (θ : Configuration N) (r : ℝ) :
    energyComponent false (energyRay F χ hUV e O θ r) = component false (rayIntegrand F χ e O θ r) := by
  simp only [energyRay, rayIntegrand, map_sum, map_smul]
  rfl

theorem energyLabel_fst (X : Configuration N) :
    (energyLabel F χ hUV e O X).val.1 = (label F χ e O X).val.1 := by
  change energyComponent false (energyLabel F χ hUV e O X) = component false (label F χ e O X)
  rw [energyLabel, label, ← (energyComponent false).intervalIntegral_comp_comm
    ((energyRay_continuous F χ hUV e O X).intervalIntegrable 0 1),
    ← (component false).intervalIntegral_comp_comm
      ((rayIntegrand_continuous F χ e O X).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr (fun s _ => energyRay_fst F χ hUV e O X s)

/-- This is the literal multiplier relation required by `weylWeightedGraph`. -/
theorem sqrtLabel_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, sqrtLabel F χ hUV e O X p =
      (Real.sqrt ‖p.1‖ : ℂ) * (label F χ e O X).val.1 p := by
  have h := (energyLabel F χ hUV e O X).property
  change ∀ᵐ p ∂photonMeasure, (energyLabel F χ hUV e O X).val.2 p =
    (Real.sqrt ‖p.1‖ : ℂ) * (energyLabel F χ hUV e O X).val.1 p at h
  rw [energyLabel_fst F χ hUV e O X] at h
  exact h

theorem energyRay_smul (θ : Configuration N) (r s : ℝ) :
    energyRay F χ hUV e O (r • θ) s = r • energyRay F χ hUV e O θ (s * r) := by
  simp only [energyRay, PiLp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, mul_assoc]

theorem energyLabel_smul (θ : Configuration N) (r : ℝ) :
    energyLabel F χ hUV e O (r • θ) = ∫ s in (0 : ℝ)..r, energyRay F χ hUV e O θ s := by
  unfold energyLabel
  simp_rw [energyRay_smul]
  rw [intervalIntegral.integral_smul]
  simp

theorem energyLabel_radial_hasDerivAt (θ : Configuration N) (r : ℝ) :
    HasDerivAt (fun s : ℝ => energyLabel F χ hUV e O (s • θ)) (energyRay F χ hUV e O θ r) r := by
  simp_rw [energyLabel_smul]
  exact intervalIntegral.integral_hasDerivAt_right
    ((energyRay_continuous F χ hUV e O θ).intervalIntegrable 0 r)
    (energyRay_continuous F χ hUV e O θ).stronglyMeasurable.stronglyMeasurableAtFilter
    (energyRay_continuous F χ hUV e O θ).continuousAt

/-- The radiation-weighted radial label has the exact logarithmic derivative. -/
theorem sqrtLabel_logarithmic_hasDerivAt (θ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sqrtLabel F χ hUV e O (Real.exp (-s) • θ))
      ((-Real.exp (-t)) • energyComponent true (energyRay F χ hUV e O θ (Real.exp (-t)))) t := by
  have ht : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hh := (energyLabel_radial_hasDerivAt F χ hUV e O θ (Real.exp (-t))).scomp t ht
  simpa only [sqrtLabel, Function.comp_def, map_smul] using
    (energyComponent true).hasFDerivAt.comp_hasDerivAt t hh

/-- Uniform `O(r)` bound, including its dependence on electron number and charge. -/
theorem sqrtLabel_logarithmic_derivative_bound (θ : Configuration N) (r : ℝ) :
    ‖(-r) • energyComponent true (energyRay F χ hUV e O θ r)‖ ≤
      |r| * (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  have h (j : Fin N × Fin 3) :
      ‖(omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1)).val.2‖ ≤
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
    (norm_snd_le _).trans (omegaKernel_uniform_bound F χ hUV _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  simp only [energyRay, map_sum, map_smul]
  change |r| * ‖∑ j : Fin N × Fin 3, θ j • ((-e) •
    (omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1)).val.2)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg r)).trans
  have hs : (∑ j : Fin N × Fin 3,
      ‖θ j • ((-e) • (omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1)).val.2)‖) ≤
        (Fintype.card (Fin N × Fin 3) : ℝ) * (‖θ‖ * (|e| *
          PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _))) := by
    calc
      _ ≤ ∑ _j : Fin N × Fin 3, ‖θ‖ * (|e| *
          PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, norm_smul, Real.norm_eq_abs (-e), abs_neg]
        exact mul_le_mul (PiLp.norm_apply_le θ j)
          (mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)) (by positivity) (norm_nonneg _)
      _ = _ := by simp
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (by ring)

set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] RadialGauge.energyKernel energyRay energyLabel sqrtLabel

theorem energyRay_joint_continuous :
    Continuous (fun p : Configuration N × ℝ => energyRay F χ hUV e O p.1 p.2) := by
  have hθ : Continuous (fun p : Configuration N × ℝ => p.1) := continuous_fst
  have hr : Continuous (fun p : Configuration N × ℝ => p.2) := continuous_snd
  have hX : Continuous (fun p : Configuration N × ℝ => O + p.2 • p.1) := continuous_const.add (hr.smul hθ)
  have hp (j : Fin N) : Continuous (fun p : Configuration N × ℝ => particle (O + p.2 • p.1) j) :=
    (particleLinear j).continuous_of_finiteDimensional.comp hX
  have hk (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ =>
      energyKernel F χ hUV j.2 (particle (O + p.2 • p.1) j.1)) :=
    (energyKernel_continuous F χ hUV j.2).comp (hp j.1)
  have hc (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ => p.1 j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp hθ
  unfold energyRay
  exact continuous_finsetSum _ (fun j _ => (hc j).smul
    ((continuous_const : Continuous (fun _ : Configuration N × ℝ => (-e : ℝ))).smul (hk j)))

theorem energyRay_continuous_theta (r : ℝ) :
    Continuous (fun θ : Configuration N => energyRay F χ hUV e O θ r) := by
  have harg : Continuous (fun θ : Configuration N => (θ, r)) :=
    continuous_id.prodMk continuous_const
  exact (energyRay_joint_continuous F χ hUV e O).comp harg

theorem energyLabel_continuous : Continuous (energyLabel F χ hUV e O (N := N)) := by
  unfold energyLabel
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (energyRay_joint_continuous F χ hUV e O) 0 1

theorem sqrtLabel_continuous : Continuous (sqrtLabel F χ hUV e O (N := N)) := by
  unfold sqrtLabel
  exact (energyComponent true).continuous.comp (energyLabel_continuous F χ hUV e O)

/-- Uniform square-root-frequency bound for the radial integrand. -/
theorem energyRay_sqrt_norm_le (θ : Configuration N) (r : ℝ) :
    ‖energyComponent true (energyRay F χ hUV e O θ r)‖ ≤
      (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  have h (j : Fin N × Fin 3) :
      ‖(omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1)).val.2‖ ≤
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
    (norm_snd_le _).trans (omegaKernel_uniform_bound F χ hUV _ _)
  simp only [energyRay, map_sum, map_smul]
  unfold energyKernel
  change ‖∑ j : Fin N × Fin 3, θ j • ((-e) •
    (omegaKernel F χ hUV j.2 (particle (O + r • θ) j.1)).val.2)‖ ≤ _
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin N × Fin 3, ‖θ‖ * (|e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, norm_smul, Real.norm_eq_abs (-e), abs_neg]
      exact mul_le_mul (PiLp.norm_apply_le θ j)
        (mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)) (by positivity) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Uniform linear growth of the actual square-root-frequency gauge label. -/
theorem sqrtLabel_smul_norm_le (θ : Configuration N) (r : ℝ) :
    ‖sqrtLabel F χ hUV e O (r • θ)‖ ≤
      |r| * (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  rw [sqrtLabel, energyLabel_smul, ← (energyComponent true).intervalIntegral_comp_comm
    ((energyRay_continuous F χ hUV e O θ).intervalIntegrable 0 r)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := r)
    (fun s _ => energyRay_sqrt_norm_le F χ hUV e O θ s)
  exact h.trans_eq (by simp only [sub_zero]; ring)

end PfHk.CenteredRadialGauge
