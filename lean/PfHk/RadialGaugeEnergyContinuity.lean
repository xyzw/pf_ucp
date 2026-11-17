import PfHk.RadialGaugeEnergyLabel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Joint continuity of the actual radiation displacement labels. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
attribute [local irreducible] energyKernel energyRay energyLabel sqrtLabel

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

theorem energyRay_joint_continuous :
    Continuous (fun p : Configuration N × ℝ => energyRay F χ hUV e p.1 p.2) := by
  have hθ : Continuous (fun p : Configuration N × ℝ => p.1) := continuous_fst
  have hr : Continuous (fun p : Configuration N × ℝ => p.2) := continuous_snd
  have hX : Continuous (fun p : Configuration N × ℝ => p.2 • p.1) := hr.smul hθ
  have hp (j : Fin N) : Continuous (fun p : Configuration N × ℝ => particle (p.2 • p.1) j) :=
    (particleLinear j).continuous_of_finiteDimensional.comp hX
  have hk (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ =>
      energyKernel F χ hUV j.2 (particle (p.2 • p.1) j.1)) :=
    (energyKernel_continuous F χ hUV j.2).comp (hp j.1)
  have hc (j : Fin N × Fin 3) : Continuous (fun p : Configuration N × ℝ => p.1 j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) j).comp hθ
  unfold energyRay
  exact continuous_finsetSum _ (fun j _ => (hc j).smul
    ((continuous_const : Continuous (fun _ : Configuration N × ℝ => (-e : ℝ))).smul (hk j)))

theorem energyRay_continuous_theta (r : ℝ) :
    Continuous (fun θ : Configuration N => energyRay F χ hUV e θ r) := by
  have harg : Continuous (fun θ : Configuration N => (θ, r)) :=
    continuous_id.prodMk continuous_const
  exact (energyRay_joint_continuous F χ hUV e).comp harg

theorem energyLabel_continuous : Continuous (energyLabel F χ hUV e (N := N)) := by
  unfold energyLabel
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (energyRay_joint_continuous F χ hUV e) 0 1

theorem sqrtLabel_continuous : Continuous (sqrtLabel F χ hUV e (N := N)) := by
  unfold sqrtLabel
  exact (energyComponent true).continuous.comp (energyLabel_continuous F χ hUV e)

/-- Uniform square-root-frequency bound for the radial integrand. -/
theorem energyRay_sqrt_norm_le (θ : Configuration N) (r : ℝ) :
    ‖energyComponent true (energyRay F χ hUV e θ r)‖ ≤
      (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  have h (j : Fin N × Fin 3) :
      ‖(omegaKernel F χ hUV j.2 (particle (r • θ) j.1)).val.2‖ ≤
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
    (norm_snd_le _).trans (omegaKernel_uniform_bound F χ hUV _ _)
  simp only [energyRay, map_sum, map_smul]
  unfold energyKernel
  change ‖∑ j : Fin N × Fin 3, θ j • ((-e) •
    (omegaKernel F χ hUV j.2 (particle (r • θ) j.1)).val.2)‖ ≤ _
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
    ‖sqrtLabel F χ hUV e (r • θ)‖ ≤
      |r| * (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  rw [sqrtLabel, energyLabel_smul, ← (energyComponent true).intervalIntegral_comp_comm
    ((energyRay_continuous F χ hUV e θ).intervalIntegrable 0 r)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := r)
    (fun s _ => energyRay_sqrt_norm_le F χ hUV e θ s)
  exact h.trans_eq (by simp only [sub_zero]; ring)

end PfHk.RadialGauge
