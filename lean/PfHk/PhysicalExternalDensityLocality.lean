import PfHk.PhysicalExternalEnergy
import PfHk.PhysicalCoefficientLocality

/-! Coefficients agreeing on the vector support give the same full
covariant Carleman density. -/

noncomputable section
namespace PfHk.PhysicalExternalDensityLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalExternalEnergy PfHk.PhysicalCoefficientLocality PfHk.PhysicalDyadicEnergy

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

local instance densityLocalityPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A A' : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative positive' negative' : Configuration N → ℝ)

theorem density_congr (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u)
    (hu' : ExternalDomain (fun _ => 0) A' positive' negative' u)
    (h : Agreement A A' positive negative positive' negative'
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :
    density F χ C e A positive negative O τ α u hu =
      density F χ C e A' positive' negative' O τ α u hu' := by
  funext X
  have hkin := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
    congrArg (fun z : WaveSpace (Fin N × Fin 3) => ‖z X‖ ^ 2)
      (covariant_congr (fun _ => 0) A A' positive negative positive' negative' C
        (profile F χ 0) (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0)
        e u hu hu' h i)
  exact congrArg (fun z : ℝ => massEnergy O τ α u X + positiveKineticWeight O τ α X * z +
    radiationEnergy O τ α u X) hkin

def untruncatedDensity (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u) (X : Configuration N) : ℝ :=
  massEnergy O τ α u X + centeredKineticWeight O τ α X *
    (∑ i, ‖externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu i X‖ ^ 2) +
    radiationEnergy O τ α u X

theorem weights_nonneg_on_ball {O X : Configuration N} {R τ α : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (hR : R < 1) (hX : X ∈ Metric.ball O R) :
    0 ≤ centeredMassWeight O τ α X ∧ 0 ≤ centeredKineticWeight O τ α X := by
  have hnorm : ‖X - O‖ ≤ 1 := by
    simpa only [dist_eq_norm] using (Metric.mem_ball.mp hX).le.trans hR.le
  have hlog : 0 ≤ -Real.log ‖X - O‖ := neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hnorm)
  have hbeta : 0 ≤ CarlemanWeights.beta α (-Real.log ‖X - O‖) :=
    mul_nonneg (mul_nonneg hα.le (by linarith only [hα])) (Real.rpow_nonneg hlog _)
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hτ _)) hbeta)
      (inv_nonneg.mpr (sq_nonneg _))
  · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hτ) hbeta

theorem density_eq_on_ball {O X : Configuration N} {R τ α : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (hR : R < 1) (hX : X ∈ Metric.ball O R)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u) :
    density F χ C e A positive negative O τ α u hu X =
      untruncatedDensity F χ C e A positive negative O τ α u hu X := by
  have hw := max_eq_right (weights_nonneg_on_ball hτ hα hR hX).2
  exact congrArg (fun z : ℝ => massEnergy O τ α u X + z *
    (∑ i, ‖externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu i X‖ ^ 2) +
      radiationEnergy O τ α u X) hw

private theorem weighted_zero {H : Type*} [NormedAddCommGroup H] (w : ℝ) :
    w * ‖(0 : H)‖ ^ 2 = 0 := by simp

theorem density_nonneg {O : Configuration N} {R τ α : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (hR : R < 1)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u)
    (hsupp : PhysicalCarlemanInput.AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    ∀ᵐ X ∂volume, 0 ≤ density F χ C e A positive negative O τ α u hu X := by
  let r := Classical.choose hsupp
  let r' := Classical.choose (Classical.choose_spec hsupp)
  have hsupport := Classical.choose_spec (Classical.choose_spec hsupp)
  have hr'R := hsupport.2.2.1
  have hs := hsupport.2.2.2
  filter_upwards [hs] with X hX
  have hm : 0 ≤ massEnergy O τ α u X := by
    by_cases hx : X ∈ Metric.ball O R
    · exact mul_nonneg (weights_nonneg_on_ball hτ hα hR hx).1 (sq_nonneg _)
    · have hz := hX (Or.inr (hr'R.trans_le (not_lt.mp hx)))
      exact ((congrArg (fun z : PhotonFock => centeredMassWeight O τ α X * ‖z‖ ^ 2) hz).trans
        (weighted_zero _)).ge
  have hk : 0 ≤ positiveKinetic F χ C e A positive negative O τ α u hu X :=
    mul_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hr : 0 ≤ radiationEnergy O τ α u X :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hτ)) (sq_nonneg _)
  exact add_nonneg (add_nonneg hm hk) hr

theorem paper_density_bound {O : Configuration N} {R τ α K source : ℝ}
    (hτ : 0 ≤ τ) (hα : 0 < α) (hR : R < 1)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u)
    (hsupp : PhysicalCarlemanInput.AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hi : Integrable (density F χ C e A positive negative O τ α u hu))
    (hb : (∫ X, density F χ C e A positive negative O τ α u hu X) ≤ K * source) :
    IntegrableOn (untruncatedDensity F χ C e A positive negative O τ α u hu) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, untruncatedDensity F χ C e A positive negative O τ α u hu X) ≤ K * source := by
  have heq : density F χ C e A positive negative O τ α u hu =ᵐ[volume.restrict (Metric.ball O R)]
      untruncatedDensity F χ C e A positive negative O τ α u hu := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
    exact density_eq_on_ball F χ C e A positive negative hτ hα hR hX u hu
  exact ⟨hi.integrableOn.congr heq,
    (integral_congr_ae heq).symm.le.trans
      ((setIntegral_le_integral hi (density_nonneg F χ C e A positive negative hτ hα hR u hu hsupp)).trans hb)⟩

end PfHk.PhysicalExternalDensityLocality
