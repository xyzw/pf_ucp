import PfHk.RadialGauge
import PfHk.PhysicalFieldRegularity

/-! The radial Weyl label in the square-root-frequency graph. The weight
relation is preserved by integrating in the actual closed multiplier
graph, and the logarithmic derivative has a uniform `O(r)` bound. -/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

/-- The second component of `ωG` is exactly `√ω G`. -/
theorem omegaKernel_sqrt_relation (i : Fin 3) (x : FieldSpace) :
    ∀ᵐ p ∂photonMeasure, (omegaKernel F χ hUV i x).val.2 p =
      (Real.sqrt ‖p.1‖ : ℂ) * (physicalKernel F χ i x).val.1 p := by
  have hn : ∀ᵐ p ∂photonMeasure, p.1 ≠ (0 : FieldSpace) :=
    (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae (volume.ae_ne 0)
  filter_upwards [omegaKernel_fst_ae F χ hUV i x, (omegaKernel F χ hUV i x).property, hn]
    with p hp hq hn
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hn))))
  rw [← hq, hp, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (norm_nonneg _)]

abbrev EnergyLabel := PhysicalMultiplicationGraph.GraphSpace photonMeasure
  (H := ℂ) (fun p => (Real.sqrt ‖p.1‖ : ℂ))

def energyKernel (i : Fin 3) (x : FieldSpace) : EnergyLabel :=
  ⟨((physicalKernel F χ i x).val.1, (omegaKernel F χ hUV i x).val.2),
    omegaKernel_sqrt_relation F χ hUV i x⟩

def energyComponent (infrared : Bool) : EnergyLabel →L[ℝ] Lp ℂ 2 photonMeasure :=
  ((if infrared then ContinuousLinearMap.snd ℂ _ _ else ContinuousLinearMap.fst ℂ _ _).comp
    (PhysicalMultiplicationGraph.graph photonMeasure (H := ℂ)
      (fun p => (Real.sqrt ‖p.1‖ : ℂ))).subtypeL).restrictScalars ℝ

theorem energyKernel_continuous (i : Fin 3) : Continuous (energyKernel F χ hUV i) := by
  apply Continuous.subtype_mk
  exact ((component false).continuous.comp (physicalKernel_continuous F χ i)).prodMk
    ((component true).continuous.comp (omegaKernel_continuous F χ hUV i))

def energyRay (θ : Configuration N) (r : ℝ) : EnergyLabel :=
  ∑ j : Fin N × Fin 3, θ j • ((-e) • energyKernel F χ hUV j.2 (particle (r • θ) j.1))

theorem energyRay_continuous (θ : Configuration N) : Continuous (energyRay F χ hUV e θ) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_const : Continuous (fun _ : ℝ => θ j)).smul
    ((continuous_const : Continuous (fun _ : ℝ => (-e : ℝ))).smul
      ((energyKernel_continuous F χ hUV j.2).comp
        ((particleLinear j.1).continuous_of_finiteDimensional.comp
          (continuous_id.smul continuous_const))))

def energyLabel (X : Configuration N) : EnergyLabel :=
  ∫ s in (0 : ℝ)..1, energyRay F χ hUV e X s

def sqrtLabel (X : Configuration N) : Lp ℂ 2 photonMeasure :=
  energyComponent true (energyLabel F χ hUV e X)

theorem energyRay_fst (θ : Configuration N) (r : ℝ) :
    energyComponent false (energyRay F χ hUV e θ r) = component false (rayIntegrand F χ e θ r) := by
  simp only [energyRay, rayIntegrand, map_sum, map_smul]
  rfl

theorem energyLabel_fst (X : Configuration N) :
    (energyLabel F χ hUV e X).val.1 = (label F χ e X).val.1 := by
  change energyComponent false (energyLabel F χ hUV e X) = component false (label F χ e X)
  rw [energyLabel, label, ← (energyComponent false).intervalIntegral_comp_comm
    ((energyRay_continuous F χ hUV e X).intervalIntegrable 0 1),
    ← (component false).intervalIntegral_comp_comm
      ((rayIntegrand_continuous F χ e X).intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr (fun s _ => energyRay_fst F χ hUV e X s)

/-- This is the literal multiplier relation required by `weylWeightedGraph`. -/
theorem sqrtLabel_relation (X : Configuration N) :
    ∀ᵐ p ∂photonMeasure, sqrtLabel F χ hUV e X p =
      (Real.sqrt ‖p.1‖ : ℂ) * (label F χ e X).val.1 p := by
  have h := (energyLabel F χ hUV e X).property
  change ∀ᵐ p ∂photonMeasure, (energyLabel F χ hUV e X).val.2 p =
    (Real.sqrt ‖p.1‖ : ℂ) * (energyLabel F χ hUV e X).val.1 p at h
  rw [energyLabel_fst F χ hUV e X] at h
  exact h

theorem energyRay_smul (θ : Configuration N) (r s : ℝ) :
    energyRay F χ hUV e (r • θ) s = r • energyRay F χ hUV e θ (s * r) := by
  simp only [energyRay, PiLp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, mul_assoc]

theorem energyLabel_smul (θ : Configuration N) (r : ℝ) :
    energyLabel F χ hUV e (r • θ) = ∫ s in (0 : ℝ)..r, energyRay F χ hUV e θ s := by
  unfold energyLabel
  simp_rw [energyRay_smul]
  rw [intervalIntegral.integral_smul]
  simp

theorem energyLabel_radial_hasDerivAt (θ : Configuration N) (r : ℝ) :
    HasDerivAt (fun s : ℝ => energyLabel F χ hUV e (s • θ)) (energyRay F χ hUV e θ r) r := by
  simp_rw [energyLabel_smul]
  exact intervalIntegral.integral_hasDerivAt_right
    ((energyRay_continuous F χ hUV e θ).intervalIntegrable 0 r)
    (energyRay_continuous F χ hUV e θ).stronglyMeasurable.stronglyMeasurableAtFilter
    (energyRay_continuous F χ hUV e θ).continuousAt

/-- The radiation-weighted radial label has the exact logarithmic derivative. -/
theorem sqrtLabel_logarithmic_hasDerivAt (θ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sqrtLabel F χ hUV e (Real.exp (-s) • θ))
      ((-Real.exp (-t)) • energyComponent true (energyRay F χ hUV e θ (Real.exp (-t)))) t := by
  have ht : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hh := (energyLabel_radial_hasDerivAt F χ hUV e θ (Real.exp (-t))).scomp t ht
  simpa only [sqrtLabel, Function.comp_def, map_smul] using
    (energyComponent true).hasFDerivAt.comp_hasDerivAt t hh

/-- Uniform `O(r)` bound, including its dependence on electron number and charge. -/
theorem sqrtLabel_logarithmic_derivative_bound (θ : Configuration N) (r : ℝ) :
    ‖(-r) • energyComponent true (energyRay F χ hUV e θ r)‖ ≤
      |r| * (Fintype.card (Fin N × Fin 3) * |e| *
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)) * ‖θ‖ := by
  have h (j : Fin N × Fin 3) :
      ‖(omegaKernel F χ hUV j.2 (particle (r • θ) j.1)).val.2‖ ≤
        PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _) :=
    (norm_snd_le _).trans (omegaKernel_uniform_bound F χ hUV _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  simp only [energyRay, map_sum, map_smul]
  change |r| * ‖∑ j : Fin N × Fin 3, θ j • ((-e) •
    (omegaKernel F χ hUV j.2 (particle (r • θ) j.1)).val.2)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg r)).trans
  have hs : (∑ j : Fin N × Fin 3,
      ‖θ j • ((-e) • (omegaKernel F χ hUV j.2 (particle (r • θ) j.1)).val.2)‖) ≤
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

end PfHk.RadialGauge
