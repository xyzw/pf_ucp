import PfHk.PhysicalOperatorCarlemanBridge

/-! The checked full Hamiltonian estimate yields the exact shifted
nonnegative-integral Carleman input for physical unique continuation. -/

noncomputable section
namespace PfHk.PhysicalOperatorCarlemanBridge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalLocalEnergy PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalExternalDensityLocality
  PfHk.PhysicalSourceAbsorption PfHk.SmoothCutoffBounds PfHk.PhysicalOperatorDomain
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

local instance shiftedPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace

variable {N : ℕ}

theorem centered_weight_shift_bound {O X : Configuration N} {R τ α E : ℝ}
    (hX : X ∈ Metric.ball O R) (hRone : R < 1) (hα : 0 < α) (hτ : 0 ≤ τ)
    (hE : 2080 * E ^ 2 ≤ τ ^ 3)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ R → r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1) :
    2080 * E ^ 2 * centeredSourceWeight O τ α X ≤ centeredMassWeight O τ α X := by
  have h := EnergyShiftAbsorption.weight_shift_bound (dist_nonneg : 0 ≤ dist X O)
    ((Metric.mem_ball.mp hX).trans hRone) hα hτ hE
    (fun hr => hratio (dist X O) hr (Metric.mem_ball.mp hX).le)
  simpa only [centeredSourceWeight, centeredMassWeight, CarlemanSpatialDensity.sourceWeight,
    CarlemanSpatialDensity.massWeight, ← dist_eq_norm] using h

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  {O₀ : Configuration N} {ρ : ℝ} (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

theorem shifted_mass_estimate {O : Configuration N} {family : BufferedFamily O}
    {R : ℝ} {hR : 0 < R} {τ α C₂ C₂e E : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    {f : WaveSpace (Fin N × Fin 3)}
    (he : PhysicalLocalExternalCarleman.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hτ : 1 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R)
    (hE : 2080 * E ^ 2 ≤ τ ^ 3)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ R → r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ 1) :
    IntegrableOn (UniqueContinuation.radialMassIntegrand (fun X => dist X O)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) α τ) (Metric.ball O R) ∧
    IntegrableOn (sourceIntegrand O α τ
      (f - (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) u)) (Metric.ball O R) ∧
      (∫⁻ X in Metric.ball O R, ENNReal.ofReal
        (UniqueContinuation.radialMassIntegrand (fun X => dist X O)
          (inclusion (Fin N × Fin 3) (fun _ => 0) u) α τ X)) ≤
      ENNReal.ofReal 2080 * ∫⁻ X in Metric.ball O R,
        ENNReal.ofReal (sourceIntegrand O α τ
          (f - (E : ℂ) • inclusion (Fin N × Fin 3) (fun _ => 0) u) X) := by
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  let ψ : WaveSpace (Fin N × Fin 3) := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let error : WaveSpace (Fin N × Fin 3) := (E : ℂ) • ψ
  let shifted : WaveSpace (Fin N × Fin 3) := f - error
  have hm := mass_bound_of_estimate F χ C e a spectral he hτ0 hα hRone hsupp
  have hw : AEStronglyMeasurable (centeredSourceWeight O τ α) volume :=
    (centeredSourceWeight_measurable O τ α).aestronglyMeasurable
  have hw0 : ∀ᵐ X ∂volume.restrict (Metric.ball O R), 0 ≤ centeredSourceWeight O τ α X :=
    ae_of_all _ (centeredSourceWeight_nonneg O τ α)
  have heMeas : AEStronglyMeasurable (sourceEnergy O τ α error)
      (volume.restrict (Metric.ball O R)) :=
    (hw.mul ((Lp.aestronglyMeasurable error).norm.pow 2)).restrict
  have hsMeas : AEStronglyMeasurable (sourceEnergy O τ α shifted)
      (volume.restrict (Metric.ball O R)) :=
    (hw.mul ((Lp.aestronglyMeasurable shifted).norm.pow 2)).restrict
  have heq : (shifted : Configuration N → PhotonFock) =ᵐ[volume.restrict (Metric.ball O R)]
      fun X => f X - error X := ae_restrict_of_ae (Lp.coeFn_sub f error)
  have hnorm : (fun X => ‖error X‖ ^ 2) =ᵐ[volume.restrict (Metric.ball O R)]
      fun X => E ^ 2 * ‖ψ X‖ ^ 2 :=
    ae_restrict_of_ae (EnergyShiftAbsorption.lp_real_smul_norm_sq_ae E ψ)
  have hsmall : ∀ᵐ X ∂volume.restrict (Metric.ball O R),
      2080 * sourceEnergy O τ α error X ≤ massEnergy O τ α u X := by
    filter_upwards [ae_restrict_mem measurableSet_ball, hnorm] with X hX hn
    have hc := centered_weight_shift_bound hX hRone hα hτ0 hE hratio
    exact (congrArg (fun z : ℝ => 2080 * (centeredSourceWeight O τ α X * z)) hn).le.trans
      (EnergyShiftAbsorption.weighted_point hc (sq_nonneg ‖ψ X‖))
  have hshift : IntegrableOn (sourceEnergy O τ α shifted) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, massEnergy O τ α u X) ≤
        2080 * ∫ X in Metric.ball O R, sourceEnergy O τ α shifted X :=
    EnergyShiftAbsorption.absorb hw0 hm.1 he.1 heMeas hsMeas heq hsmall hm.2
  have hm0 : ∀ᵐ X ∂volume.restrict (Metric.ball O R), 0 ≤ massEnergy O τ α u X := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
    exact mul_nonneg (weights_nonneg_on_ball hτ0 hα hRone hX).1 (sq_nonneg _)
  have hs0 : ∀ᵐ X ∂volume.restrict (Metric.ball O R), 0 ≤ sourceEnergy O τ α shifted X :=
    hw0.mono fun X hx => mul_nonneg hx (sq_nonneg _)
  have hline := EnergyShiftAbsorption.lintegral_bound hm.1 hshift.1 hm0 hs0 hshift.2
  have hmEq := mass_eq O τ α u
  have hsEq := source_eq O τ α shifted
  have hmi := hm.1.congr (Filter.EventuallyEq.of_eq hmEq.symm)
  have hsi := hshift.1.congr (Filter.EventuallyEq.of_eq hsEq)
  have hmInt := congrArg (fun z : Configuration N → ℝ =>
    ∫⁻ X in Metric.ball O R, ENNReal.ofReal (z X)) hmEq
  have hsInt := congrArg (fun z : Configuration N → ℝ =>
    ∫⁻ X in Metric.ball O R, ENNReal.ofReal (z X)) hsEq
  exact ⟨hmi, hsi, hmInt.le.trans (hline.trans_eq
    (congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal 2080 * z) hsInt))⟩

end PfHk.PhysicalOperatorCarlemanBridge
