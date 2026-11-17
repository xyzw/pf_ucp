import PfHk.PhysicalLocalExternalCarleman
import PfHk.EnergyShiftAbsorption

/-! The full physical Carleman estimate supplies the precise nonnegative
mass/source inequality used by unique continuation, including real energy shifts. -/

noncomputable section
namespace PfHk.PhysicalOperatorCarlemanBridge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalLocalEnergy PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalExternalEnergy PfHk.PhysicalExternalDensityLocality
  PfHk.PhysicalSourceAbsorption PfHk.SmoothCutoffBounds PfHk.PhysicalOperatorDomain
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

local instance bridgePhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace

private theorem mass_formula (r α τ q : ℝ) :
    τ ^ 3 * (CarlemanWeights.beta α (-Real.log r) * r ^ (-2 : ℝ) *
      Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) * q) =
    Real.exp (2 * τ * CarlemanWeights.weight α (-Real.log r)) * τ ^ 3 *
      CarlemanWeights.beta α (-Real.log r) * (r ^ 2)⁻¹ * q := by
  rw [Real.rpow_neg_ofNat r 2, zpow_neg, zpow_ofNat]
  ring

variable {N : ℕ}

theorem source_eq (O : Configuration N) (τ α : ℝ) (f : WaveSpace (Fin N × Fin 3)) :
    sourceEnergy O τ α f = sourceIntegrand O α τ f := by
  funext X
  simp only [sourceEnergy, centeredSourceWeight, CarlemanSpatialDensity.sourceWeight,
    sourceIntegrand, ← dist_eq_norm]

theorem mass_eq (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    UniqueContinuation.radialMassIntegrand (fun X => dist X O)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) α τ = massEnergy O τ α u := by
  funext X
  simpa only [UniqueContinuation.radialMassIntegrand, UniqueContinuation.weightedNormSq,
    massEnergy, centeredMassWeight, CarlemanSpatialDensity.massWeight, ← dist_eq_norm] using
      mass_formula (dist X O) α τ (‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)

theorem centeredMassWeight_measurable (O : Configuration N) (τ α : ℝ) :
    Measurable (centeredMassWeight O τ α) := by
  unfold centeredMassWeight CarlemanSpatialDensity.massWeight CarlemanWeights.weight CarlemanWeights.beta
  fun_prop

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  {O₀ : Configuration N} {ρ : ℝ} (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

theorem mass_bound_of_estimate {O : Configuration N} {family : BufferedFamily O}
    {R : ℝ} {hR : 0 < R} {τ α C₂ C₂e : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    {f : WaveSpace (Fin N × Fin 3)}
    (he : PhysicalLocalExternalCarleman.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    IntegrableOn (massEnergy O τ α u) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, massEnergy O τ α u X) ≤
        520 * ∫ X in Metric.ball O R, sourceEnergy O τ α f X := by
  have hm0 : ∀ᵐ X ∂volume.restrict (Metric.ball O R), 0 ≤ massEnergy O τ α u X := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
    exact mul_nonneg (weights_nonneg_on_ball hτ hα hRone hX).1 (sq_nonneg _)
  have hmd (X : Configuration N) : massEnergy O τ α u X ≤
      density F χ C e a.vector a.positive a.negative O τ α u hu X := by
    have hk : 0 ≤ positiveKinetic F χ C e a.vector a.positive a.negative O τ α u hu X :=
      mul_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hr : 0 ≤ radiationEnergy O τ α u X :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hτ)) (sq_nonneg _)
    exact (le_add_of_nonneg_right hk).trans (le_add_of_nonneg_right hr)
  have hmMeas : AEStronglyMeasurable (massEnergy O τ α u) volume :=
    (centeredMassWeight_measurable O τ α).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (inclusion (Fin N × Fin 3) (fun _ => 0) u)).norm.pow 2)
  have hm : IntegrableOn (massEnergy O τ α u) (Metric.ball O R) :=
    he.2.1.integrableOn.mono' hmMeas.restrict (by
      filter_upwards [hm0] with X hx
      exact (Real.norm_of_nonneg hx).le.trans (hmd X))
  have hd0 := density_nonneg F χ C e a.vector a.positive a.negative hτ hα hRone u hu hsupp
  have hlocal : (∫ X in Metric.ball O R, massEnergy O τ α u X) ≤
      ∫ X in Metric.ball O R, density F χ C e a.vector a.positive a.negative O τ α u hu X :=
    integral_mono_ae hm he.2.1.integrableOn (ae_of_all _ hmd)
  have hglobalLower : (∫ X in Metric.ball O R, density F χ C e a.vector a.positive a.negative O τ α u hu X) ≤
      ∫ X, density F χ C e a.vector a.positive a.negative O τ α u hu X :=
    setIntegral_le_integral he.2.1 hd0
  exact ⟨hm, hlocal.trans (hglobalLower.trans he.2.2.1)⟩

end PfHk.PhysicalOperatorCarlemanBridge
