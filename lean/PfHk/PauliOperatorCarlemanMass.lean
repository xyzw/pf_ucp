import PfHk.PauliOperatorCarlemanInput
import PfHk.PhysicalOperatorCarlemanBridge

/-! Passing the checked spin-summed physical estimate to the nonnegative
integral of the actual spin--photon norm. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliOperatorCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliLocalEnergy
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference
  PfHk.PhysicalCutoffCommutator PfHk.SmoothCutoffBounds
  PfHk.PhysicalFieldRegularity PfHk.PhysicalLocalEnergy
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalExternalEnergy
  PfHk.PhysicalExternalDensityLocality PfHk.PhysicalOperatorDomain
  PfHk.PhysicalCarlemanInput
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner
attribute [local irreducible] referenceSubspace inclusion

/-- Weighted squared norms commute with the actual finite Hilbert sum. -/
theorem weighted_bundle_ae {X T H : Type*} [MeasurableSpace X] [Fintype T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (w : X → ℝ) (f : T → Lp H 2 μ) :
    (fun x => w x * ‖FiniteFiberL2.bundle f x‖ ^ 2) =ᵐ[μ]
      fun x => ∑ s, w x * ‖f s x‖ ^ 2 := by
  filter_upwards [FiniteFiberL2.norm_sq_ae f] with x hx
  rw [hx, Finset.mul_sum]

theorem weighted_bundle_integrable {X T H : Type*} [MeasurableSpace X] [Fintype T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (w : X → ℝ) (f : T → Lp H 2 μ)
    (hi : ∀ s, Integrable (fun x => w x * ‖f s x‖ ^ 2) μ) :
    Integrable (fun x => w x * ‖FiniteFiberL2.bundle f x‖ ^ 2) μ :=
  (integrable_finsetSum Finset.univ (fun s _ => hi s)).congr (weighted_bundle_ae w f).symm

theorem weighted_bundle_integral {X T H : Type*} [MeasurableSpace X] [Fintype T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (w : X → ℝ) (f : T → Lp H 2 μ)
    (hi : ∀ s, Integrable (fun x => w x * ‖f s x‖ ^ 2) μ) :
    (∫ x, w x * ‖FiniteFiberL2.bundle f x‖ ^ 2 ∂μ) =
      ∑ s, ∫ x, w x * ‖f s x‖ ^ 2 ∂μ :=
  (integral_congr_ae (weighted_bundle_ae w f)).trans
    (integral_finsetSum Finset.univ (fun s _ => hi s))

variable {N : ℕ}

theorem source_bundle_ae (O : Configuration N) (α τ : ℝ)
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3)) :
    sourceIntegrand O α τ (FiniteFiberL2.bundle f) =ᵐ[volume]
      PauliCarlemanFinite.sourceEnergySum O τ α f := by
  have hw := weighted_bundle_ae
    (fun X : Configuration N => Real.exp (2 * τ * CarlemanWeights.weight α
      (-Real.log (dist X O))) * dist X O ^ 2) f
  refine hw.trans (Filter.Eventually.of_forall fun X => ?_)
  exact Finset.sum_congr rfl fun s _ =>
    (congrFun (PhysicalOperatorCarlemanBridge.source_eq O τ α (f s)) X).symm

theorem mass_bundle_ae (O : Configuration N) (α τ : ℝ) (u : Ref N) :
    UniqueContinuation.radialMassIntegrand (fun X => dist X O)
      (PauliReference.wave u) α τ =ᵐ[volume]
      fun X => ∑ s, massEnergy O τ α (u s) X := by
  filter_upwards [PauliReference.wave_norm_sq_ae u] with X hX
  have hsum : UniqueContinuation.radialMassIntegrand (fun X => dist X O)
      (PauliReference.wave u) α τ X =
      ∑ s, UniqueContinuation.radialMassIntegrand (fun X => dist X O)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) α τ X := by
    simp only [UniqueContinuation.radialMassIntegrand, UniqueContinuation.weightedNormSq,
      hX, Finset.mul_sum]
  exact hsum.trans (Finset.sum_congr rfl fun s _ =>
    congrFun (PhysicalOperatorCarlemanBridge.mass_eq O τ α (u s)) X)

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

/-- The actual spin--photon mass integral follows from the full Pauli
estimate. Its source is the norm of the full coupled source. -/
theorem mass_lintegral_of_estimate {O : Configuration N} {family : BufferedFamily O}
    {R τ α C₂ C₂e : ℝ} {hR : 0 < R}
    {u : Ref N} {f : SpinIndex N → WaveSpace (Fin N × Fin 3)}
    (he : PauliPhysicalCarleman.PhysicalEstimate F χ C e A v c hc spectral
      family R hR τ α C₂ C₂e u f)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : ∀ s, AnnularSupport
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) :
    (∫⁻ X in Metric.ball O R, ENNReal.ofReal
      (UniqueContinuation.radialMassIntegrand (fun X => dist X O)
        (PauliReference.wave u) α τ X)) ≤
      ENNReal.ofReal 2080 * (∫⁻ X in Metric.ball O R, ENNReal.ofReal
        (sourceIntegrand O α τ (FiniteFiberL2.bundle f) X)) := by
  let D := fun s => physicalDomain A v c hc u s
  let d := fun s => density F χ C e (vector A) (positive v c) (negative v c)
    O τ α (u s) (D s)
  let m := fun s => massEnergy O τ α (u s)
  have hm0 (s : SpinIndex N) : 0 ≤ᵐ[volume.restrict (Metric.ball O R)] m s := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
    exact mul_nonneg (weights_nonneg_on_ball hτ hα hRone hX).1 (sq_nonneg _)
  have hmd (s : SpinIndex N) (X : Configuration N) : m s X ≤ d s X := by
    have hk : 0 ≤ positiveKinetic F χ C e (vector A) (positive v c) (negative v c)
        O τ α (u s) (D s) X :=
      mul_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hr : 0 ≤ PhysicalDyadicEnergy.radiationEnergy O τ α (u s) X :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hτ)) (sq_nonneg _)
    exact (le_add_of_nonneg_right hk).trans (le_add_of_nonneg_right hr)
  have hm (s : SpinIndex N) : IntegrableOn (m s) (Metric.ball O R) :=
    (he.2.1 s).integrableOn.mono'
      (((PhysicalOperatorCarlemanBridge.centeredMassWeight_measurable O τ α).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).norm.pow 2)).restrict)
      (by filter_upwards [hm0 s] with X hX
          exact (Real.norm_of_nonneg hX).le.trans (hmd s X))
  have hd0 (s : SpinIndex N) := density_nonneg F χ C e (vector A) (positive v c)
    (negative v c) hτ hα hRone (u s) (D s) (hsupp s)
  have hmb (s : SpinIndex N) : (∫ X in Metric.ball O R, m s X) ≤ ∫ X, d s X :=
    (integral_mono_ae (hm s) (he.2.1 s).integrableOn (Filter.Eventually.of_forall (hmd s))).trans
      (setIntegral_le_integral (he.2.1 s) (hd0 s))
  have hsumint := integral_finsetSum Finset.univ (fun s _ => hm s)
  have hdint := integral_finsetSum Finset.univ (fun s _ => he.2.1 s)
  have hb : (∫ X in Metric.ball O R, ∑ s, m s X) ≤
      2080 * ∫ X in Metric.ball O R, PauliCarlemanFinite.sourceEnergySum O τ α f X :=
    hsumint.le.trans ((Finset.sum_le_sum (fun s _ => hmb s)).trans
      (hdint.symm.le.trans he.2.2.1))
  have hmass : UniqueContinuation.radialMassIntegrand (fun X => dist X O)
      (PauliReference.wave u) α τ =ᵐ[volume.restrict (Metric.ball O R)]
      (fun X => ∑ s, massEnergy O τ α (u s) X) :=
    ae_restrict_of_ae (mass_bundle_ae O α τ u)
  have hsource : sourceIntegrand O α τ (FiniteFiberL2.bundle f) =ᵐ[volume.restrict (Metric.ball O R)]
      PauliCarlemanFinite.sourceEnergySum O τ α f :=
    ae_restrict_of_ae (source_bundle_ae O α τ f)
  have hmi := (integrable_finsetSum Finset.univ (fun s _ => hm s)).congr (Filter.EventuallyEq.symm hmass)
  have hsi := he.1.congr (Filter.EventuallyEq.symm hsource)
  have hmn : 0 ≤ᵐ[volume.restrict (Metric.ball O R)]
      UniqueContinuation.radialMassIntegrand (fun X => dist X O) (PauliReference.wave u) α τ := by
    filter_upwards [hmass, ae_all_iff.mpr hm0] with X hX hn
    exact (Finset.sum_nonneg (fun s _ => hn s)).trans hX.ge
  have hsn : 0 ≤ᵐ[volume.restrict (Metric.ball O R)]
      sourceIntegrand O α τ (FiniteFiberL2.bundle f) :=
    Filter.Eventually.of_forall fun X => by unfold sourceIntegrand; positivity
  have hreal := (integral_congr_ae hmass).le.trans
    (hb.trans_eq (congrArg (fun t : ℝ => 2080 * t) (integral_congr_ae hsource).symm))
  calc
    _ = ENNReal.ofReal (∫ X in Metric.ball O R,
        UniqueContinuation.radialMassIntegrand (fun X => dist X O) (PauliReference.wave u) α τ X) :=
      (ofReal_integral_eq_lintegral_ofReal hmi hmn).symm
    _ ≤ ENNReal.ofReal (2080 * ∫ X in Metric.ball O R,
        sourceIntegrand O α τ (FiniteFiberL2.bundle f) X) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2080),
        ofReal_integral_eq_lintegral_ofReal hsi hsn]

end PfHk.PauliOperatorCarleman
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
