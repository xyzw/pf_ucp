import PfHk.PauliCarlemanFinite
import PfHk.PauliMagneticPhysicalWeighted
import PfHk.PhysicalOperatorCarlemanBridge

/-! The actual quantum Zeeman error is small relative to the physical
orbital Carleman source. The mass and radiation terms are extracted from
the proved orbital estimate. No magnetic error bound is an assumption. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCarlemanQuantum

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain PfHk.PhysicalCarlemanInput
  PfHk.PhysicalDyadicEnergy PfHk.PhysicalExternalEnergy
  PfHk.PhysicalExternalDensityLocality PfHk.SmoothCutoffBounds PfHk.PauliSpin

attribute [local instance] PhysicalLocalExternalCarleman.endpointPhotonRealInner

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

private theorem indicator_weighted_sum {X S : Type*} [Fintype S]
    (U : Set X) (w : X → ℝ) (q : S → X → ℝ) :
    (fun x => U.indicator w x * ∑ s, q s x) =
      U.indicator (fun x => ∑ s, w x * q s x) := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [Set.indicator_of_mem hx, Finset.mul_sum]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

private theorem indicator_weighted_sum_bound {X S : Type*}
    [MeasurableSpace X] [Fintype S] (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (w : X → ℝ) (q : S → X → ℝ) (K : ℝ) (source : S → ℝ)
    (hi : ∀ s, IntegrableOn (fun x => w x * q s x) U μ)
    (hb : ∀ s, (∫ x in U, w x * q s x ∂μ) ≤ K * source s) :
    Integrable (fun x => U.indicator w x * ∑ s, q s x) μ ∧
      (∫ x, U.indicator w x * ∑ s, q s x ∂μ) ≤ K * ∑ s, source s := by
  have hsum : IntegrableOn (fun x => ∑ s, w x * q s x) U μ :=
    integrable_finsetSum _ (fun s _ => hi s)
  have heq := indicator_weighted_sum U w q
  refine ⟨((integrable_indicator_iff hU).mpr hsum).congr
    (Filter.EventuallyEq.of_eq heq.symm), ?_⟩
  rw [heq, integral_indicator hU, integral_finsetSum _ (fun s _ => hi s), Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => hb s

private theorem indicator_weighted_sum_result {X S : Type*}
    [MeasurableSpace X] [Fintype S] (μ : Measure X) (U : Set X) (hU : MeasurableSet U)
    (w : X → ℝ) (q : S → X → ℝ) (bound : ℝ)
    (h : Integrable (fun x => U.indicator w x * ∑ s, q s x) μ ∧
      (∫ x, U.indicator w x * ∑ s, q s x ∂μ) ≤ bound) :
    IntegrableOn (fun x => ∑ s, w x * q s x) U μ ∧
      (∫ x in U, ∑ s, w x * q s x ∂μ) ≤ bound := by
  have heq := indicator_weighted_sum U w q
  have hi := h.1.congr (Filter.EventuallyEq.of_eq heq)
  refine ⟨(integrable_indicator_iff hU).mp hi, ?_⟩
  exact (integral_indicator hU).symm.le.trans
    ((integral_congr_ae (Filter.EventuallyEq.of_eq heq)).symm.le.trans h.2)

private theorem weighted_domination {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w v q : X → ℝ) (a : ℝ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hq : ∀ x, 0 ≤ q x)
    (hweight : ∀ᵐ x ∂μ, w x ≤ a * v x)
    (hmeas : AEStronglyMeasurable (fun x => w x * q x) μ)
    (hi : Integrable (fun x => v x * q x) μ) :
    Integrable (fun x => w x * q x) μ ∧
      (∫ x, w x * q x ∂μ) ≤ a * ∫ x, v x * q x ∂μ := by
  have hb : ∀ᵐ x ∂μ, w x * q x ≤ a * (v x * q x) := by
    filter_upwards [hweight] with x hx
    exact (mul_le_mul_of_nonneg_right hx (hq x)).trans_eq (mul_assoc _ _ _)
  have hf : Integrable (fun x => w x * q x) μ := (hi.const_mul a).mono' hmeas (by
    filter_upwards [hw, hb] with x hx hxb
    exact (Real.norm_of_nonneg (mul_nonneg hx (hq x))).le.trans hxb)
  exact ⟨hf, (integral_mono_ae hf (hi.const_mul a) hb).trans_eq (integral_const_mul _ _)⟩

private theorem mass_coefficient_identity (σ τ : ℝ) :
    (σ / τ ^ 3) * 520 = 520 * σ * τ ^ (-3 : ℝ) := by
  rw [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
  simp only [div_eq_mul_inv]
  ring

private theorem magnetic_arithmetic {K a b r m f : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : r ≤ 520 * f) (hm : m ≤ 520 * f) :
    K * (a * r + b * m) ≤ (K * 520 * (a + b)) * f := by
  calc
    _ ≤ K * (a * (520 * f) + b * (520 * f)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hr ha) (mul_le_mul_of_nonneg_left hm hb)) hK
    _ = _ := by ring

private theorem coefficient_identity (K r σ τ : ℝ) :
    K * 520 * (r ^ 2 / (2 * τ) + σ / τ ^ 3) =
      (260 * K * r ^ 2) * τ ^ (-1 : ℝ) + (520 * K * σ) * τ ^ (-3 : ℝ) := by
  rw [Real.rpow_neg_one, Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem radiation_nonneg {I : Type*} [Fintype I] {τ α : ℝ}
    (hτ : 0 ≤ τ) (X : PolarCalculus.Position I) :
    0 ≤ CarlemanSpatialDensity.radiationWeight τ α X :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hτ)

private theorem indicator_weight_comparisons {I : Type} [Fintype I] [DecidableEq I]
    {O : PolarCalculus.Position I} {R r₀ τ α σ : ℝ}
    (hτ : 0 < τ) (hα : 0 < α) (hRr : R ≤ r₀) (hrone : r₀ < 1)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ σ)
    (X : PolarCalculus.Position I) :
    (Metric.ball O R).indicator (centeredSourceWeight O τ α) X ≤
        (r₀ ^ 2 / (2 * τ)) * (Metric.ball O R).indicator (centeredRadiationWeight O τ α) X ∧
      (Metric.ball O R).indicator (centeredSourceWeight O τ α) X ≤
        (σ / τ ^ 3) * (Metric.ball O R).indicator (centeredMassWeight O τ α) X := by
  classical
  by_cases hx : X ∈ Metric.ball O R
  · simp only [Set.indicator_of_mem hx]
    have hn : ‖X - O‖ ≤ r₀ := by
      exact (show ‖X - O‖ < R from (dist_eq_norm X O) ▸ hx).le.trans hRr
    refine ⟨PauliCarlemanWeights.source_le_radiation hτ hn, ?_⟩
    by_cases hz : ‖X - O‖ = 0
    · simp only [centeredSourceWeight, CarlemanSpatialDensity.sourceWeight,
        centeredMassWeight, CarlemanSpatialDensity.massWeight, hz, zero_pow (by decide : (2 : ℕ) ≠ 0),
        inv_zero, mul_zero]
      exact le_rfl
    · have hn0 : 0 < ‖X - O‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hb := CarlemanWeights.beta_pos hα
        (neg_pos.mpr (Real.log_neg hn0 (hn.trans_lt hrone)))
      have hquot := (div_le_iff₀ hb).mp (hratio _ hn0 hn)
      have hpow : ‖X - O‖ ^ 4 ≤ σ * CarlemanWeights.beta α (-Real.log ‖X - O‖) := by
        simpa only [Real.rpow_ofNat] using hquot
      exact PauliCarlemanWeights.source_le_mass hτ hn0 hpow
  · simp only [Set.indicator_of_notMem hx, mul_zero, le_refl, and_self]

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion covariant radiation roughMultiply
  externalCovariant PauliMagneticOperator.quantum

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  {O₀ : Configuration N} {ρ : ℝ} (a : PhysicalLocalExternalCoefficients.Data O₀ ρ)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))

theorem radiation_bound_of_estimate {O : Configuration N} {family : BufferedFamily O}
    {R : ℝ} {hR : 0 < R} {τ α C₂ C₂e : ℝ}
    {u : Reference (Fin N × Fin 3) (fun _ => 0)}
    {hu : ExternalDomain (fun _ => 0) a.vector a.positive a.negative u}
    {f : WaveSpace (Fin N × Fin 3)}
    (he : PhysicalLocalExternalCarleman.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hRone : R < 1)
    (hsupp : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    IntegrableOn (radiationEnergy O τ α u) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, radiationEnergy O τ α u X) ≤
        520 * ∫ X in Metric.ball O R, sourceEnergy O τ α f X := by
  have hr0 (X : Configuration N) : 0 ≤ radiationEnergy O τ α u X :=
    mul_nonneg (radiation_nonneg hτ (X - O)) (sq_nonneg _)
  have hrd : ∀ᵐ X ∂volume.restrict (Metric.ball O R), radiationEnergy O τ α u X ≤
      density F χ C e a.vector a.positive a.negative O τ α u hu X := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
    have hm : 0 ≤ massEnergy O τ α u X :=
      mul_nonneg (weights_nonneg_on_ball hτ hα hRone hX).1 (sq_nonneg _)
    have hk : 0 ≤ positiveKinetic F χ C e a.vector a.positive a.negative O τ α u hu X :=
      mul_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact le_add_of_nonneg_left (add_nonneg hm hk)
  have hw : Measurable (centeredRadiationWeight O τ α) := by
    unfold centeredRadiationWeight CarlemanSpatialDensity.radiationWeight CarlemanWeights.weight
    fun_prop
  have hrMeas : AEStronglyMeasurable (radiationEnergy O τ α u) volume :=
    hw.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable
      (radiation (Fin N × Fin 3) (fun _ => 0) u)).norm.pow 2)
  have hi : IntegrableOn (radiationEnergy O τ α u) (Metric.ball O R) :=
    he.2.1.integrableOn.mono' hrMeas.restrict (by
      filter_upwards [hrd] with X hx
      exact (Real.norm_of_nonneg (hr0 X)).le.trans hx)
  have hd0 := density_nonneg F χ C e a.vector a.positive a.negative hτ hα hRone u hu hsupp
  exact ⟨hi, (integral_mono_ae hi he.2.1.integrableOn hrd).trans
    ((setIntegral_le_integral he.2.1 hd0).trans he.2.2.1)⟩

def radiationCoefficient (hUV : CarlemanUV χ) (r₀ : ℝ) : ℝ :=
  260 * PauliMagneticWeighted.constant (N := N) F χ hUV e * r₀ ^ 2

def massCoefficient (hUV : CarlemanUV χ) (σ : ℝ) : ℝ :=
  520 * PauliMagneticWeighted.constant (N := N) F χ hUV e * σ

theorem radiationCoefficient_nonneg (hUV : CarlemanUV χ) (r₀ : ℝ) :
    0 ≤ radiationCoefficient (N := N) F χ e hUV r₀ :=
  mul_nonneg (mul_nonneg (by norm_num) (PauliMagneticWeighted.constant_nonneg F χ hUV e))
    (sq_nonneg _)

theorem massCoefficient_nonneg (hUV : CarlemanUV χ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ massCoefficient (N := N) F χ e hUV σ :=
  mul_nonneg (mul_nonneg (by norm_num) (PauliMagneticWeighted.constant_nonneg F χ hUV e)) hσ

/-- The zero-order term controls the weighted wave source itself. -/
theorem mass_source_bound_of_estimate
    {O : Configuration N} {family : BufferedFamily O} {R r₀ τ α σ C₂ C₂e : ℝ}
    {hR : 0 < R} (hτ : 0 < τ) (hα : 0 < α) (hRr : R ≤ r₀) (hrone : r₀ < 1)
    (hσ : 0 ≤ σ)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ σ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hsupp : ∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) :
    IntegrableOn (fun X => ∑ s, sourceEnergy O τ α
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) X) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, ∑ s, sourceEnergy O τ α
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) X) ≤
        (520 * σ * τ ^ (-3 : ℝ)) *
            ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X := by
  let U := Metric.ball O R
  let src := fun s => ∫ X in U, sourceEnergy O τ α (f s) X
  have hm (s : SpinIndex N) := PhysicalOperatorCarlemanBridge.mass_bound_of_estimate
    F χ C e a spectral (he.1 s) hτ.le hα (hRr.trans_lt hrone) (hsupp s)
  have hM := indicator_weighted_sum_bound volume U measurableSet_ball
    (centeredMassWeight O τ α)
    (fun s X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    520 src (fun s => (hm s).1) (fun s => (hm s).2)
  have hb : 0 ≤ σ / τ ^ 3 := div_nonneg hσ (pow_nonneg hτ.le _)
  have hw0 : ∀ᵐ X ∂volume, 0 ≤ U.indicator (centeredSourceWeight O τ α) X := by
    apply ae_of_all
    intro X
    by_cases hx : X ∈ U
    · simpa only [Set.indicator_of_mem hx] using PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α X
    · simp only [Set.indicator_of_notMem hx, le_refl]
  have hweight := indicator_weight_comparisons (I := Fin N × Fin 3) (O := O)
    hτ hα hRr hrone hratio
  have hw : Measurable (U.indicator (centeredSourceWeight O τ α)) :=
    (PhysicalSourceAbsorption.centeredSourceWeight_measurable O τ α).indicator measurableSet_ball
  have hmeas : AEStronglyMeasurable
      (fun X => U.indicator (centeredSourceWeight O τ α) X *
        ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) volume :=
    hw.aestronglyMeasurable.mul (Finset.univ.aestronglyMeasurable_fun_sum fun s _ =>
      (Lp.aestronglyMeasurable (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).norm.pow 2)
  have hbound := weighted_domination volume (U.indicator (centeredSourceWeight O τ α))
    (U.indicator (centeredMassWeight O τ α))
    (fun X => ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    (σ / τ ^ 3) hw0 (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (ae_of_all _ fun X => (hweight X).2) hmeas hM.1
  have hfinal := hbound.2.trans (mul_le_mul_of_nonneg_left hM.2 hb)
  have heq : (σ / τ ^ 3) * (520 * ∑ s, src s) =
      (520 * σ * τ ^ (-3 : ℝ)) * ∑ s, src s :=
    (mul_assoc _ _ _).symm.trans (congrArg (fun z : ℝ => z * ∑ s, src s)
      (mass_coefficient_identity σ τ))
  exact indicator_weighted_sum_result volume U measurableSet_ball (centeredSourceWeight O τ α)
    (fun s X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) _
    ⟨hbound.1, hfinal.trans_eq heq⟩

/-- Both source integrability and the tau-decaying bound follow from the
actual orbital estimates and the first ultraviolet moment. -/
theorem source_bound_of_estimate (hUV : CarlemanUV χ)
    {O : Configuration N} {family : BufferedFamily O} {R r₀ τ α σ C₂ C₂e : ℝ}
    {hR : 0 < R} (hτ : 0 < τ) (hα : 0 < α) (hRr : R ≤ r₀) (hrone : r₀ < 1)
    (hσ : 0 ≤ σ)
    (hratio : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      r ^ (4 : ℝ) / CarlemanWeights.beta α (-Real.log r) ≤ σ)
    (u : PauliReference.Ref N)
    (hu : ∀ s, ExternalDomain (fun _ => 0) a.vector a.positive a.negative (u s))
    (f : SpinIndex N → WaveSpace (Fin N × Fin 3))
    (he : PauliCarlemanFinite.Estimate F χ C e a spectral family R hR τ α C₂ C₂e u hu f)
    (hsupp : ∀ s, AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) O R) :
    IntegrableOn (fun X => ∑ s, sourceEnergy O τ α
      (PauliMagneticOperator.quantum F χ hUV C e u s) X) (Metric.ball O R) ∧
      (∫ X in Metric.ball O R, ∑ s, sourceEnergy O τ α
        (PauliMagneticOperator.quantum F χ hUV C e u s) X) ≤
        (radiationCoefficient (N := N) F χ e hUV r₀ * τ ^ (-1 : ℝ) +
          massCoefficient (N := N) F χ e hUV σ * τ ^ (-3 : ℝ)) *
            ∑ s, ∫ X in Metric.ball O R, sourceEnergy O τ α (f s) X := by
  let U := Metric.ball O R
  let src := fun s => ∫ X in U, sourceEnergy O τ α (f s) X
  have hm (s : SpinIndex N) := PhysicalOperatorCarlemanBridge.mass_bound_of_estimate
    F χ C e a spectral (he.1 s) hτ.le hα (hRr.trans_lt hrone) (hsupp s)
  have hr (s : SpinIndex N) := radiation_bound_of_estimate
    F χ C e a spectral (he.1 s) hτ.le hα (hRr.trans_lt hrone) (hsupp s)
  have hM := indicator_weighted_sum_bound volume U measurableSet_ball
    (centeredMassWeight O τ α)
    (fun s X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    520 src (fun s => (hm s).1) (fun s => (hm s).2)
  have hR := indicator_weighted_sum_bound volume U measurableSet_ball
    (centeredRadiationWeight O τ α)
    (fun s X => ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    520 src (fun s => (hr s).1) (fun s => (hr s).2)
  have ha : 0 ≤ r₀ ^ 2 / (2 * τ) := div_nonneg (sq_nonneg _) (by positivity)
  have hb : 0 ≤ σ / τ ^ 3 := div_nonneg hσ (pow_nonneg hτ.le _)
  have hw0 : ∀ᵐ X ∂volume, 0 ≤ U.indicator (centeredSourceWeight O τ α) X := by
    apply ae_of_all
    intro X
    by_cases hx : X ∈ U
    · simpa only [Set.indicator_of_mem hx] using PhysicalSourceAbsorption.centeredSourceWeight_nonneg O τ α X
    · simp only [Set.indicator_of_notMem hx, le_refl]
  have hweight := indicator_weight_comparisons (I := Fin N × Fin 3) (O := O) hτ hα hRr hrone hratio
  have hq := PauliMagneticPhysicalWeighted.source_bound F χ hUV C e u
    (U.indicator (centeredSourceWeight O τ α)) (U.indicator (centeredMassWeight O τ α))
    (U.indicator (centeredRadiationWeight O τ α)) ha hb hw0
    ((PhysicalSourceAbsorption.centeredSourceWeight_measurable O τ α).indicator
      measurableSet_ball).aestronglyMeasurable
    (ae_of_all _ fun X => (hweight X).1) (ae_of_all _ fun X => (hweight X).2) hM.1 hR.1
  have hbound := hq.2.trans (magnetic_arithmetic
    (PauliMagneticWeighted.constant_nonneg F χ hUV e) ha hb hR.2 hM.2)
  have hcoeff : PauliMagneticWeighted.constant (N := N) F χ hUV e * 520 *
      (r₀ ^ 2 / (2 * τ) + σ / τ ^ 3) =
      radiationCoefficient (N := N) F χ e hUV r₀ * τ ^ (-1 : ℝ) +
        massCoefficient (N := N) F χ e hUV σ * τ ^ (-3 : ℝ) :=
    coefficient_identity _ _ _ _
  exact indicator_weighted_sum_result volume U measurableSet_ball (centeredSourceWeight O τ α)
    (fun s X => ‖PauliMagneticOperator.quantum F χ hUV C e u s X‖ ^ 2) _
    ⟨hq.1, hbound.trans_eq (congrArg (fun z : ℝ => z * ∑ s, src s) hcoeff)⟩

end PfHk.PauliCarlemanQuantum

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
