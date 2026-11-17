import GptLean.TransformationsGaugeWeakH1
import GptLean.PhysicalPFReference
import GptLean.PhysicalFockSeparable
import Mathlib.Analysis.Normed.Operator.Banach

/-! Article-regular weak gauges preserve the full Pauli--Fierz reference
domain. Continuity follows from the closed graph theorem and the proved
intertwining with the unitary multiplication operator on the wave space. -/

noncomputable section

namespace GptLean.TransformationsGauge.WeakSpatialGauge

open MeasureTheory Filter SymmetricLift TransformationsPhase PhysicalFock PhysicalPFReference
open scoped ENNReal Topology InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000

section MultiplicationPhase

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A scalar phase preserves an arbitrary scalar multiplication graph. -/
def multiplicationGraphPhase (μ : Measure X) (a : X → ℂ) {θ : X → ℝ}
    (hθ : AEStronglyMeasurable θ μ) (u : PhysicalMultiplicationGraph.GraphSpace μ (H := H) a) :
    PhysicalMultiplicationGraph.GraphSpace μ (H := H) a :=
  ⟨(phase hθ u.val.1, phase hθ u.val.2), by
    change ∀ᵐ x ∂μ, phase hθ u.val.2 x = a x • phase hθ u.val.1 x
    filter_upwards [u.property, phase_ae hθ u.val.1, phase_ae hθ u.val.2]
      with x hx h₁ h₂
    exact h₂.trans ((congrArg (fun v : H => factor θ x • v) hx).trans
      ((smul_comm (factor θ x) (a x) (u.val.1 x)).trans
        (congrArg (fun v : H => a x • v) h₁.symm)))⟩

end MultiplicationPhase

variable (G : WeakSpatialGauge) {N : ℕ} (V : Position (Fin N × Fin 3) → ℝ)

abbrev wavePhase : WaveSpace (Fin N × Fin 3) ≃ₗᵢ[ℂ] WaveSpace (Fin N × Fin 3) :=
  phase (G.configurationAngle_measurable N)

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

def radiationPhase : RadiationGraph (Fin N × Fin 3) ≃ₗᵢ[ℂ] RadiationGraph (Fin N × Fin 3) :=
  phase (G.configurationAngle_measurable N)

theorem radiationPhase_value (u : RadiationGraph (Fin N × Fin 3)) :
    spatialRadiationInclusion volume (G.radiationPhase u) =
      G.wavePhase (spatialRadiationInclusion volume u) :=
  compLpL_phase (G.configurationAngle_measurable N) radiationGraphInclusion u

theorem radiationPhase_output (u : RadiationGraph (Fin N × Fin 3)) :
    spatialRadiationDerivative volume (G.radiationPhase u) =
      G.wavePhase (spatialRadiationDerivative volume u) :=
  compLpL_phase (G.configurationAngle_measurable N) radiationGraphDerivative u

def potentialPhase (u : PotentialGraph (Fin N × Fin 3) V) : PotentialGraph (Fin N × Fin 3) V :=
  multiplicationGraphPhase volume (fun x => (Real.sqrt (V x) : ℂ))
    (G.configurationAngle_measurable N) u

theorem potentialPhase_value (u : PotentialGraph (Fin N × Fin 3) V) :
    PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _ (G.potentialPhase V u) =
      G.wavePhase (PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _ u) := rfl

theorem potentialPhase_output (u : PotentialGraph (Fin N × Fin 3) V) :
    PhysicalMultiplicationGraph.output (H := PhotonFock) volume _ (G.potentialPhase V u) =
      G.wavePhase (PhysicalMultiplicationGraph.output (H := PhotonFock) volume _ u) := rfl

/-- The gauge transformation on all three coordinates of the common PF domain. -/
def gaugeReference (u : Reference (Fin N × Fin 3) V) : Reference (Fin N × Fin 3) V :=
  ⟨(G.gaugeH1 (electronic (Fin N × Fin 3) V u),
      G.radiationPhase (radiationSource (Fin N × Fin 3) V u),
      G.potentialPhase V (potentialSource (Fin N × Fin 3) V u)), by
    change (ElectronicH1Complex.value (G.gaugeH1 (electronic (Fin N × Fin 3) V u)) -
        spatialRadiationInclusion volume (G.radiationPhase (radiationSource (Fin N × Fin 3) V u)),
      ElectronicH1Complex.value (G.gaugeH1 (electronic (Fin N × Fin 3) V u)) -
        PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _
          (G.potentialPhase V (potentialSource (Fin N × Fin 3) V u))) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((G.value_gaugeH1 _).trans
        ((congrArg G.wavePhase (radiation_matches (Fin N × Fin 3) V u).symm).trans
          (G.radiationPhase_value _).symm))
    · exact sub_eq_zero.mpr ((G.value_gaugeH1 _).trans
        ((congrArg G.wavePhase (potential_matches (Fin N × Fin 3) V u).symm).trans
          (G.potentialPhase_value V _).symm))⟩

theorem inclusion_gaugeReference (u : Reference (Fin N × Fin 3) V) :
    inclusion (Fin N × Fin 3) V (G.gaugeReference V u) =
      G.wavePhase (inclusion (Fin N × Fin 3) V u) := G.value_gaugeH1 _

theorem radiation_gaugeReference (u : Reference (Fin N × Fin 3) V) :
    radiation (Fin N × Fin 3) V (G.gaugeReference V u) =
      G.wavePhase (radiation (Fin N × Fin 3) V u) := G.radiationPhase_output _

theorem potential_gaugeReference (u : Reference (Fin N × Fin 3) V) :
    potential (Fin N × Fin 3) V (G.gaugeReference V u) =
      G.wavePhase (potential (Fin N × Fin 3) V u) := rfl

def gaugeReferenceLinear : Reference (Fin N × Fin 3) V →ₗ[ℂ] Reference (Fin N × Fin 3) V where
  toFun := G.gaugeReference V
  map_add' u v := by
    apply inclusion_injective (Fin N × Fin 3) V
    simp only [G.inclusion_gaugeReference, map_add]
  map_smul' c u := by
    apply inclusion_injective (Fin N × Fin 3) V
    simp only [G.inclusion_gaugeReference, map_smul, RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
theorem gaugeReference_continuous : Continuous (G.gaugeReference V) := by
  change Continuous (G.gaugeReferenceLinear V)
  refine LinearMap.continuous_of_seq_closed_graph (𝕜 := ℂ)
    (E := Reference (Fin N × Fin 3) V) (F := Reference (Fin N × Fin 3) V)
    (G.gaugeReferenceLinear V) ?_
  intro u a b hu hb
  apply inclusion_injective (Fin N × Fin 3) V
  have h₁ := ((inclusion (Fin N × Fin 3) V).continuous.tendsto b).comp hb
  have h₂ := (G.wavePhase.continuous.tendsto (inclusion (Fin N × Fin 3) V a)).comp
    (((inclusion (Fin N × Fin 3) V).continuous.tendsto a).comp hu)
  have heq : (fun n => inclusion (Fin N × Fin 3) V (G.gaugeReferenceLinear V (u n))) =
      fun n => G.wavePhase (inclusion (Fin N × Fin 3) V (u n)) := by
    funext n
    exact G.inclusion_gaugeReference V _
  exact (tendsto_nhds_unique (h₁.congr' (Eventually.of_forall fun n => congrFun heq n)) h₂).trans
    (G.inclusion_gaugeReference V a).symm

def gaugeReferenceMap : Reference (Fin N × Fin 3) V →L[ℂ] Reference (Fin N × Fin 3) V :=
  ⟨G.gaugeReferenceLinear V, G.gaugeReference_continuous V⟩

def gradientSource (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    WaveSpace (Fin N × Fin 3) :=
  (G.gradient_source_memLp (electronic (Fin N × Fin 3) V u) q).toLp
    (fun x => G.gradient q.2 (particle x q.1) • inclusion (Fin N × Fin 3) V u x)

theorem gradientSource_ae (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    G.gradientSource V q u =ᵐ[volume]
      fun x => G.gradient q.2 (particle x q.1) • inclusion (Fin N × Fin 3) V u x :=
  (G.gradient_source_memLp (electronic (Fin N × Fin 3) V u) q).coeFn_toLp

theorem ordinary_gaugeReference (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    ordinary (Fin N × Fin 3) V q (G.gaugeReference V u) =
      G.wavePhase (ordinary (Fin N × Fin 3) V q u + Complex.I • G.gradientSource V q u) := by
  apply Lp.ext
  filter_upwards [G.derivative_gaugeH1_ae (electronic (Fin N × Fin 3) V u) q,
    phase_ae (G.configurationAngle_measurable N)
      (ordinary (Fin N × Fin 3) V q u + Complex.I • G.gradientSource V q u),
    Lp.coeFn_add (ordinary (Fin N × Fin 3) V q u) (Complex.I • G.gradientSource V q u),
    Lp.coeFn_smul Complex.I (G.gradientSource V q u), G.gradientSource_ae V q u]
      with x hx h₁ h₂ h₃ h₄
  change ElectronicH1Complex.derivative q (G.gaugeH1 (electronic (Fin N × Fin 3) V u)) x = _
  have hsum :
      (ordinary (Fin N × Fin 3) V q u + Complex.I • G.gradientSource V q u) x =
        ordinary (Fin N × Fin 3) V q u x +
          Complex.I • (G.gradient q.2 (particle x q.1) • inclusion (Fin N × Fin 3) V u x) :=
    h₂.trans (congrArg (fun v : PhotonFock => ordinary (Fin N × Fin 3) V q u x + v)
      (h₃.trans (congrArg (fun v : PhotonFock => Complex.I • v) h₄)))
  exact hx.trans ((h₁.trans (congrArg₂ (fun (c : ℂ) (v : PhotonFock) => c • v)
    (G.factor_configurationAngle N x) hsum)).symm)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)

theorem field_gaugeReference (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    field (Fin N × Fin 3) V C κ hκ M hbound q (G.gaugeReference V u) =
      G.wavePhase (field (Fin N × Fin 3) V C κ hκ M hbound q u) := by
  apply Lp.ext
  filter_upwards [spatialField_ae volume C (κ q) (hκ q) M (hbound q)
      (G.radiationPhase (radiationSource (Fin N × Fin 3) V u)),
    phase_ae (G.configurationAngle_measurable N) (radiationSource (Fin N × Fin 3) V u),
    phase_ae (G.configurationAngle_measurable N) (field (Fin N × Fin 3) V C κ hκ M hbound q u),
    spatialField_ae volume C (κ q) (hκ q) M (hbound q) (radiationSource (Fin N × Fin 3) V u)]
      with x h₁ h₂ h₃ h₄
  change spatialField volume C (κ q) (hκ q) M (hbound q)
    (G.radiationPhase (radiationSource (Fin N × Fin 3) V u)) x = _
  exact h₁.trans ((congrArg (kernelField C (κ q x)) h₂).trans
    ((map_smul (kernelField C (κ q x)) (factor (G.configurationAngle N) x)
      (radiationSource (Fin N × Fin 3) V u x)).trans
        ((congrArg (fun v : PhotonFock => factor (G.configurationAngle N) x • v) h₄.symm).trans
          h₃.symm)))

private theorem covariant_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (d g f : E) (e : ℂ) :
    (-Complex.I) • L (d + Complex.I • g) - e • L f = L ((-Complex.I) • d - e • f + g) := by
  simp only [map_add, map_sub, map_smul, smul_add, smul_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  abel

theorem covariant_gaugeReference (e : ℝ) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) V) :
    covariant (Fin N × Fin 3) V C κ hκ M hbound e q (G.gaugeReference V u) =
      G.wavePhase (covariant (Fin N × Fin 3) V C κ hκ M hbound e q u + G.gradientSource V q u) :=
  (covariant_apply (Fin N × Fin 3) V C κ hκ M hbound e q (G.gaugeReference V u)).trans
    ((congrArg₂ (fun a b : WaveSpace (Fin N × Fin 3) => (-Complex.I) • a - (e : ℂ) • b)
      (G.ordinary_gaugeReference V q u) (G.field_gaugeReference V C κ hκ M hbound q u)).trans
      ((covariant_algebra G.wavePhase (ordinary (Fin N × Fin 3) V q u)
        (G.gradientSource V q u) (field (Fin N × Fin 3) V C κ hκ M hbound q u) (e : ℂ)).trans
        (congrArg (fun z : WaveSpace (Fin N × Fin 3) => G.wavePhase (z + G.gradientSource V q u))
          (covariant_apply (Fin N × Fin 3) V C κ hκ M hbound e q u).symm)))

private theorem norm_add_sq_re (a b : WaveSpace (Fin N × Fin 3)) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (⟪a, b⟫_ℂ).re + ‖b‖ ^ 2 := by
  simpa only [RCLike.re_to_complex] using norm_add_sq (𝕜 := ℂ) a b

theorem covariant_norm_sq_gaugeReference (e : ℝ) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) V) :
    ‖covariant (Fin N × Fin 3) V C κ hκ M hbound e q (G.gaugeReference V u)‖ ^ 2 =
      ‖covariant (Fin N × Fin 3) V C κ hκ M hbound e q u‖ ^ 2 +
        2 * (⟪covariant (Fin N × Fin 3) V C κ hκ M hbound e q u,
          G.gradientSource V q u⟫_ℂ).re + ‖G.gradientSource V q u‖ ^ 2 :=
  (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ‖w‖ ^ 2)
    (G.covariant_gaugeReference V C κ hκ M hbound e q u)).trans
    ((congrArg (fun t : ℝ => t ^ 2) (G.wavePhase.norm_map _)).trans (norm_add_sq_re _ _))

theorem kineticEnergy_gaugeReference (e : ℝ) (u : Reference (Fin N × Fin 3) V) :
    kineticEnergy (Fin N × Fin 3) V C κ hκ M hbound e (G.gaugeReference V u) =
      kineticEnergy (Fin N × Fin 3) V C κ hκ M hbound e u +
        ∑ q, (⟪covariant (Fin N × Fin 3) V C κ hκ M hbound e q u,
          G.gradientSource V q u⟫_ℂ).re +
        (1 / 2 : ℝ) * ∑ q, ‖G.gradientSource V q u‖ ^ 2 := by
  unfold kineticEnergy
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl
    fun q (_ : q ∈ Finset.univ) => G.covariant_norm_sq_gaugeReference V C κ hκ M hbound e q u
  refine (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) h).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem energy_gaugeReference (e : ℝ) (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κ hκ M hbound e (G.gaugeReference V u) =
      energy (Fin N × Fin 3) V C κ hκ M hbound e u +
        ∑ q, (⟪covariant (Fin N × Fin 3) V C κ hκ M hbound e q u,
          G.gradientSource V q u⟫_ℂ).re +
        (1 / 2 : ℝ) * ∑ q, ‖G.gradientSource V q u‖ ^ 2 := by
  have hr : ‖radiation (Fin N × Fin 3) V (G.gaugeReference V u)‖ =
      ‖radiation (Fin N × Fin 3) V u‖ :=
    (congrArg norm (G.radiation_gaugeReference V u)).trans (G.wavePhase.norm_map _)
  have hp : ‖potential (Fin N × Fin 3) V (G.gaugeReference V u)‖ =
      ‖potential (Fin N × Fin 3) V u‖ :=
    (congrArg norm (G.potential_gaugeReference V u)).trans (G.wavePhase.norm_map _)
  unfold energy
  refine (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (G.kineticEnergy_gaugeReference V C κ hκ M hbound e u) (congrArg (· ^ 2) hr))
    (congrArg (· ^ 2) hp)).trans ?_
  ring

private theorem wavePhase_neg_apply (w : WaveSpace (Fin N × Fin 3)) :
    G.neg.wavePhase (G.wavePhase w) = w := by
  have h := (phase (E := PhotonFock) (G.configurationAngle_measurable N)).symm_apply_apply w
  rw [phase_symm_apply] at h
  simpa only [wavePhase, G.configurationAngle_neg] using h

theorem neg_gaugeReference (u : Reference (Fin N × Fin 3) V) :
    G.neg.gaugeReference V (G.gaugeReference V u) = u :=
  inclusion_injective (Fin N × Fin 3) V
    ((G.neg.inclusion_gaugeReference V (G.gaugeReference V u)).trans
      ((congrArg G.neg.wavePhase (G.inclusion_gaugeReference V u)).trans
        (G.wavePhase_neg_apply (inclusion (Fin N × Fin 3) V u))))

attribute [irreducible] gaugeReference

end GptLean.TransformationsGauge.WeakSpatialGauge
