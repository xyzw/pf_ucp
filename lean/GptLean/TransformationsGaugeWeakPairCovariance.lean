import GptLean.TransformationsGaugeWeakReference
import GptLean.TransformationsGaugeWeakPair
import GptLean.TransformationsGaugeStates
import GptLean.PhysicalWeightedCurrent

/-! The actual Pauli--Fierz pair transforms by the weak gauge gradient.
The density test needed in the current transformation is allowed to be
unbounded. Its integrability follows from the proved gradient source. -/

noncomputable section

namespace GptLean

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsPhase
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option Elab.async false

namespace PhysicalWeightedCurrentCore

open ElectronicH1Space PhysicalPairRealization PhysicalSourceCoordinates
  PhysicalSourceMarginal PhysicalSourcePair PhysicalSourceH1

private theorem re_inner_self_complex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) : (inner ℂ v v).re = ‖v‖ ^ 2 :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

theorem tested_density_ofWaveFunction_weighted {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (a : PhysicalPairSpace.Position → ℝ)
    (hi : Integrable (fun z => a (particle z i) * ‖value u z‖ ^ 2)) :
    Integrable (fun x => a x * densityL1 (ofWaveFunction i u d) x) ∧
      (∫ x, a x * densityL1 (ofWaveFunction i u d) x) =
        (N : ℝ) * ∫ z, a (particle z i) * ‖value u z‖ ^ 2 := by
  have hi' : Integrable (fun z => a (particle z i) * (inner ℂ (value u z) (value u z)).re) := by
    simpa only [re_inner_self_complex] using hi
  have hp := particleMap_tested_re_inner i (value u) (value u) a hi'
  simp only [re_inner_self_complex] at hp
  have he : (fun x => a x * densityL1 (ofWaveFunction i u d) x) =ᵐ[volume]
      fun x => (N : ℝ) * (a x * ‖particleMap i (value u) x‖ ^ 2) := by
    filter_upwards [density_ofSource_ae N (particleMap i (value u))
      (fun c => particleMap i (d c)) (Lp.memLp _) (particleSource_memLp_six i u)
      (fun _ => Lp.memLp _)] with x hx
    have hscalar := congrArg (fun r : ℝ => a x * r) hx
    change a x * densityL1 (ofWaveFunction i u d) x =
      a x * ((N : ℝ) * ‖particleMap i (value u) x‖ ^ 2) at hscalar
    exact hscalar.trans (mul_left_comm _ _ _)
  exact ⟨(hp.1.const_mul (N : ℝ)).congr he.symm,
    (integral_congr_ae he).trans ((integral_const_mul _ _).trans
      (congrArg (fun r : ℝ => (N : ℝ) * r) hp.2))⟩

end PhysicalWeightedCurrentCore

namespace TransformationsGauge.WeakSpatialGauge

variable (G : WeakSpatialGauge) {N : ℕ}
  (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

theorem wavePhase_ae (w : WaveSpace (Fin N × Fin 3)) :
    G.wavePhase w =ᵐ[volume] fun x => factor (G.configurationAngle N) x • w x :=
  phase_ae (G.configurationAngle_measurable N) w

theorem gradient_density_configuration_integrable (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) V) :
    Integrable (fun z => G.gradient q.2 (particle z q.1) *
      ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) volume := by
  apply ((L2.integrable_inner (𝕜 := ℂ) (inclusion (Fin N × Fin 3) V u)
    (G.gradientSource V q u)).re).congr
  filter_upwards [G.gradientSource_ae V q u] with z hz
  change (inner ℂ (inclusion (Fin N × Fin 3) V u z) (G.gradientSource V q u z)).re = _
  exact (congrArg (fun w : PhotonFock =>
    (inner ℂ (inclusion (Fin N × Fin 3) V u z) w).re) hz).trans
      ((re_inner_real_smul _ _ _).trans
        (congrArg (fun r : ℝ => G.gradient q.2 (particle z q.1) * r)
          (norm_sq_eq_re_inner (𝕜 := ℂ) (inclusion (Fin N × Fin 3) V u z)).symm))

theorem pair_gauge (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (G.gaugeReference V u) =
      G.shiftPair (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  let T := G.gaugeReference V u
  have hincl : ⇑(inclusion (Fin N × Fin 3) V T) =ᵐ[volume]
      fun z => factor (G.configurationAngle N) z • inclusion (Fin N × Fin 3) V u z :=
    (Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w)
      (G.inclusion_gaugeReference V u))).trans
      (G.wavePhase_ae (inclusion (Fin N × Fin 3) V u))
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    refine Eq.trans ?_ (G.tested_density_shiftPair _ t.weight).symm
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans (Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [hincl] with z hz
    exact (congrArg (fun y : PhotonFock => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
      ‖y‖ ^ 2) hz).trans (congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        r ^ 2) (phase_norm _ (norm_factor _ z) _))
  · intro b t
    have hbt : ∀ x, ‖t.weight x‖ ≤ 1 := t.bounded
    have hcov := G.covariant_gaugeReference V C κP hκP M hbP e (i, b) u
    have hD : ⇑(covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T) =ᵐ[volume]
        fun z => factor (G.configurationAngle N) z •
          (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z +
            G.gradient b (particle z i) • inclusion (Fin N × Fin 3) V u z) := by
      filter_upwards [Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w)
          hcov),
        G.wavePhase_ae (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u +
          G.gradientSource V (i, b) u),
        Lp.coeFn_add (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)
          (G.gradientSource V (i, b) u), G.gradientSource_ae V (i, b) u]
        with z h₁ h₂ h₃ h₄
      exact h₁.trans (h₂.trans (congrArg (fun y => factor (G.configurationAngle N) z • y)
        (h₃.trans (congrArg (fun y => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z + y) h₄))))
    have hmeas : AEStronglyMeasurable
        (fun z => t.weight ((PhysicalSourceCoordinates.split i) z).1) volume :=
      t.measurable.comp_fst.comp_measurePreserving
        (PhysicalSourceCoordinates.split_measurePreserving i)
    have hi₁ : Integrable (fun z => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        (⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ).re) volume :=
      ((L2.integrable_inner (𝕜 := ℂ) _ _).re.congr (ae_of_all _ fun z =>
        RCLike.re_to_complex)).bdd_mul hmeas (c := 1) (ae_of_all _ fun z => hbt _)
    have hi₂ : Integrable (fun z => (t.weight ((PhysicalSourceCoordinates.split i) z).1 *
        G.gradient b ((PhysicalSourceCoordinates.split i) z).1) *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) volume := by
      have h := (G.gradient_density_configuration_integrable V (i, b) u).bdd_mul
        hmeas (c := 1) (ae_of_all _ fun z => hbt _)
      simpa only [PhysicalSourcePair.split_fst_eq_particle, mul_assoc] using h
    have hi₂' : Integrable (fun z => (t.weight (particle z i) * G.gradient b (particle z i)) *
        ‖ElectronicH1Space.value
          (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u)) z‖ ^ 2) := by
      apply hi₂.congr
      refine ae_of_all _ fun z => ?_
      have hposition := PhysicalSourcePair.split_fst_eq_particle i z
      have hvalue : inclusion (Fin N × Fin 3) V u z =
          ElectronicH1Space.value
            (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u)) z := rfl
      exact congrArg₂ (fun x (w : PhotonFock) =>
        (t.weight x * G.gradient b x) * ‖w‖ ^ 2) hposition hvalue
    have hweighted := (PhysicalWeightedCurrentCore.tested_density_ofWaveFunction_weighted i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u)
      (fun x => t.weight x * G.gradient b x) hi₂').2
    simp only [← PhysicalSourcePair.split_fst_eq_particle i] at hweighted
    refine Eq.trans ?_ (G.tested_current_shiftPair _ b t.weight t.measurable hbt).symm
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) b t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· + ·) (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm hweighted.symm)
    refine Eq.trans ?_ (mul_add _ _ _)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (Eq.trans ?_ (integral_add hi₁ hi₂))
    apply integral_congr_ae
    filter_upwards [hincl, hD] with z h₁ h₂
    change t.weight _ * (⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ).re = _
    refine (congrArg₂ (fun a c => t.weight ((PhysicalSourceCoordinates.split i) z).1 *
      (⟪a, c⟫_ℂ).re) h₁ h₂).trans ?_
    refine (congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r)
      (phase_current _ (norm_factor _ z) _ _ _)).trans ?_
    exact current_algebra t.weight (G.gradient b) (PhysicalSourcePair.split_fst_eq_particle i z) _ _

end TransformationsGauge.WeakSpatialGauge

end GptLean
