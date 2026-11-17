import GptLean.TransformationsGaugeWeakReference
import GptLean.TransformationsGaugeWeakPairCovariance
import GptLean.TransformationsGaugeStates
import GptLean.PhysicalWeightedCurrent

/-! Weighted physical pair identities for weak spatial gauges. -/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory Filter PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  TransformationsPhase PhysicalSourceMarginal PhysicalPairRealization
  PhysicalNormalTrace PhysicalClosedForms
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace WeakSpatialGauge

private theorem sum_fin_constant {N : ℕ} (f : Fin N → ℝ) (i : Fin N)
    (h : ∀ j, f j = f i) : ∑ j, f j = (N : ℝ) * f i := by
  calc
    ∑ j, f j = ∑ _j : Fin N, f i := Finset.sum_congr rfl fun j _ => h j
    _ = _ := by simp

variable (G : WeakSpatialGauge) {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)

theorem re_inner_gradientSource (q : Fin N × Fin 3)
    (d : WaveSpace (Fin N × Fin 3)) (u : Reference (Fin N × Fin 3) V) :
    (⟪d, G.gradientSource V q u⟫_ℂ).re =
      ∫ z, G.gradient q.2 (particle z q.1) *
        PhysicalPairIntegrability.currentComponent (inclusion (Fin N × Fin 3) V u z) (d z) := by
  have h₁ : ⟪d, G.gradientSource V q u⟫_ℂ = ∫ z, ⟪d z, G.gradientSource V q u z⟫_ℂ :=
    L2.inner_def d (G.gradientSource V q u)
  have h₂ := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) d (G.gradientSource V q u))
  simp only [RCLike.re_to_complex] at h₂
  refine (congrArg Complex.re h₁).trans (h₂.symm.trans ?_)
  apply integral_congr_ae
  filter_upwards [G.gradientSource_ae V q u] with z hz
  exact (congrArg (fun y => (⟪d z, y⟫_ℂ).re) hz).trans (re_inner_real_smul _ _ _)

theorem currentComponent_integrable (q : Fin N × Fin 3)
    (d : WaveSpace (Fin N × Fin 3)) (u : Reference (Fin N × Fin 3) V) :
    Integrable (fun z => G.gradient q.2 (particle z q.1) *
      PhysicalPairIntegrability.currentComponent (inclusion (Fin N × Fin 3) V u z) (d z)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) d (G.gradientSource V q u)).re.congr ?_
  filter_upwards [G.gradientSource_ae V q u] with z hz
  change (⟪d z, G.gradientSource V q u z⟫_ℂ).re =
    G.gradient q.2 (particle z q.1) * (⟪inclusion (Fin N × Fin 3) V u z, d z⟫_ℂ).re
  exact (congrArg (fun y : PhotonFock => (⟪d z, y⟫_ℂ).re) hz).trans
    (re_inner_real_smul _ _ _)

theorem norm_sq_gradientSource (q : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) V) :
    ‖G.gradientSource V q u‖ ^ 2 =
      ∫ z, G.gradient q.2 (particle z q.1) ^ 2 * ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2 := by
  refine (l2_norm_sq_complex _).trans ?_
  apply integral_congr_ae
  filter_upwards [G.gradientSource_ae V q u] with z hz
  exact (congrArg (fun y => ‖y‖ ^ 2) hz).trans (norm_real_smul_sq _ _)

theorem density_gradient_square_integrable (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) V) :
    Integrable (fun z => G.gradient q.2 (particle z q.1) ^ 2 *
      ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) := by
  have hn : Integrable (fun z => ‖G.gradientSource V q u z‖ ^ 2) volume :=
    (Lp.memLp (G.gradientSource V q u)).integrable_norm_pow (p := 2) (by decide)
  refine hn.congr ?_
  filter_upwards [G.gradientSource_ae V q u] with z hz
  exact (congrArg (fun y : PhotonFock => ‖y‖ ^ 2) hz).trans (norm_real_smul_sq _ _)

variable (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

theorem energy_gauge (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    energy (Fin N × Fin 3) V C κP hκP M hbP e (G.gaugeReference V u) =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u +
        G.energyShift (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  have hvalue (z : Configuration N) : inclusion (Fin N × Fin 3) V u z =
      ElectronicH1Space.value
        (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u)) z := rfl
  have hpair : PhysicalPFParticle.pair C K hK M hM V i e u =
      PhysicalSourcePair.ofWaveFunction i
        (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
        (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) := rfl
  refine (G.energy_gaugeReference V C κP hκP M hbP e u).trans ?_
  rw [add_assoc]
  refine congrArg (fun r : ℝ => energy (Fin N × Fin 3) V C κP hκP M hbP e u + r) ?_
  unfold energyShift
  apply congrArg₂ (· + ·)
  · simp_rw [G.re_inner_gradientSource]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    have hs (j : Fin N) := PhysicalElectronicFermions.current_particle_integral_eq N PhotonFock
      ⟨inclusion (Fin N × Fin 3) V u, hu⟩
      (fun q => covariant (Fin N × Fin 3) V C κP hκP M hbP e q u)
      (PhysicalPFParticle.covariant_covariance C K hK M hM V e u hu) j i b (G.gradient b)
    refine (sum_fin_constant (fun j => ∫ z, G.gradient b (particle z j) *
      PhysicalPairIntegrability.currentComponent (inclusion (Fin N × Fin 3) V u z)
        (covariant (Fin N × Fin 3) V C κP hκP M hbP e (j, b) u z)) i hs).trans ?_
    have hc (z : Configuration N) :
        G.gradient b (particle z i) *
          PhysicalPairIntegrability.currentComponent (inclusion (Fin N × Fin 3) V u z)
            (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z) =
        G.gradient b (particle z i) *
          (⟪ElectronicH1Space.value
            (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u)) z,
            covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ).re :=
      congrArg (fun w : PhotonFock => G.gradient b (particle z i) *
        (⟪w, covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ).re) (hvalue z)
    have ht := PhysicalWeightedCurrentCore.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) b (G.gradient b)
      ((G.currentComponent_integrable V (i, b)
        (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u) u).congr (ae_of_all _ hc))
    exact (congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae (ae_of_all _ hc))).trans
      (ht.2.symm.trans (congrArg (fun p : Pair =>
        ∫ y, G.gradient b y * currentL1 p y b) hpair.symm))
  · apply congrArg ((1 / 2 : ℝ) * ·)
    simp_rw [G.norm_sq_gradientSource]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hn (b : Fin 3) (z : Configuration N) :
        G.gradient b (particle z i) ^ 2 * ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2 =
          G.gradient b (particle z i) ^ 2 * ‖ElectronicH1Space.value
            (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u)) z‖ ^ 2 :=
      congrArg (fun w : PhotonFock => G.gradient b (particle z i) ^ 2 * ‖w‖ ^ 2) (hvalue z)
    have hid (b : Fin 3) := PhysicalWeightedCurrentCore.tested_density_ofWaveFunction_weighted i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u)
      (fun y => G.gradient b y ^ 2)
      ((G.density_gradient_square_integrable V (i, b) u).congr (ae_of_all _ (hn b)))
    have hi (b : Fin 3) : Integrable (fun y => G.gradient b y ^ 2 *
        densityL1 (PhysicalPFParticle.pair C K hK M hM V i e u) y) :=
      (hid b).1.congr (ae_of_all _ fun y => congrArg
        (fun p : Pair => G.gradient b y ^ 2 * densityL1 p y) hpair.symm)
    have hsum (b : Fin 3) :
        (∑ j, ∫ z, G.gradient b (particle z j) ^ 2 * ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) =
          ∫ y, G.gradient b y ^ 2 * densityL1 (PhysicalPFParticle.pair C K hK M hM V i e u) y := by
      have hs (j : Fin N) := PhysicalElectronicFermions.density_particle_integral_eq N PhotonFock
        ⟨inclusion (Fin N × Fin 3) V u, hu⟩ j i (fun y => G.gradient b y ^ 2)
      refine (sum_fin_constant (fun j => ∫ z, G.gradient b (particle z j) ^ 2 *
        ‖inclusion (Fin N × Fin 3) V u z‖ ^ 2) i hs).trans ?_
      exact (congrArg (fun r : ℝ => (N : ℝ) * r)
        (integral_congr_ae (ae_of_all _ (hn b)))).trans
        ((hid b).2.symm.trans (congrArg (fun p : Pair =>
          ∫ y, G.gradient b y ^ 2 * densityL1 p y) hpair.symm))
    exact (Finset.sum_congr rfl (fun b _ => hsum b)).trans
      ((integral_finsetSum _ (fun b _ => hi b)).symm.trans
        (integral_congr_ae (ae_of_all _ fun y => (Finset.sum_mul ..).symm)))


theorem configuration_permute (π : Equiv.Perm (Fin N)) (z : Configuration N) :
    G.configurationAngle N (permuteConfiguration π z) = G.configurationAngle N z := by
  change ∑ j, G.fn (particle (permuteConfiguration π z) j) = ∑ j, G.fn (particle z j)
  simp_rw [particle_permute]
  exact Equiv.sum_comp π.symm (fun j => G.fn (particle z j))

theorem permutation_wavePhase (π : Equiv.Perm (Fin N)) (v : WaveSpace (Fin N × Fin 3)) :
    PhysicalElectronicFermions.permutation N PhotonFock π (G.wavePhase v) =
      G.wavePhase (PhysicalElectronicFermions.permutation N PhotonFock π v) := by
  apply Lp.ext
  have hcomp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (phase_ae (G.configurationAngle_measurable N) v)
  filter_upwards [PhysicalElectronicFermions.permutation_ae N PhotonFock π (G.wavePhase v),
    hcomp, phase_ae (G.configurationAngle_measurable N)
      (PhysicalElectronicFermions.permutation N PhotonFock π v),
    PhysicalElectronicFermions.permutation_ae N PhotonFock π v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₄]
  simp only [Function.comp_apply] at h₂
  rw [h₂]
  unfold factor
  rw [G.configuration_permute π x]

theorem wavePhase_mem_fermionic {v : WaveSpace (Fin N × Fin 3)}
    (hv : v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    G.wavePhase v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock := by
  intro π
  exact (G.permutation_wavePhase π v).trans
    ((congrArg G.wavePhase (hv π)).trans (map_smul G.wavePhase _ v))

theorem wavePhase_neg (v : WaveSpace (Fin N × Fin 3)) : G.neg.wavePhase (G.wavePhase v) = v := by
  apply Lp.ext
  filter_upwards [phase_ae (G.neg.configurationAngle_measurable N) (G.wavePhase v),
    phase_ae (G.configurationAngle_measurable N) v] with x h₁ h₂
  rw [h₁, h₂, smul_smul, G.configurationAngle_neg, factor_neg_mul, one_smul]

theorem wavePhase_neg_left (v : WaveSpace (Fin N × Fin 3)) :
    G.wavePhase (G.neg.wavePhase v) = v := by
  apply Lp.ext
  filter_upwards [phase_ae (G.configurationAngle_measurable N) (G.neg.wavePhase v),
    phase_ae (G.neg.configurationAngle_measurable N) v] with x h₁ h₂
  rw [h₁, h₂, smul_smul, G.configurationAngle_neg, mul_comm, factor_neg_mul, one_smul]

/-- Gauge covariance on the article's full weak gauge class. -/
theorem search_gauge (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
    (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (G.shiftPair d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d +
        ((G.energyShift d : ℝ) : EReal) :=
  TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    G.wavePhase G.neg.wavePhase G.shiftEquiv G.energyShift
    (fun v => G.wavePhase.norm_map v) (fun v => G.neg.wavePhase.norm_map v)
    (fun v hv => G.wavePhase_mem_fermionic hv) (fun v hv => G.neg.wavePhase_mem_fermionic hv)
    G.wavePhase_neg G.wavePhase_neg_left
    (fun u => ⟨G.neg.gaugeReference V u, G.neg.inclusion_gaugeReference V u⟩)
    (fun u hu => ⟨G.gaugeReference V u, G.inclusion_gaugeReference V u,
      G.energy_gauge V C K hK M hM e i u hu, G.pair_gauge V C K hK M hM e i u⟩) d

end WeakSpatialGauge

end GptLean.TransformationsGauge
