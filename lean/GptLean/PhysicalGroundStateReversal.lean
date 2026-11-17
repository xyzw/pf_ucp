import GptLean.PhysicalGroundState
import GptLean.TransformationsTimeReversalFrame

/-!
Time reversal of ground states (`prop-ground-state-fields` (iv)).

The mean vector potential of a reference vector `Ψ` at a point `y` is
`⟨Ψ, A^a(y) Ψ⟩ = ∫ Re ⟨Ψ(X), A^a(y) Ψ(X)⟩ dX`, with the actual Segal field of
the article kernel `G^a_y` acting in each configuration fibre. It is
invariant under unimodular phases and odd under the frame time reversal `Θ`.
For `A = 0` the reversed ground state is again a ground state, since `Θ` keeps
the energy and the density and reverses the combined current. If the ground
state is nondegenerate, `ΘΨ = cΨ` with `|c| = 1`, so the current and the mean
vector potential vanish. The mean magnetic field, the distributional curl of
the mean vector potential, then vanishes as well.
-/

noncomputable section

namespace GptLean.PhysicalGroundState

open MeasureTheory Filter PhysicalPairSpace PhysicalPairDuality PhysicalFock PhysicalPFReference
  TransformationsTimeReversal TransformationsPotentials
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

local instance referenceModule {I : Type} [Fintype I] [DecidableEq I] (V : Position I → ℝ) :
    Module ℂ (Reference I V) :=
  (referenceNormedSpace I V).toModule

section InnerAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_unit_smul (c : ℂ) (hc : ‖c‖ = 1) (x y : E) :
    (⟪c • x, c • y⟫_ℂ).re = (⟪x, y⟫_ℂ).re := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

theorem norm_unit_smul (c : ℂ) (hc : ‖c‖ = 1) (x : E) : ‖c • x‖ = ‖x‖ := by
  rw [norm_smul, hc, one_mul]

theorem re_inner_anti_neg (W : E ≃ₗᵢ⋆[ℂ] E) (x y : E) :
    (⟪W x, -W y⟫_ℂ).re = -(⟪x, y⟫_ℂ).re := by
  rw [inner_neg_right, TransformationsFock.inner_antiunitary, Complex.neg_re, Complex.conj_re]

end InnerAlgebra

section Generic

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- The mean vector potential `⟨Ψ, A^a(y) Ψ⟩` of a reference vector. -/
def meanVectorPotential (u : Reference (Fin N × Fin 3) V) (a : Fin 3)
    (y : PhysicalPairSpace.Position) : ℝ :=
  ∫ z, (⟪inclusion (Fin N × Fin 3) V u z,
    kernelField C (K (a, y)) (radiationSource (Fin N × Fin 3) V u z)⟫_ℂ).re

theorem inclusion_smul_ae (c : ℂ) (u : Reference (Fin N × Fin 3) V) :
    ∀ᵐ z ∂volume, inclusion (Fin N × Fin 3) V (c • u) z = c • inclusion (Fin N × Fin 3) V u z := by
  filter_upwards [Lp.coeFn_smul c (inclusion (Fin N × Fin 3) V u)] with z hz
  exact (congrFun (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
    (w : PhysicalPFReference.Position (Fin N × Fin 3) → PhotonFock))
      (map_smul (inclusion (Fin N × Fin 3) V) c u)) z).trans hz

theorem radiationSource_smul_ae (c : ℂ) (u : Reference (Fin N × Fin 3) V) :
    ∀ᵐ z ∂volume, radiationSource (Fin N × Fin 3) V (c • u) z =
      c • radiationSource (Fin N × Fin 3) V u z := by
  filter_upwards [Lp.coeFn_smul c (radiationSource (Fin N × Fin 3) V u)] with z hz
  exact (congrFun (congrArg (fun w : RadiationGraph (Fin N × Fin 3) =>
    (w : PhysicalPFReference.Position (Fin N × Fin 3) → RadiationGraphSpace))
      (map_smul (radiationSource (Fin N × Fin 3) V) c u)) z).trans hz

/-- The mean vector potential is invariant under unimodular phases. -/
theorem meanVectorPotential_smul (c : ℂ) (hc : ‖c‖ = 1) (u : Reference (Fin N × Fin 3) V)
    (a : Fin 3) (y : PhysicalPairSpace.Position) :
    meanVectorPotential V C K (c • u) a y = meanVectorPotential V C K u a y := by
  unfold meanVectorPotential
  apply integral_congr_ae
  filter_upwards [inclusion_smul_ae V c u, radiationSource_smul_ae V c u] with z h₁ h₂
  exact (congrArg₂ (fun (x : PhotonFock) (r : RadiationGraphSpace) =>
      (⟪x, kernelField C (K (a, y)) r⟫_ℂ).re) h₁ h₂).trans
    ((congrArg (fun w : PhotonFock => (⟪c • inclusion (Fin N × Fin 3) V u z, w⟫_ℂ).re)
      (map_smul (kernelField C (K (a, y))) c _)).trans (re_inner_unit_smul c hc _ _))

/-- The constructed pair is invariant under unimodular phases. -/
theorem pair_unit_smul (c : ℂ) (hc : ‖c‖ = 1) (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (c • u) =
      PhysicalPFParticle.pair C K hK M hM V i e u := by
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (c • u)))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) (c • u)) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans (Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [inclusion_smul_ae V c u] with z hz
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r ^ 2)
      ((congrArg norm hz).trans (norm_unit_smul c hc _))
  · intro b t
    have hcov : ∀ᵐ z ∂volume,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) (c • u) z =
          c • covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z := by
      filter_upwards [Lp.coeFn_smul c (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)]
        with z hz
      exact (congrFun (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
        (w : PhysicalPFReference.Position (Fin N × Fin 3) → PhotonFock))
          (map_smul (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b)) c u)) z).trans hz
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V (c • u)))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) (c • u)) b t.weight
      t.measurable (ae_of_all _ t.bounded)).trans (Eq.trans ?_
      (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [inclusion_smul_ae V c u, hcov] with z h₁ h₂
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r)
      ((congrArg₂ (fun x y : PhotonFock => (⟪x, y⟫_ℂ).re) h₁ h₂).trans
        (re_inner_unit_smul c hc _ _))

variable (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)
  (Wr : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace)
  (hincl : ∀ q, radiationGraphInclusion (Wr q) = W (radiationGraphInclusion q))
  (hodd : ∀ z r, kernelField C (K z) (Wr r) = -W (kernelField C (K z) r))

include hodd in
/-- The mean vector potential is odd under an antiunitary with odd field kernels. -/
theorem meanVectorPotential_reverse (u : Reference (Fin N × Fin 3) V) (a : Fin 3)
    (y : PhysicalPairSpace.Position) :
    meanVectorPotential V C K (reverse W Wr hincl V u) a y = -meanVectorPotential V C K u a y := by
  unfold meanVectorPotential
  refine Eq.trans ?_ (integral_neg _)
  apply integral_congr_ae
  have hr : ∀ᵐ z ∂volume, radiationSource (Fin N × Fin 3) V (reverse W Wr hincl V u) z =
      Wr (radiationSource (Fin N × Fin 3) V u z) :=
    (realCLM Wr).coeFn_compLpL (radiationSource (Fin N × Fin 3) V u)
  filter_upwards [antiWave_ae W (inclusion (Fin N × Fin 3) V u), hr] with z h₁ h₂
  exact (congrArg₂ (fun (x : PhotonFock) (r : RadiationGraphSpace) =>
      (⟪x, kernelField C (K (a, y)) r⟫_ℂ).re) h₁ h₂).trans
    ((congrArg (fun w : PhotonFock => (⟪W (inclusion (Fin N × Fin 3) V u z), w⟫_ℂ).re)
      (hodd (a, y) _)).trans (re_inner_anti_neg W _ _))

end Generic

section Article

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)

set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (PhysicalPolarization.formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous
  (PhysicalPolarization.formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalProfiles.kernelBound (PhysicalPolarization.formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound
  (PhysicalPolarization.formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential N 1

/-- The reference vector of a pure state. -/
def stateVector (p : State F χ C B S e (N := N)) : Reference (Fin N × Fin 3) Vp :=
  Classical.choose (TransformationsPureStates.pure_reference Vp C Kf hKf MK hMK B S e p)

theorem stateVector_spec (p : State F χ C B S e (N := N)) :
    inclusion (Fin N × Fin 3) Vp (stateVector F χ C B S e p) = p.val :=
  Classical.choose_spec (TransformationsPureStates.pure_reference Vp C Kf hKf MK hMK B S e p)

/-- The mean vector potential `⟨Ψ, A^a(y) Ψ⟩` of a pure state of the article model. -/
def stateMeanField (p : State F χ C B S e (N := N)) (a : Fin 3)
    (y : PhysicalPairSpace.Position) : ℝ :=
  meanVectorPotential Vp C Kf (stateVector F χ C B S e p) a y

theorem pairPotential_currentFlip {a : Potential} (hA : a.2 = 0) (d : Pair) :
    pairPotential a (currentFlip d) = pairPotential a d := by
  change pairing a.1 d.1 + pairing a.2 (-d.2) = pairing a.1 d.1 + pairing a.2 d.2
  rw [hA, map_neg]
  have h0 (f : Current) : pairing (p := 3 / 2) (0 : VectorPotential) f = 0 := by
    rw [pairing_eq_integral]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    have hz : ((0 : VectorPotential).val : PhysicalPairSpace.Position → Vector) =ᵐ[volume] 0 :=
      AEEqFun.coeFn_zero
    filter_upwards [hz] with x hx
    rw [hx, Pi.zero_apply, inner_zero_left]
  simp only [h0, neg_zero]

private theorem eq_zero_of_eq_neg {E : Type*} [AddCommGroup E] [Module ℝ E] {v : E}
    (h : v = -v) : v = 0 := by
  have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel v
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

private theorem eq_zero_of_eq_neg_real {v : ℝ} (h : v = -v) : v = 0 := by linarith

/-- **`prop-ground-state-fields` (iv).** Let `A = 0` and let the ground state be
nondegenerate, so every ground state is a phase multiple of it. Then the
current density and the mean vector potential vanish. -/
theorem ground_reversal {a : Potential} (hA : a.2 = 0) {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p)
    (hnd : ∀ q, IsGroundState i F χ C B S e a q → ∃ c : ℂ, q.val = c • p.val) :
    currentL1 ((model i F χ C B S e).density p) = 0 ∧
      ∀ b y, stateMeanField F χ C B S e p b y = 0 := by
  let u := stateVector F χ C B S e p
  have hu : inclusion (Fin N × Fin 3) Vp u = p.val := stateVector_spec F χ C B S e p
  let W := TransformationsTimeReversal.frameReversal F
  let Wr := TransformationsTimeReversal.frameRadiationReversal F
  have hincl := TransformationsTimeReversal.frameReversal_inclusion F
  have hodd := TransformationsTimeReversal.kernelField_frameReversal F χ
    (LinearIsometryEquiv.refl ℝ _) C
  let u' := reverse W Wr hincl Vp u
  have hnorm : ‖p.val‖ = 1 := p.property.1
  have hferm := TransformationsPureStates.pure_fermionic Vp C Kf hKf MK hMK B S e p
  have hu'n : ‖inclusion (Fin N × Fin 3) Vp u'‖ = 1 :=
    (norm_antiWave W _).trans ((congrArg norm hu).trans hnorm)
  have hu'f : inclusion (Fin N × Fin 3) Vp u' ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    antiWave_mem_fermionic W ((congrArg (fun v => v ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) hu).mpr hferm)
  let q : State F χ C B S e (N := N) :=
    TransformationsPureStates.ofVector Vp C Kf hKf MK hMK B S e
      (inclusion (Fin N × Fin 3) Vp u') hu'n hu'f ⟨u', rfl⟩
  have hEq : (model i F χ C B S e).energy q = (model i F χ C B S e).energy p :=
    (TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S e i q u' rfl).trans
      ((energy_reverse W Wr hincl (TransformationsTimeReversal.frameReversal_derivative F) Vp C
        (PhysicalPFParticle.particleKernel Kf) (PhysicalPFParticle.particleKernel_measurable Kf hKf)
        MK (PhysicalPFParticle.particleKernel_bound Kf MK hMK)
        (field_odd_particle W Wr C Kf hodd) e u).trans
      (TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S e i p u hu).symm)
  have hpair_u' : PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e u' =
      currentFlip (PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e u) :=
    pair_antiReverse W Wr hincl Vp C Kf hKf MK hMK e i hodd u
  have hdp : (model i F χ C B S e).density p = PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e u :=
    TransformationsPureStates.pure_density Vp C Kf hKf MK hMK B S e i p u hu
  have hdq : (model i F χ C B S e).density q =
      currentFlip ((model i F χ C B S e).density p) :=
    (TransformationsPureStates.pure_density Vp C Kf hKf MK hMK B S e i q u' rfl).trans
      (hpair_u'.trans (congrArg currentFlip hdp.symm))
  have hshift : shiftedEnergy i F χ C B S e a q = shiftedEnergy i F χ C B S e a p :=
    congrArg₂ (· + ·) hEq ((congrArg (pairPotential a) hdq).trans
      (pairPotential_currentFlip hA _))
  have hq : IsGroundState i F χ C B S e a q := fun r => hshift.trans_le (h r)
  obtain ⟨c, hc⟩ := hnd q hq
  have hcn : ‖c‖ = 1 :=
    (mul_one ‖c‖).symm.trans ((congrArg (‖c‖ * ·) hnorm.symm).trans
      ((norm_smul c p.val).symm.trans ((congrArg norm hc).symm.trans hu'n)))
  have hu'c : u' = c • u := by
    apply inclusion_injective (Fin N × Fin 3) Vp
    exact hc.trans ((congrArg (c • ·) hu.symm).trans (map_smul _ c u).symm)
  have hpair_eq : PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e u =
      currentFlip (PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e u) :=
    (pair_unit_smul Vp C Kf hKf MK hMK e i c hcn u).symm.trans
      ((congrArg (PhysicalPFParticle.pair C Kf hKf MK hMK Vp i e) hu'c.symm).trans hpair_u')
  refine ⟨?_, fun b y => ?_⟩
  · exact (congrArg currentL1 hdp).trans (eq_zero_of_eq_neg
      ((congrArg currentL1 hpair_eq).trans (currentL1_currentFlip _)))
  · have hm := (meanVectorPotential_smul Vp C Kf c hcn u b y).symm.trans
      ((congrArg (fun w => meanVectorPotential Vp C Kf w b y) hu'c.symm).trans
        (meanVectorPotential_reverse Vp C Kf W Wr hincl hodd u b y))
    exact eq_zero_of_eq_neg_real hm

end Article

end GptLean.PhysicalGroundState
