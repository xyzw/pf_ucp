import GptLean.TransformationsRotationPhysical
import GptLean.TransformationsTimeReversalForm

/-!
Time reversal for the article's polarization frame, `prop-time-reversal`.

In the solenoidal representation the time reversal uses `(J f)(k) = conj f(-k)`.
In the polarization-label representation with a measurable frame `ε_a(k)`,
both pairs `ε_b(k)` and `ε_b(-k)` span `k^⊥`, so `J` becomes
`(J f)(k, a) = ∑_b ⟪ε_a(k), ε_b(-k)⟫ conj f(-k, b)`. Let `Υ` be the photon map
of the spatial inversion `R = -1`. Its one-photon action is
`(Υ g)(k, a) = ∑_b O_ab(k) g(-k, b)` with `O_ab(k) = ⟪ε_a(k), -ε_b(-k)⟫`. With `𝒞`
the complex conjugation in the label representation, the photon antiunitary
`W = Γ(Υ) 𝒞` has one-photon part `-J`.

The cutoff reality condition `χ(k) = conj χ(-k)` and `∑_b O_ab(k) ε_b(-k) = -ε_a(k)`
give `W K = -K` for the article's kernels, so the field is odd under `W`. No
parity property of the frame is used. The time reversal `Θ` applies `W`
pointwise in the electron configuration and conjugates the electronic wave
function. It preserves the energy, fixes the density and reverses the combined
current. Hence `F(ρ, -j) = F(ρ, j)` for `F_LL` and `F_L` on the actual model with
the article's arbitrary frame and cutoff.

The general part of this file proves the last statement for every pointwise
photon antiunitary with odd field kernels.
-/

noncomputable section

namespace GptLean.TransformationsTimeReversal

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization PhysicalPFReference
  TransformationsFock TransformationsKernelCovariance TransformationsRotation
  TransformationsPotentials PhotonLocalizationPhysicalKernels PhysicalPairSpace SymmetricLift
  PhysicalNormalTrace PhysicalClosedForms
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance frameRadiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

section Antiunitary

variable {N : ℕ} (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)
  (Wr : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace)
  (hincl : ∀ q, radiationGraphInclusion (Wr q) = W (radiationGraphInclusion q))
  (hderiv : ∀ q, radiationGraphDerivative (Wr q) = W (radiationGraphDerivative q))
  (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)
  (hodd : ∀ z r, kernelField C (K z) (Wr r) = -W (kernelField C (K z) r))

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

include hodd in
theorem field_odd_particle (q : Fin N × Fin 3) (x : Configuration N) (r : RadiationGraphSpace) :
    kernelField C (κP q x) (Wr r) = -W (kernelField C (κP q x) r) :=
  hodd _ r

include hodd in
/-- The time reversal fixes the density and reverses the current. -/
theorem pair_antiReverse (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (reverse W Wr hincl V u) =
      currentFlip (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  let T := reverse W Wr hincl V u
  apply pair_eq_of_bounded_spatial_tests
  · intro t
    refine (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) t.weight t.measurable
      (ae_of_all _ t.bounded)).trans (Eq.trans ?_ (PhysicalSourcePair.tested_density_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (integral_congr_ae ?_)
    filter_upwards [antiWave_ae W (inclusion (Fin N × Fin 3) V u)] with z hz
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r ^ 2)
      ((congrArg norm hz).trans (W.norm_map _))
  · intro b t
    have hcov := covariant_reverse W Wr hincl V C κP hκP M hbP
      (field_odd_particle W Wr C K hodd) e (i, b) u
    have hR : (∫ x, t.weight x *
        currentL1 (currentFlip (PhysicalPFParticle.pair C K hK M hM V i e u)) x b) =
        -∫ x, t.weight x * currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u) x b := by
      refine Eq.trans ?_ (integral_neg _)
      apply integral_congr_ae
      filter_upwards [Filter.EventuallyEq.of_eq (congrArg (fun f : Lp PhysicalPairSpace.Vector 1
          (volume : Measure PhysicalPairSpace.Position) => ⇑f)
          (currentL1_currentFlip (PhysicalPFParticle.pair C K hK M hM V i e u))),
        Lp.coeFn_neg (currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u))] with x h₁ h₂
      refine (congrArg (fun y : PhysicalPairSpace.Vector => t.weight x * y b) (h₁.trans h₂)).trans ?_
      change t.weight x * (-(currentL1 (PhysicalPFParticle.pair C K hK M hM V i e u) x b)) = _
      ring
    refine Eq.trans ?_ hR.symm
    refine (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V T))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) T) b t.weight t.measurable
      (ae_of_all _ t.bounded)).trans ?_
    refine Eq.trans ?_ (congrArg Neg.neg (PhysicalSourcePair.tested_current_ofWaveFunction i
      (ElectronicH1Complex.realEquiv (electronic (Fin N × Fin 3) V u))
      (fun a => covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, a) u) b t.weight t.measurable
      (ae_of_all _ t.bounded)).symm)
    refine Eq.trans ?_ (neg_mul_eq_mul_neg _ _).symm
    refine congrArg (fun r : ℝ => (N : ℝ) * r) (Eq.trans ?_ (integral_neg _))
    apply integral_congr_ae
    filter_upwards [antiWave_ae W (inclusion (Fin N × Fin 3) V u),
      Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w) hcov),
      Lp.coeFn_neg (antiWave W (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)),
      antiWave_ae W (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)]
      with z h₁ h₂ h₃ h₄
    change t.weight _ * (⟪inclusion (Fin N × Fin 3) V T z,
      covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ).re = _
    have hinner : ⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ =
        -(starRingEnd ℂ) ⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ := by
      exact (congrArg₂ (fun p q => ⟪p, q⟫_ℂ) h₁ (h₂.trans (h₃.trans
        (congrArg Neg.neg h₄)))).trans ((inner_neg_right _ _).trans
          (congrArg Neg.neg (inner_antiunitary W _ _)))
    exact (congrArg (fun c : ℂ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * c.re)
      hinner).trans (neg_conj_re_mul _ _)

include hincl in
theorem antiReverse_reference (u : Reference (Fin N × Fin 3) V) :
    ∃ u' : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u' = antiWave W.symm (inclusion (Fin N × Fin 3) V u) :=
  ⟨reverse W.symm Wr.symm (inclusion_symm W Wr hincl) V u, rfl⟩

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

include hincl hderiv hodd in
/-- **Time-reversal invariance of `F_LL`** for every pointwise photon
antiunitary with odd field kernels. -/
theorem search_antiReverse (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (currentFlip d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d := by
  have h := TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    (antiWave W) (antiWave W.symm) currentFlip (fun _ => 0)
    (fun v => norm_antiWave _ v) (fun v => norm_antiWave _ v)
    (fun v hv => antiWave_mem_fermionic _ hv) (fun v hv => antiWave_mem_fermionic _ hv)
    (fun v => antiWave_symm _ v) (fun v => antiWave_symm_left _ v)
    (antiReverse_reference W Wr hincl V)
    (fun u _ => ⟨reverse W Wr hincl V u, rfl,
      (energy_reverse W Wr hincl hderiv V C κP hκP M hbP (field_odd_particle W Wr C K hodd) e
        u).trans (add_zero _).symm,
      pair_antiReverse W Wr hincl V C K hK M hM e i hodd u⟩) d
  rw [h, EReal.coe_zero, add_zero]

include hincl hderiv hodd in
/-- **Time-reversal invariance of the Lieb functional** for every pointwise
photon antiunitary with odd field kernels. -/
theorem lieb_antiReverse (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (currentFlip d) =
      DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_flip _ (search_antiReverse W Wr hincl hderiv V C K hK M hM e i hodd B S) d

end Antiunitary

section Frame

/-- The spatial inversion `k ↦ -k`. -/
abbrev inversion : FieldSpace ≃ₗᵢ[ℝ] FieldSpace := LinearIsometryEquiv.neg ℝ

theorem inversion_apply (k : FieldSpace) : inversion k = -k := rfl

theorem inversion_symm_apply (k : FieldSpace) : inversion.symm k = -k := rfl

variable (F : Frame)

/-- `∑_b O_ab(k) ε_b(-k) = -ε_a(k)` for the overlap of the inversion. -/
theorem epsilon_inversion (k : FieldSpace) (hk : k ≠ 0) (a : Fin 2) (μ : Fin 3) :
    ∑ b, overlap inversion F k a b * F.epsilon (-k) b μ = -F.epsilon k a μ := by
  have h := congrArg (fun v : FieldSpace => v μ) (overlap_reconstruction inversion F k hk a)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, rotatedEpsilon,
    inversion_apply, inversion_symm_apply, PiLp.neg_apply] at h
  rw [← h, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- A profile `c(k) ε_a(k)_μ` with `conj c(-k) = c(k)` is odd under `-J`. -/
theorem profile_inversion (c : FieldSpace → ℂ) (k : FieldSpace) (hk : k ≠ 0)
    (hc : starRingEnd ℂ (c (-k)) = c k) (a : Fin 2) (μ : Fin 3) :
    ∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ ((F.epsilon (-k) b μ : ℂ) * c (-k)) =
      -((F.epsilon k a μ : ℂ) * c k) := by
  simp only [map_mul, Complex.conj_ofReal, hc]
  have h := congrArg (fun t : ℝ => (t : ℂ) * c k) (epsilon_inversion F k hk a μ)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg, Finset.sum_mul] at h
  rw [← neg_mul, ← h]
  exact Finset.sum_congr rfl fun b _ => by ring

variable (χ : ArticleCutoff)

/-- The article's form factors are odd under `-J`, by the cutoff reality condition. -/
theorem base_inversion (k : FieldSpace) (hk : k ≠ 0)
    (hχ : χ.value k = starRingEnd ℂ (χ.value (-k))) (a : Fin 2) (μ : Fin 3) :
    ∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ (base F χ μ (-k, b)) =
      -base F χ μ (k, a) := by
  have hc : starRingEnd ℂ (χ.value (-(-k)) / (Real.sqrt 2 : ℂ)) =
      χ.value (-k) / (Real.sqrt 2 : ℂ) := by
    rw [neg_neg, map_div₀, Complex.conj_ofReal, hχ, Complex.conj_conj]
  have h := profile_inversion F (fun q => χ.value (-q) / (Real.sqrt 2 : ℂ)) k hk hc a μ
  refine Eq.trans ?_ (h.trans ?_)
  · refine Finset.sum_congr rfl fun b _ =>
      congrArg (fun z => (overlap inversion F k a b : ℂ) * starRingEnd ℂ z) ?_
    simp only [base]
    ring
  · simp only [base]
    ring

/-- The inverse-frequency profiles are odd under `-J` as well. -/
theorem infraredBase_inversion (k : FieldSpace) (hk : k ≠ 0)
    (hχ : χ.value k = starRingEnd ℂ (χ.value (-k))) (a : Fin 2) (μ : Fin 3) :
    ∑ b, (overlap inversion F k a b : ℂ) *
        starRingEnd ℂ (infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ μ) (-k, b)) =
      -infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ μ) (k, a) := by
  have hc : starRingEnd ℂ ((((Real.sqrt ‖-k‖)⁻¹ : ℝ) : ℂ) *
      (χ.value (-(-k)) / (Real.sqrt 2 : ℂ))) =
      (((Real.sqrt ‖k‖)⁻¹ : ℝ) : ℂ) * (χ.value (-k) / (Real.sqrt 2 : ℂ)) := by
    rw [neg_neg, norm_neg, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal, hχ,
      Complex.conj_conj]
  have h := profile_inversion F
    (fun q => (((Real.sqrt ‖q‖)⁻¹ : ℝ) : ℂ) * (χ.value (-q) / (Real.sqrt 2 : ℂ))) k hk hc a μ
  refine Eq.trans ?_ (h.trans ?_)
  · refine Finset.sum_congr rfl fun b _ =>
      congrArg (fun z => (overlap inversion F k a b : ℂ) * starRingEnd ℂ z) ?_
    simp only [infraredBase, base, Complex.real_smul]
    ring
  · simp only [infraredBase, base, Complex.real_smul]
    ring

private theorem phase_sum (o : Fin 2 → ℂ) (c : ℂ) (g : Fin 2 → ℂ) :
    ∑ b, o b * (c * g b) = c * ∑ b, o b * g b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `Υ 𝒞 u = -u` for a phased profile that is odd under `-J`. -/
theorem oneParticle_inversion (g : PhotonMode → ℂ)
    (hg : ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ 0 → ∀ a,
      ∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ (g (-k, b)) = -g (k, a))
    (y : FieldSpace) {u : Lp ℂ 2 photonMeasure}
    (hu : u =ᵐ[photonMeasure] fun p => fieldPhase p.1 y * g p) :
    (photonFamily inversion F).one (conjL2 u) = -u := by
  apply Lp.ext
  have hc : conjL2 u =ᵐ[photonMeasure] fun p => starRingEnd ℂ (fieldPhase p.1 y * g p) := by
    filter_upwards [conjL2_ae u, hu] with p h₁ h₂
    rw [h₁, h₂]
  have hn : ∀ᵐ p ∂photonMeasure, p.1 ≠ 0 → ∀ a,
      ∑ b, (overlap inversion F p.1 a b : ℂ) * starRingEnd ℂ (g (-p.1, b)) = -g (p.1, a) :=
    (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae hg
  have h0 : ∀ᵐ p ∂photonMeasure, p.1 ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae
      ((volume : Measure FieldSpace).ae_ne 0)
  filter_upwards [photonFamily_one_ae inversion F hc, Lp.coeFn_neg u, hu, hn, h0]
    with p h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, Pi.neg_apply, h₃]
  simp only [inversion_symm_apply, map_mul, conj_fieldPhase_neg]
  rw [phase_sum, h₄ h₅ p.2, mul_neg]

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T)

theorem base_ae (μ : Fin 3) :
    ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ 0 → ∀ a,
      ∑ b, (overlap inversion F k a b : ℂ) * starRingEnd ℂ (base F χ μ (-k, b)) =
        -base F χ μ (k, a) := by
  filter_upwards [χ.reality] with k hk hk0 a
  exact base_inversion F χ k hk0 hk a μ

theorem infraredBase_ae (μ : Fin 3) :
    ∀ᵐ k ∂(volume : Measure FieldSpace), k ≠ 0 → ∀ a,
      ∑ b, (overlap inversion F k a b : ℂ) *
          starRingEnd ℂ (infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ μ) (-k, b)) =
        -infraredBase (Prod.fst : PhotonMode → FieldSpace) (base F χ μ) (k, a) := by
  filter_upwards [χ.reality] with k hk hk0 a
  exact infraredBase_inversion F χ k hk0 hk a μ

/-- **The article's kernels are odd** under the one-photon part `Υ 𝒞` of the
frame time reversal. -/
theorem kernel_reversal (μ : Fin 3) (y : FieldSpace) :
    (photonFamily inversion F).kernel (photonFamily_dispersive inversion F)
        (kernelConj (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (μ, y))) =
      -PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (μ, y) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun f => (photonFamily inversion F).one (conjL2 f))
      (momentumKernel_fst (formFactors F χ) rfl J (μ, y))).trans
      ((oneParticle_inversion F (base F χ μ) (base_ae F χ μ) y
        (fourierKernel_ae (formFactors F χ) rfl μ y)).trans
        (congrArg Neg.neg (momentumKernel_fst (formFactors F χ) rfl J (μ, y)).symm))
  · exact (congrArg (fun f => (photonFamily inversion F).one (conjL2 f))
      (momentumKernel_snd (formFactors F χ) rfl J (μ, y))).trans
      ((oneParticle_inversion F _ (infraredBase_ae F χ μ) y
        (weightedFourierKernel_ae (formFactors F χ) rfl μ y)).trans
        (congrArg Neg.neg (momentumKernel_snd (formFactors F χ) rfl J (μ, y)).symm))

/-- The photon time reversal for the frame, `W = Γ(Υ) 𝒞`. -/
def frameReversal : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock :=
  (fockConj photonMeasure).trans (photonFamily inversion F).fock

/-- Its action on the radiation graph. -/
def frameRadiationReversal : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace :=
  radiationGraphConj.trans
    ((photonFamily inversion F).radiationGraph (photonFamily_dispersive inversion F))

theorem frameReversal_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (frameRadiationReversal F q) =
      frameReversal F (radiationGraphInclusion q) :=
  ((photonFamily inversion F).radiationGraphInclusion_radiationGraph
    (photonFamily_dispersive inversion F) _).trans
    (congrArg (photonFamily inversion F).fock (radiationGraphInclusion_conj q))

theorem frameReversal_derivative (q : RadiationGraphSpace) :
    radiationGraphDerivative (frameRadiationReversal F q) =
      frameReversal F (radiationGraphDerivative q) :=
  ((photonFamily inversion F).radiationGraphDerivative_radiationGraph
    (photonFamily_dispersive inversion F) _).trans
    (congrArg (photonFamily inversion F).fock (radiationGraphDerivative_conj q))

/-- **The field is odd** under the frame time reversal, `W A(x) W⁻¹ = -A(x)`. -/
theorem kernelField_frameReversal (C : CanonicalSectorCCR photonMeasure) (z : Fin 3 × FieldSpace)
    (q : RadiationGraphSpace) :
    kernelField C (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J z)
        (frameRadiationReversal F q) =
      -frameReversal F (kernelField C (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J z) q) := by
  have h := (photonFamily inversion F).kernelField_kernel (photonFamily_dispersive inversion F) C
    (kernelConj (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (z.1, z.2)))
    (radiationGraphConj q)
  rw [kernel_reversal F χ J z.1 z.2, kernelField_conj] at h
  have hneg : kernelField C (-PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (z.1, z.2)) =
      -kernelField C (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J (z.1, z.2)) :=
    map_neg (kernelFieldMap C) _
  rw [hneg, _root_.neg_apply] at h
  exact (neg_neg _).symm.trans (congrArg Neg.neg h)

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (i : Fin N)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

/-- **`F-time-reversal` for `F_LL`** with the article's frame and cutoff. -/
theorem search_reversal_frame (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i) (currentFlip d) =
      DFT.search (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i) d :=
  search_antiReverse (frameReversal F) (frameRadiationReversal F) (frameReversal_inclusion F)
    (frameReversal_derivative F) V C _ (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
    _ (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) e i
    (kernelField_frameReversal F χ J C) B S d

/-- **`F-time-reversal` for the Lieb functional** with the article's frame and cutoff. -/
theorem lieb_reversal_frame (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (currentFlip d) =
      DFT.lieb (TransformationsPureStates.pureModel V C
        (PhysicalProfiles.momentumKernel (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl J)
        (PhysicalProfiles.kernelBound (formFactors F χ) rfl J)
        (PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl J) B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_flip _ (search_reversal_frame F χ J V C e i B S) d

end Frame

end GptLean.TransformationsTimeReversal
