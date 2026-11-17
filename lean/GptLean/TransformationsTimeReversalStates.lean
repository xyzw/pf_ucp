import GptLean.TransformationsTimeReversalReference
import GptLean.TransformationsKernelCovariance
import GptLean.TransformationsPureStates
import GptLean.TransformationsPotentials

/-!
Time-reversal invariance of the Levy--Lieb and Lieb functionals on the actual
Pauli--Fierz model, `prop-time-reversal`.

The time reversal is `(Θ Ψ)(X) = (-1)^N 𝒞_J (Ψ(X))`, the pointwise action of
the photon antiunitary `Γ(-J)`, where `(J f)(k, λ) = conj f(-k, λ)`. Applied
pointwise it conjugates the electronic wave function. If the field kernels are
`J`-invariant, which holds for form factors with
`conj (g_a(-k, λ)) = g_a(k, λ)`, then the field is odd, the covariant
derivatives are odd and the energy is invariant. The density is unchanged and
the combined current changes sign. Hence

`F(ρ, -j) = F(ρ, j)`

for `F = F_LL` and for the Lieb functional `F = F_L`.
-/

noncomputable section

namespace GptLean.TransformationsTimeReversal

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsFock TransformationsKernelCovariance
  TransformationsPotentials
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace' : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

theorem norm_neg_one : ‖(-1 : ℂ)‖ = 1 := by simp

theorem neg_conj_re_mul (t : ℝ) (X : ℂ) : t * (-(starRingEnd ℂ) X).re = -(t * X.re) := by
  rw [Complex.neg_re, Complex.conj_re]
  ring

/-- The photon reflection `k ↦ -k` with weight `-1`. -/
abbrev reflection : PointwiseUnitary photonMeasure := photonReflection (-1) norm_neg_one

/-- The photon antiunitary `Γ(-J)`. -/
abbrev photonReversal : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock := fockAnti reflection

/-- Its action on the radiation graph. -/
abbrev radiationReversal : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace :=
  radiationGraphAnti reflection (photonReflection_dispersion (-1) norm_neg_one)

theorem reversal_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationReversal q) = photonReversal (radiationGraphInclusion q) :=
  radiationGraphInclusion_anti _ _ q

theorem reversal_derivative (q : RadiationGraphSpace) :
    radiationGraphDerivative (radiationReversal q) =
      photonReversal (radiationGraphDerivative q) :=
  radiationGraphDerivative_anti _ _ q

theorem reversal_symm_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (radiationReversal.symm q) =
      photonReversal.symm (radiationGraphInclusion q) := by
  apply photonReversal.injective
  refine (reversal_inclusion (radiationReversal.symm q)).symm.trans ?_
  exact (congrArg radiationGraphInclusion (radiationReversal.apply_symm_apply q)).trans
    (photonReversal.apply_symm_apply _).symm

/-- The odd field law `A(x) Θ = - Θ A(x)` from `J`-invariant kernels. -/
theorem kernelField_reversal (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (hk : kernelAnti reflection (photonReflection_dispersion (-1) norm_neg_one) k = (-1 : ℂ) • k)
    (q : RadiationGraphSpace) :
    kernelField C k (radiationReversal q) = -photonReversal (kernelField C k q) := by
  have h := kernelField_anti reflection (photonReflection_dispersion (-1) norm_neg_one) C k q
  rw [hk, neg_one_smul ℂ k] at h
  have hneg : kernelField C (-k) = -kernelField C k := map_neg (kernelFieldMap C) k
  rw [hneg, ContinuousLinearMap.neg_apply] at h
  rw [← h, neg_neg]

variable {N : ℕ}

/-- Time reversal of wave functions. -/
abbrev reversal (v : WaveSpace (Fin N × Fin 3)) : WaveSpace (Fin N × Fin 3) :=
  antiWave photonReversal v

/-- The inverse of time reversal. -/
abbrev reversalInv (v : WaveSpace (Fin N × Fin 3)) : WaveSpace (Fin N × Fin 3) :=
  antiWave photonReversal.symm v

theorem antiWave_permutation (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock) (π : Equiv.Perm (Fin N))
    (v : WaveSpace (Fin N × Fin 3)) :
    PhysicalElectronicFermions.permutation N PhotonFock π (antiWave W v) =
      antiWave W (PhysicalElectronicFermions.permutation N PhotonFock π v) := by
  apply Lp.ext
  have hcomp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (antiWave_ae W v)
  filter_upwards [PhysicalElectronicFermions.permutation_ae N PhotonFock π (antiWave W v),
    hcomp, antiWave_ae W (PhysicalElectronicFermions.permutation N PhotonFock π v),
    PhysicalElectronicFermions.permutation_ae N PhotonFock π v] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (Eq.trans (congrArg W h₄.symm) h₃.symm))

theorem antiWave_mem_fermionic (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)
    {v : WaveSpace (Fin N × Fin 3)}
    (hv : v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    antiWave W v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock := by
  intro π
  refine (antiWave_permutation W π v).trans ((congrArg (antiWave W) (hv π)).trans
    ((antiWave_smul W _ v).trans ?_))
  congr 1
  unfold PhysicalElectronicFermions.signCharacter
  exact map_intCast (starRingEnd ℂ) _

variable (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)
  (hKodd : ∀ z, kernelAnti reflection (photonReflection_dispersion (-1) norm_neg_one) (K z) =
    (-1 : ℂ) • K z)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- Time reversal on the reference domain. -/
abbrev reverseRef (u : Reference (Fin N × Fin 3) V) : Reference (Fin N × Fin 3) V :=
  reverse photonReversal radiationReversal reversal_inclusion V u

include hKodd in
theorem field_odd (q : Fin N × Fin 3) (x : Configuration N) (r : RadiationGraphSpace) :
    kernelField C (κP q x) (radiationReversal r) = -photonReversal (kernelField C (κP q x) r) :=
  kernelField_reversal C _ (hKodd _) r

include hKodd in
theorem energy_reversal (u : Reference (Fin N × Fin 3) V) :
    energy (Fin N × Fin 3) V C κP hκP M hbP e (reverseRef V u) =
      energy (Fin N × Fin 3) V C κP hκP M hbP e u :=
  energy_reverse photonReversal radiationReversal reversal_inclusion reversal_derivative V C κP
    hκP M hbP (field_odd C K hKodd) e u

include hKodd in
/-- Time reversal fixes the density and reverses the current. -/
theorem pair_reversal (u : Reference (Fin N × Fin 3) V) :
    PhysicalPFParticle.pair C K hK M hM V i e (reverseRef V u) =
      currentFlip (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  let T := reverseRef V u
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
    filter_upwards [antiWave_ae photonReversal (inclusion (Fin N × Fin 3) V u)] with z hz
    exact congrArg (fun r : ℝ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * r ^ 2)
      ((congrArg norm hz).trans (photonReversal.norm_map _))
  · intro b t
    have hcov := covariant_reverse photonReversal radiationReversal reversal_inclusion V C κP hκP
      M hbP (field_odd C K hKodd) e (i, b) u
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
    filter_upwards [antiWave_ae photonReversal (inclusion (Fin N × Fin 3) V u),
      Filter.EventuallyEq.of_eq (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ⇑w) hcov),
      Lp.coeFn_neg (antiWave photonReversal (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)),
      antiWave_ae photonReversal (covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u)]
      with z h₁ h₂ h₃ h₄
    change t.weight _ * (⟪inclusion (Fin N × Fin 3) V T z,
      covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ).re = _
    have hinner : ⟪inclusion (Fin N × Fin 3) V T z,
        covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) T z⟫_ℂ =
        -(starRingEnd ℂ) ⟪inclusion (Fin N × Fin 3) V u z,
          covariant (Fin N × Fin 3) V C κP hκP M hbP e (i, b) u z⟫_ℂ := by
      exact (congrArg₂ (fun p q => ⟪p, q⟫_ℂ) h₁ (h₂.trans (h₃.trans
        (congrArg Neg.neg h₄)))).trans ((inner_neg_right _ _).trans
          (congrArg Neg.neg (inner_antiunitary photonReversal _ _)))
    exact (congrArg (fun c : ℂ => t.weight ((PhysicalSourceCoordinates.split i) z).1 * c.re)
      hinner).trans (neg_conj_re_mul _ _)

theorem reversal_reference (u : Reference (Fin N × Fin 3) V) :
    ∃ u' : Reference (Fin N × Fin 3) V,
      inclusion (Fin N × Fin 3) V u' = reversalInv (inclusion (Fin N × Fin 3) V u) :=
  ⟨reverse photonReversal.symm radiationReversal.symm reversal_symm_inclusion V u, rfl⟩

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

include hKodd in
/-- **Time-reversal invariance of `F_LL`**, `F(ρ, -j) = F(ρ, j)`. -/
theorem search_reversal (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) (currentFlip d) =
      DFT.search (TransformationsPureStates.pureModel V C K hK M hM B S e i) d := by
  have h := TransformationsPureStates.search_covariance_of_reference V C K hK M hM B S e i
    reversal reversalInv currentFlip (fun _ => 0)
    (fun v => norm_antiWave _ v) (fun v => norm_antiWave _ v)
    (fun v hv => antiWave_mem_fermionic _ hv) (fun v hv => antiWave_mem_fermionic _ hv)
    (fun v => antiWave_symm _ v) (fun v => antiWave_symm_left _ v)
    (reversal_reference V)
    (fun u _ => ⟨reverseRef V u, rfl,
      (energy_reversal V C K hK M hM e hKodd u).trans (add_zero _).symm,
      pair_reversal V C K hK M hM e i hKodd u⟩) d
  rw [h, EReal.coe_zero, add_zero]

include hKodd in
/-- **Time-reversal invariance of the Lieb functional** `F_L`. -/
theorem lieb_reversal (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) (currentFlip d) =
      DFT.lieb (TransformationsPureStates.pureModel V C K hK M hM B S e i)
        (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_flip _ (search_reversal V C K hK M hM e i hKodd B S) d

/-- For form factors with `conj (g_a(-k, λ)) = g_a(k, λ)` the kernel condition holds. -/
theorem search_reversal_physical {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (F : PhotonLocalizationPhysicalKernels.FormFactors photonMeasure (Fin 3))
    (hF : F.momentum = Prod.fst) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T)
    (hpar : ∀ a (p : PhotonMode), starRingEnd ℂ (F.base a (-p.1, p.2)) = F.base a p)
    (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel V C (PhysicalProfiles.momentumKernel F hF J)
        (PhysicalProfiles.momentumKernel_continuous F hF J) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.momentumKernel_bound F hF J) B S e i) (currentFlip d) =
      DFT.search (TransformationsPureStates.pureModel V C (PhysicalProfiles.momentumKernel F hF J)
        (PhysicalProfiles.momentumKernel_continuous F hF J) (PhysicalProfiles.kernelBound F hF J)
        (PhysicalProfiles.momentumKernel_bound F hF J) B S e i) d :=
  search_reversal V C _ _ _ _ e i
    (fun z => kernelAnti_reflection F hF J (-1) norm_neg_one hpar z.1 z.2) B S d

end GptLean.TransformationsTimeReversal
