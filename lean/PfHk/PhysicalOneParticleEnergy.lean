import PfHk.PhysicalZeroCouplingDerivative

/-! The actual one-electron shifted energy at zero coupling splits into
ordinary electronic kinetic energy, the scalar/current pairings, and the
nonnegative radiation energy. -/

noncomputable section
namespace PfHk.PhysicalOneParticleEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  GptLean.PhysicalPairDuality PfHk.PhysicalOneParticleState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

local instance energyPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance energyWaveDirectInner : InnerProductSpace ℂ (WaveSpace Index) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace Index)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace Index)) }

attribute [local irreducible] inclusion covariant ordinary radiation potential
  PhysicalPFReference.referenceSubspace ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.derivative ElectronicH1Complex.value energy kineticEnergy

private theorem potential_norm_sq_eq_zero (V : Position Index → ℝ) (hV : ∀ X, V X = 0)
    (u : Reference Index V) : ‖potential Index V u‖ ^ 2 = 0 := by
  have hp := potential_energy Index V (fun X => by rw [hV X]) u
  have hz : ENNReal.ofReal (‖potential Index V u‖ ^ 2) = 0 := by
    simpa only [hV, ENNReal.ofReal_zero, zero_mul, lintegral_zero] using hp
  have hn := ENNReal.ofReal_eq_zero.mp hz
  exact le_antisymm hn (sq_nonneg _)

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential 1 1
set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound (formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := 1) Kf
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := 1) Kf hKf
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := 1) Kf MK hMK

/-- The internal energy of the actual one-electron state at zero coupling. -/
theorem internalEnergy (p : State F χ C B S 0 (N := 1)) (u : Ref)
    (hu : inclusion Index (fun _ => 0) u = p.val) :
    (model (0 : Fin 1) F χ C B S 0).energy p =
      (1 / 2 : ℝ) * (∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2) +
        ‖radiation Index (fun _ => 0) u‖ ^ 2 := by
  let uc := PhysicalReferenceCoulombEquiv.equiv (N := 1) 1 zero_le_one u
  have huc : inclusion Index Vp uc = p.val :=
    (PhysicalReferenceCoulombEquiv.inclusion_equiv (N := 1) 1 zero_le_one u).trans hu
  have he := TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S 0
    (0 : Fin 1) p uc huc
  have hpot : ‖potential Index Vp uc‖ ^ 2 = 0 :=
    potential_norm_sq_eq_zero Vp (fun X => congrFun coulomb_potential_one X) uc
  have hrad : radiation Index Vp uc = radiation Index (fun _ => 0) u :=
    PhysicalReferenceCoulombEquiv.radiation_equiv (N := 1) 1 zero_le_one u
  have hcov (q : Index) : covariant Index Vp C κP hκP MK hbP 0 q uc =
      (-Complex.I) • ordinary Index (fun _ => 0) q u := by
    exact (PhysicalReferenceCoulombEquiv.covariant_equiv (N := 1) C κP hκP MK hbP
      1 zero_le_one 0 u q).trans (covariant_zero F χ C u q)
  exact he.trans (by
    unfold energy kineticEnergy
    simp only [hcov, hrad, hpot, norm_smul, norm_neg, Complex.norm_I,
      one_mul, add_zero])

/-- The shifted physical energy equals the concrete electronic form plus
radiation energy. Both potential terms are the actual physical marginals. -/
theorem shiftedEnergy (w : ScalarPotential) (A : VectorPotential)
    (p : State F χ C B S 0 (N := 1)) (u : Ref)
    (hu : inclusion Index (fun _ => 0) u = p.val) :
    PhysicalGroundState.shiftedEnergy (0 : Fin 1) F χ C B S 0 (w, A) p =
      (1 / 2 : ℝ) * (∑ q : Index, ‖ordinary Index (fun _ => 0) q u‖ ^ 2) +
        ‖radiation Index (fun _ => 0) u‖ ^ 2 +
        PhysicalShiftedFormEnergy.scalarSum w u +
        PhysicalShiftedFormEnergy.magneticSum C Kf hKf MK hMK 0 A u := by
  have hp := PhysicalGroundStateWeak.pure_density_eq_pair F χ C B S 0
    (0 : Fin 1) p u hu
  have hs := PhysicalShiftedFormEnergy.pairing_scalar (N := 1) C Kf hKf MK hMK 0
    (0 : Fin 1) w u (fermionic _)
  have ha := PhysicalShiftedFormEnergy.pairing_vector (N := 1) C Kf hKf MK hMK 0
    (0 : Fin 1) A u (fermionic _)
  have hpair : pairPotential (w, A) ((model (0 : Fin 1) F χ C B S 0).density p) =
      PhysicalShiftedFormEnergy.scalarSum w u +
        PhysicalShiftedFormEnergy.magneticSum C Kf hKf MK hMK 0 A u :=
    (congrArg (pairPotential (w, A)) hp).trans
      ((PhysicalShiftedFormEnergy.pairPotential_eq_parts w A _).trans
        (congrArg₂ (fun x y : ℝ => x + y) hs ha))
  exact (congrArg₂ (fun x y : ℝ => x + y)
    (internalEnergy F χ C B S p u hu) hpair).trans (add_assoc _ _ _).symm

end PfHk.PhysicalOneParticleEnergy
