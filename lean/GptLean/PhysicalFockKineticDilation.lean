import GptLean.PhysicalFockChannelReference
import GptLean.PhysicalCovariantKinetic
import GptLean.PhotonLocalizationKineticChannel

/-!
The kinetic dilation source is built from actual weak derivatives,
annihilation, creation and vacuum vectors on the common physical domain.
Its small inputs are pointwise bounds on the one-photon kernels over the
electronic support. No output kinetic estimate or domain transport is
assumed. The physical form-factor specialization supplies these bounds.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhysicalNormalTrace PhysicalClosedForms
  PhotonLocalization PhotonLocalizationChannel PhotonLocalizationPhysicalKernels
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000
set_option Elab.async false

private theorem negative_charge_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e ε a : ℝ) (v : H) (hv : ‖v‖ ≤ ε * a) :
    ‖(-(e : ℂ)) • v‖ ^ 2 ≤ e ^ 2 * ε ^ 2 * a ^ 2 := by
  have hn : ‖(-(e : ℂ)) • v‖ ^ 2 = e ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  exact hn.le.trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg v) hv 2) (sq_nonneg e)).trans_eq (by ring))

private theorem negative_charge_orthogonal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : ℝ) (u v : H)
    (h : ⟪u, v⟫_ℂ = 0) : ⟪u, (-(e : ℂ)) • v⟫_ℂ = 0 := by
  rw [inner_smul_right, h, mul_zero]

variable (N : ℕ) (C : CanonicalSectorCCR photonMeasure)
  (g : (Fin N × Fin 3) → SymmetricLift.Configuration N → WeightedPhotonKernel)
  (hg : ∀ i, AEStronglyMeasurable (g i) volume)
  (L : ℝ) (hL : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ L) (e : ℝ)

local instance electronicNormedAddCommGroup :
    NormedAddCommGroup (ElectronicH1Complex.ComplexH1 PhotonFock (Fin N × Fin 3)) :=
  (ElectronicH1Complex.complexWeakGraph PhotonFock (Fin N × Fin 3)).normedAddCommGroup

local instance freeReferenceNormedAddCommGroup :
    NormedAddCommGroup (PhysicalFreeForm.Reference (Fin N × Fin 3)) :=
  (PhysicalFreeReferenceCore.freeSubspace (Fin N × Fin 3)).normedAddCommGroup

local instance freeReferenceNormedSpace : NormedSpace ℂ (PhysicalFreeForm.Reference (Fin N × Fin 3)) :=
  (PhysicalFreeReferenceCore.freeSubspace (Fin N × Fin 3)).normedSpace

local instance freeReferenceModule : Module ℂ (PhysicalFreeForm.Reference (Fin N × Fin 3)) :=
  (freeReferenceNormedSpace N).toModule

local instance freeReferenceSMul : SMul ℂ (PhysicalFreeForm.Reference (Fin N × Fin 3)) :=
  (freeReferenceModule N).toSMul

def freeCovariant (i : Fin N × Fin 3) :
    PhysicalFreeForm.Reference (Fin N × Fin 3) →L[ℂ] FullHilbert N :=
  (PhysicalPFReference.covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
    C g hg L hL e i).comp (PhysicalCoulombReferenceCore.attach N 1 zero_le_one)

def dilationDerivativeConstant : ℝ := 2 * ∑ i, ‖freeCovariant N C g hg L hL e i‖

theorem dilationDerivativeConstant_nonneg : 0 ≤ dilationDerivativeConstant N C g hg L hL e := by
  unfold dilationDerivativeConstant
  positivity

private theorem free_norm_sqrt (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    ‖PhysicalFreeForm.energyOutput (Fin N × Fin 3) q‖ =
      Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q) := by
  exact (Real.sqrt_sq (norm_nonneg
    (PhysicalFreeForm.energyOutput (Fin N × Fin 3) q))).symm.trans
      (congrArg Real.sqrt (PhysicalFreeForm.energyOutput_norm_sq (Fin N × Fin 3) q))

theorem freeCovariant_sum_bound (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    ∑ i, ‖freeCovariant N C g hg L hL e i q‖ ≤
      dilationDerivativeConstant N C g hg L hL e *
        Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q) := by
  have hq : ‖q‖ ≤ 2 * Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q) :=
    (PhysicalFreeForm.reference_norm_le_energyOutput (Fin N × Fin 3) q).trans_eq
      (congrArg (fun r : ℝ => 2 * r) (free_norm_sqrt N q))
  calc
    _ ≤ ∑ i, ‖freeCovariant N C g hg L hL e i‖ *
        (2 * Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q)) := by
      apply Finset.sum_le_sum
      intro i _
      exact ((freeCovariant N C g hg L hL e i).le_opNorm q).trans
        (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; unfold dilationDerivativeConstant; ring

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (B : SobolevMultiplierBackground S) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w))
  (BF : StandardSymmetricFockExponential) (BT : StandardNormalTraceBackground)
  (CF : StandardClosedFormBackground) (m : ℕ)
  (κ : (Fin N × Fin 3) → SymmetricLift.Configuration N → ChannelKernel (physicalSplit m))
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (t : (Fin N × Fin 3) → SymmetricLift.Configuration N → WeightedPhotonKernel)
  (ht : ∀ i, AEStronglyMeasurable (t i) volume)
  (K : ℝ) (hK : ∀ i, ∀ᵐ x ∂volume, ‖t i x‖ ≤ K)
  (hfull : ∀ i, ∀ᵐ x ∂volume, (g i x).val.1 = (κ i x).val.1)
  (hretained : ∀ i, ∀ᵐ x ∂volume, (κ i x).val.2 = g i x - t i x)

private theorem freeCovariant_normalEnergy (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (PhysicalCovariantKinetic.normalEnergy N C g hg L hL e BT CF).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖freeCovariant N C g hg L hL e i q‖ ^ 2) := by
  let r := PhysicalCoulombReferenceCore.attach N 1 zero_le_one q
  let E := PhysicalCovariantKinetic.normalEnergy N C g hg L hL e BT CF
  have hv : PhysicalPFReference.inclusion (Fin N × Fin 3)
      (PhysicalCovariantKinetic.potential N) r = PhysicalFreeForm.inclusion (Fin N × Fin 3) q := rfl
  have hd (i : Fin N × Fin 3) : PhysicalPFReference.covariant (Fin N × Fin 3)
      (PhysicalCovariantKinetic.potential N) C g hg L hL e i r =
        freeCovariant N C g hg L hL e i q := rfl
  have he := PhysicalCovariantKinetic.normalEnergy_reference N C g hg L hL e BT CF r
  have hvE := congrArg (fun v : FullHilbert N => E.expectation
    ((BT.realization (FullHilbert N)).rank.rankOne v)) hv
  exact hvE.symm.trans (he.trans (congrArg ENNReal.ofReal
    (congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
      (Finset.sum_congr rfl fun i _ => congrArg (fun v : FullHilbert N => ‖v‖ ^ 2) (hd i)))))

include hfull hretained in
/-- The coordinate identity holds on the entire actual common domain,
independently of any compact support or small-error estimate. -/
theorem physicalOutput_covariant (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (a : ℕ) (i : Fin N × Fin 3) :
    PhysicalPFReference.covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
      C g hg L hL e i (physicalOutputCoulombReference B J hmult BF C BT N m q a) =
      physicalKraus BF N m
        (freeCovariant N C g hg L hL e i q +
          (e : ℂ) • spatialField volume C (t i) (ht i) K (hK i)
            (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q)) a -
        (e : ℂ) • spatialChannelVacuum volume BF C (physicalSplit m) (κ i) (hκ i) M (hM i)
          (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q) a :=
  channel_covariant_identity BF C (physicalSplit m) (κ i) (hκ i) M (hM i)
    (g i) (t i) (hg i) (ht i) L K (hL i) (hK i) (hfull i) (hretained i)
    (PhysicalFreeReferenceCore.electronic (Fin N × Fin 3) q)
    (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q)
    (physicalOutputRadiation B J hmult BF C BT N m q a)
    (PhysicalFreeReferenceCore.value_matching (Fin N × Fin 3) q).symm a
    (physicalOutputRadiation_value B J hmult BF C BT N m q a) e i

set_option maxHeartbeats 400000 in
/-- A direct physical source, using the proved output reference domain. -/
def physicalKineticDilation (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hnegative : ∀ i, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖(t i x).val.2‖ ≤ ε)
    (hl2 : ∀ i, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖(t i x).val.1‖ ≤ ε)
    (hloss : ∀ i, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖(κ i x).val.1‖ ^ 2 - ‖(κ i x).val.2.val.1‖ ^ 2 ≤ ε ^ 2) :
    KineticDilationSource (A := (BT.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C g hg L hL e BT CF)
      (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF)
      (physicalKraus BF N m) (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)
      e ε 3 (dilationDerivativeConstant N C g hg L hL e) := by
  let u := PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q
  let U := physicalKraus BF N m
  let d := fun i => freeCovariant N C g hg L hL e i q
  let ann := fun i => spatialAnnihilation volume (t i) (ht i) K (hK i) u
  let cre := fun i => spatialCreation volume C (t i) (ht i) K (hK i) u
  let vac := fun i => spatialChannelVacuum volume BF C (physicalSplit m) (κ i) (hκ i) M (hM i) u
  let noise := fun i => (-(e : ℂ)) • vac i
  let loc := fun i => U (d i + (e : ℂ) • (ann i + cre i)) + noise i
  have hvalue : spatialRadiationInclusion volume u = PhysicalFreeForm.inclusion (Fin N × Fin 3) q :=
    (PhysicalFreeReferenceCore.value_matching (Fin N × Fin 3) q).symm
  have hmass : ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖ ≤
      Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q) := by
    have hp := PiLp.norm_apply_le
      (PhysicalFreeForm.energyOutput (Fin N × Fin 3) q) (Sum.inr 0)
    have he := congrArg (fun v : FullHilbert N => ‖v‖)
      (PhysicalFreeForm.energyOutput_mass (Fin N × Fin 3) q)
    exact (he.symm.trans_le hp).trans_eq (free_norm_sqrt N q)
  have hrad : ‖spatialRadiationDerivative volume u‖ ≤
      Real.sqrt (PhysicalFreeForm.energy (Fin N × Fin 3) q) := by
    have hp := PiLp.norm_apply_le
      (PhysicalFreeForm.energyOutput (Fin N × Fin 3) q) (Sum.inr 1)
    have he := congrArg (fun v : FullHilbert N => ‖v‖)
      (PhysicalFreeForm.energyOutput_radiation (Fin N × Fin 3) q)
    exact (he.symm.trans_le hp).trans_eq (free_norm_sqrt N q)
  have hgraph (a : ℕ) (i : Fin N × Fin 3) :
      PhysicalPFReference.covariant (Fin N × Fin 3) (PhysicalCovariantKinetic.potential N)
        C g hg L hL e i (physicalOutputCoulombReference B J hmult BF C BT N m q a) = loc i a := by
    have h := physicalOutput_covariant N C g hg L hL e B J hmult BF BT m
      κ hκ M hM t ht K hK hfull hretained q a i
    have htfield : spatialField volume C (t i) (ht i) K (hK i) u = ann i + cre i :=
      congrArg (fun A : SpatialRadiationGraph (volume : Measure (SymmetricLift.Configuration N)) →L[ℂ]
        FullHilbert N => A u) (spatialField_eq_parts volume C (t i) (ht i) K (hK i))
    change _ = U (d i + (e : ℂ) • spatialField volume C (t i) (ht i) K (hK i) u) a -
      (e : ℂ) • vac i a at h
    have hfield := congrArg (fun f : FullHilbert N =>
      U (d i + (e : ℂ) • f) a - (e : ℂ) • vac i a) htfield
    have hloc : U (d i + (e : ℂ) • (ann i + cre i)) a - (e : ℂ) • vac i a = loc i a := by
      change _ = U (d i + (e : ℂ) • (ann i + cre i)) a + ((-(e : ℂ)) • vac i) a
      simp only [neg_smul, lp.coeFn_neg, lp.coeFn_smul, Pi.neg_apply, Pi.smul_apply, sub_eq_add_neg]
    exact h.trans (hfield.trans hloc)
  refine
    { control := PhysicalFreeForm.energy (Fin N × Fin 3) q
      control_nonneg := by unfold PhysicalFreeForm.energy; positivity
      control_eq := PhysicalFreeForm.normalEnergy_rankOne (Fin N × Fin 3) BT CF q
      derivative := d
      annihilated := ann
      created := cre
      noise := noise
      localized := loc
      radiationNorm := ‖spatialRadiationDerivative volume u‖
      massNorm := ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖
      radiationNorm_nonneg := norm_nonneg _
      massNorm_nonneg := norm_nonneg _
      annihilation := fun i => spatialAnnihilation_supported_bound volume (t i) (ht i) K (hK i)
        ε u (hnegative i)
      creation := ?_
      scale_le := by linarith only [hmass, hrad]
      mass_le := ?_
      derivative_le := freeCovariant_sum_bound N C g hg L hL e q
      noise_le := ?_
      intertwining := fun _ => rfl
      orthogonality := ?_
      original_form := freeCovariant_normalEnergy N C g hg L hL e BT CF q
      coordinate_form := ?_ }
  · intro i
    have h := spatialCreation_supported_bound volume C (t i) (ht i) K (hK i) ε u (hl2 i)
    exact h.trans_eq (congrArg (fun w : FullHilbert N => ‖ann i‖ ^ 2 + ε ^ 2 * ‖w‖ ^ 2) hvalue)
  · unfold PhysicalFreeForm.energy
    have hs : 0 ≤ ∑ i, ‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i q‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hfirst : ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖ ^ 2 ≤
        ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖ ^ 2 +
          ∑ i, ‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i q‖ ^ 2 := le_add_of_nonneg_right hs
    exact hfirst.trans (le_add_of_nonneg_right
      (sq_nonneg ‖PhysicalFreeForm.radiation (Fin N × Fin 3) q‖))
  · intro i
    have hv := spatialChannelVacuum_supported_norm_le volume BF C (physicalSplit m)
      (κ i) (hκ i) M (hM i) ε hε u (hloss i)
    have hv' := hv.trans_eq (congrArg (fun w : FullHilbert N => ε * ‖w‖) hvalue)
    exact negative_charge_bound e ε ‖PhysicalFreeForm.inclusion (Fin N × Fin 3) q‖ (vac i) hv'
  · intro i
    exact negative_charge_orthogonal e (U (d i + (e : ℂ) • (ann i + cre i))) (vac i)
      (spatialChannelVacuum_orthogonal volume BF C (physicalSplit m) (κ i) (hκ i) M (hM i) u
        (d i + (e : ℂ) • (ann i + cre i)))
  · intro a
    have he := PhysicalCovariantKinetic.normalEnergy_reference N C g hg L hL e BT CF
      (physicalOutputCoulombReference B J hmult BF C BT N m q a)
    have hvE := congrArg (fun v : FullHilbert N =>
      (PhysicalCovariantKinetic.normalEnergy N C g hg L hL e BT CF).expectation
        ((BT.realization (FullHilbert N)).rank.rankOne v))
      (physicalOutputCoulombReference_value B J hmult BF C BT N m q a)
    exact hvE.symm.trans (he.trans (congrArg ENNReal.ofReal
      (congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
        (Finset.sum_congr rfl fun i _ => congrArg (fun v : FullHilbert N => ‖v‖ ^ 2) (hgraph a i)))))

end GptLean.PhysicalFock
