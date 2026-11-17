import GptLean.PhysicalFockChannelCovariant
import GptLean.PhysicalFockRadiationDomainLocalization
import GptLean.PhysicalFreeDecomposition
import GptLean.PhysicalCoulombReferenceCore

/-!
The actual localization channel preserves the common electronic H1 and
radiation domain. Its output reference vectors are constructed from the
bounded H1 Kraus map and the proved radiation-domain localization result.
Mass and ordinary derivative Parseval identities also give finite total
free energy of the full pure channel, not only its individual slices.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory Gaussian PhotonLocalization PhotonLocalizationKernelCutoffs
  PhotonLocalizationPhysicalKernels PhotonLocalizationFockChannel PhotonLocalizationChannel
  PhysicalNormalTrace PhysicalClosedForms
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000
set_option Elab.async false

def physicalSplit (m : ℕ) : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) :=
  transportSplit PhysicalOnePhotonFourier.fourier (complexOnePhotonIsometry (radius m))

def physicalKraus (BF : StandardSymmetricFockExponential) (N m : ℕ) :
    KrausIsometry (FullHilbert N) :=
  (fullFactorization BF PhysicalOnePhotonFourier.fourier N).factor
    (complexOnePhotonIsometry (radius m))

@[simp] theorem physicalKraus_lift (BF : StandardSymmetricFockExponential) (N m : ℕ) :
    physicalKraus BF N m = KrausL2.lift (volume : Measure (SymmetricLift.Configuration N))
      ((photonFactorization BF).factor (physicalSplit m)) := rfl

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (B : SobolevMultiplierBackground S) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w))
  (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
  (BT : StandardNormalTraceBackground) (N m : ℕ)

include hmult CCR BT in
theorem physicalOutputRadiation_exists
    (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    ∃ r : SpatialRadiationGraph (volume : Measure (SymmetricLift.Configuration N)),
      spatialRadiationInclusion volume r =
        physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a := by
  apply fullFactorization_radiation_domain physicalRadiationCoordinates B J hmult BF CCR BT N m rfl
  exact ⟨PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q,
    (PhysicalFreeReferenceCore.value_matching (Fin N × Fin 3) q).symm⟩

def physicalOutputRadiation (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    SpatialRadiationGraph (volume : Measure (SymmetricLift.Configuration N)) :=
  (physicalOutputRadiation_exists B J hmult BF CCR BT N m q a).choose

theorem physicalOutputRadiation_value (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    spatialRadiationInclusion volume (physicalOutputRadiation B J hmult BF CCR BT N m q a) =
      physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a :=
  (physicalOutputRadiation_exists B J hmult BF CCR BT N m q a).choose_spec

def physicalOutputReference (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    PhysicalFreeForm.Reference (Fin N × Fin 3) :=
  ⟨(channelH1 BF (physicalSplit m) a (PhysicalFreeReferenceCore.electronic (Fin N × Fin 3) q),
      physicalOutputRadiation B J hmult BF CCR BT N m q a), by
    change ElectronicH1Complex.value
      (channelH1 BF (physicalSplit m) a (PhysicalFreeReferenceCore.electronic (Fin N × Fin 3) q)) -
        spatialRadiationInclusion volume (physicalOutputRadiation B J hmult BF CCR BT N m q a) = 0
    exact sub_eq_zero.mpr (physicalOutputRadiation_value B J hmult BF CCR BT N m q a).symm⟩

theorem physicalOutputReference_value (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    PhysicalFreeForm.inclusion (Fin N × Fin 3) (physicalOutputReference B J hmult BF CCR BT N m q a) =
      physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a := rfl

theorem physicalOutputReference_derivative (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (a : ℕ) (i : Fin N × Fin 3) :
    PhysicalFreeForm.ordinary (Fin N × Fin 3) i (physicalOutputReference B J hmult BF CCR BT N m q a) =
      physicalKraus BF N m (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a := rfl

def physicalOutputCoulombReference (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    PhysicalCoulombReferenceCore.Reference N 1 :=
  PhysicalCoulombReferenceCore.attach N 1 (by norm_num)
    (physicalOutputReference B J hmult BF CCR BT N m q a)

theorem physicalOutputCoulombReference_value (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) (a : ℕ) :
    PhysicalPFReference.inclusion (Fin N × Fin 3)
      (fun x => 1 * PhysicalCoulombH1.potential N x)
      (physicalOutputCoulombReference B J hmult BF CCR BT N m q a) =
        physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a := rfl

private theorem mass_tsum_eq {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H →ₗᵢ[ℂ] Space (fun _ : ℕ => K)) (v : H) :
    (∑' a, ENNReal.ofReal (‖U v a‖ ^ 2)) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have he := massForm_eq (fun _ : ℕ => K) (U v)
  simpa only [weightedForm, one_mul, U.norm_map] using he

include hmult CCR in
theorem physicalKraus_radiation_tsum_bound
    (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (∑' a, (PhysicalFreeDecomposition.radiation (Fin N × Fin 3) BT).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        (PhysicalFreeDecomposition.radiation (Fin N × Fin 3) BT).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne
            (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) := by
  let D := fullFormCalculus BF CCR BT PhysicalOnePhotonFourier.fourier N
  have he (v : FullHilbert N) :
      (D.observable radiationFamily).expectation ((BT.realization (FullHilbert N)).rank.rankOne v) =
        (PhysicalFreeDecomposition.radiation (Fin N × Fin 3) BT).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne v) :=
    fullFormCalculus_radiation_eq BF CCR BT PhysicalOnePhotonFourier.fourier N
      ((BT.realization (FullHilbert N)).rank.rankOne_positive v)
  have h : (∑' a, (D.observable radiationFamily).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        (D.observable radiationFamily).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne
            (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) :=
    fullFactorization_radiation_sum_bound physicalRadiationCoordinates B J hmult BF CCR BT
      N m rfl (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)
  exact (tsum_congr (fun a => he
    (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))).symm.le.trans
    (h.trans_eq (congrArg (fun r : ℝ≥0∞ => ENNReal.ofReal (radiationMultiplierConstant B) * r)
      (he (PhysicalFreeForm.inclusion (Fin N × Fin 3) q))))

include hmult CCR in
theorem physicalKraus_radiation_tsum_finite
    (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (∑' a, (PhysicalFreeDecomposition.radiation (Fin N × Fin 3) BT).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))) < ⊤ := by
  apply (physicalKraus_radiation_tsum_bound B J hmult BF CCR BT N m q).trans_lt
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  rw [PhysicalFreeDecomposition.radiation_reference]
  exact ENNReal.ofReal_lt_top

private theorem sum_three_bound (f g h : ℕ → ℝ≥0∞) (a b c C : ℝ≥0∞)
    (hC : 1 ≤ C) (hf : (∑' n, f n) = a) (hg : (∑' n, g n) = b)
    (hh : (∑' n, h n) ≤ C * c) :
    (∑' n, (f n + g n + h n)) ≤ C * (a + b + c) := by
  have hscale (x : ℝ≥0∞) : x ≤ C * x := by
    simpa only [one_mul] using mul_le_mul_left hC x
  rw [ENNReal.tsum_add, ENNReal.tsum_add, hf, hg, mul_add, mul_add]
  exact add_le_add (add_le_add (hscale a) (hscale b)) hh

variable (CF : StandardClosedFormBackground)

include hmult CCR in
theorem physicalKraus_free_tsum_bound (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (∑' a, (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne
            (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) := by
  let U := physicalKraus BF N m
  let v := PhysicalFreeForm.inclusion (Fin N × Fin 3) q
  let rank := (BT.realization (FullHilbert N)).rank
  let kinetic := PhysicalFreeDecomposition.kinetic (Fin N × Fin 3) BT CF
  let rad := PhysicalFreeDecomposition.radiation (Fin N × Fin 3) BT
  have he (a : ℕ) : kinetic.expectation (rank.rankOne (U v a)) =
      ∑ i : Fin N × Fin 3, ENNReal.ofReal
        (‖U (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a‖ ^ 2) := by
    let w := physicalOutputReference B J hmult BF CCR BT N m q a
    have hw : PhysicalFreeForm.inclusion (Fin N × Fin 3) w = U v a :=
      physicalOutputReference_value B J hmult BF CCR BT N m q a
    have hform := PhysicalFreeDecomposition.kinetic_reference (Fin N × Fin 3) BT CF w
    have hsum : ENNReal.ofReal (∑ i, ‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i w‖ ^ 2) =
        ∑ i, ENNReal.ofReal (‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i w‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
    have hder : (∑ i, ENNReal.ofReal (‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i w‖ ^ 2)) =
        ∑ i, ENNReal.ofReal (‖U (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a‖ ^ 2) :=
      Finset.sum_congr rfl fun i _ => congrArg ENNReal.ofReal
        (congrArg (fun z : FullHilbert N => ‖z‖ ^ 2)
          (physicalOutputReference_derivative B J hmult BF CCR BT N m q a i))
    exact (congrArg (fun z : FullHilbert N => kinetic.expectation (rank.rankOne z)) hw).symm.trans
      (hform.trans (hsum.trans hder))
  have hk : (∑' a, kinetic.expectation (rank.rankOne (U v a))) =
      kinetic.expectation (rank.rankOne v) := by
    have hswap : (∑' a, ∑ i : Fin N × Fin 3,
        ENNReal.ofReal (‖U (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a‖ ^ 2)) =
        ∑ i : Fin N × Fin 3, ∑' a,
          ENNReal.ofReal (‖U (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a‖ ^ 2) :=
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    have hmass : (∑ i : Fin N × Fin 3, ∑' a,
        ENNReal.ofReal (‖U (PhysicalFreeForm.ordinary (Fin N × Fin 3) i q) a‖ ^ 2)) =
        ∑ i : Fin N × Fin 3, ENNReal.ofReal (‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i q‖ ^ 2) :=
      Finset.sum_congr rfl fun i _ => mass_tsum_eq U _
    have hsum : ENNReal.ofReal (∑ i, ‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i q‖ ^ 2) =
        ∑ i, ENNReal.ofReal (‖PhysicalFreeForm.ordinary (Fin N × Fin 3) i q‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
    exact (tsum_congr he).trans (hswap.trans (hmass.trans (hsum.symm.trans
      (PhysicalFreeDecomposition.kinetic_reference (Fin N × Fin 3) BT CF q).symm)))
  have hr : (∑' a, rad.expectation (rank.rankOne (U v a))) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) * rad.expectation (rank.rankOne v) :=
    physicalKraus_radiation_tsum_bound B J hmult BF CCR BT N m q
  have hc : (1 : ENNReal) ≤ ENNReal.ofReal (radiationMultiplierConstant B) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [radiationMultiplierConstant]
    nlinarith [sq_nonneg B.multiplierConstant]
  have hout : (∑' a, (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
      (rank.rankOne (U v a))) =
      ∑' a, (ENNReal.ofReal (‖U v a‖ ^ 2) +
        kinetic.expectation (rank.rankOne (U v a)) + rad.expectation (rank.rankOne (U v a))) :=
    tsum_congr (fun a =>
      PhysicalFreeDecomposition.rankOne_decomposition (Fin N × Fin 3) BT CF (U v a))
  have hb := sum_three_bound
    (fun a => ENNReal.ofReal (‖U v a‖ ^ 2))
    (fun a => kinetic.expectation (rank.rankOne (U v a)))
    (fun a => rad.expectation (rank.rankOne (U v a)))
    (ENNReal.ofReal (‖v‖ ^ 2)) (kinetic.expectation (rank.rankOne v))
    (rad.expectation (rank.rankOne v)) (ENNReal.ofReal (radiationMultiplierConstant B))
    hc (mass_tsum_eq U v) hk hr
  exact hout.le.trans (hb.trans_eq (congrArg
    (fun r : ℝ≥0∞ => ENNReal.ofReal (radiationMultiplierConstant B) * r)
    (PhysicalFreeDecomposition.rankOne_decomposition (Fin N × Fin 3) BT CF v).symm))

include hmult CCR in
theorem physicalKraus_free_tsum_finite (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (∑' a, (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
      ((BT.realization (FullHilbert N)).rank.rankOne
        (physicalKraus BF N m (PhysicalFreeForm.inclusion (Fin N × Fin 3) q) a))) < ⊤ := by
  apply (physicalKraus_free_tsum_bound B J hmult BF CCR BT N m CF q).trans_lt
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  rw [PhysicalFreeForm.normalEnergy_rankOne]
  exact ENNReal.ofReal_lt_top

include hmult CCR in
/-- The whole pure channel has finite free energy. -/
theorem physicalKraus_free_pure_finite (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
      (pure (BT.realization (FullHilbert N)).rank (physicalKraus BF N m)
        (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) < ⊤ := by
  exact (PhotonLocalizationChannel.NormalTraceData.pure_expectation (R := (BT.realization (FullHilbert N)).rank)
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF) (fun _ hx => hx)
    (physicalKraus BF N m) (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)).trans_lt
    (physicalKraus_free_tsum_finite B J hmult BF CCR BT N m CF q)

include hmult CCR in
theorem physicalKraus_free_pure_bound (q : PhysicalFreeForm.Reference (Fin N × Fin 3)) :
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
      (pure (BT.realization (FullHilbert N)).rank (physicalKraus BF N m)
        (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) ≤
      ENNReal.ofReal (radiationMultiplierConstant B) *
        (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF).expectation
          ((BT.realization (FullHilbert N)).rank.rankOne
            (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)) := by
  exact (PhotonLocalizationChannel.NormalTraceData.pure_expectation (R := (BT.realization (FullHilbert N)).rank)
    (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF) (fun _ hx => hx)
    (physicalKraus BF N m) (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)).le.trans
    (physicalKraus_free_tsum_bound B J hmult BF CCR BT N m CF q)

end GptLean.PhysicalFock
