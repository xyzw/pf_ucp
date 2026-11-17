import GptLean.PhysicalFockKineticDilation
import GptLean.PhysicalFockPhysicalProfiles

/-!
The kinetic dilation uses the actual form-factor tails and the proved
compact cutoff error. Its support condition is geometric. All small
annihilation, creation and vacuum bounds follow from the same physical
kernel family, rather than being inputs to this constructor.
-/

noncomputable section
namespace GptLean.PhysicalFock.PhysicalProfiles

open MeasureTheory Gaussian PhotonLocalizationPhysicalKernels PhotonLocalizationKernelCutoffs
  PhotonLocalization PhotonLocalizationFockChannel PhysicalNormalTrace PhysicalClosedForms SymmetricLift
open PhysicalNormalTrace.StandardNormalTraceBackground
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000
set_option Elab.async false

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  (F : FormFactors photonMeasure (Fin 3)) (hF : F.momentum = Prod.fst)
  (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S)
  (hmult : ∀ (χ : FieldSpace → ℝ) (_hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hc : HasCompactSupport χ)
    (hχm : AEStronglyMeasurable χ (volume : Measure FieldSpace))
    (hb : ∀ᵐ y ∂(volume : Measure FieldSpace), |χ y| ≤ 1) a w,
    physicalRadiationCoordinates.representative J a w →
    physicalRadiationCoordinates.representative J
      (PhotonKernelLocalization.l2Multiplier χ hχm hb a) (B.multiplier χ w))

def tailKernel (m : ℕ) : Fin 3 × FieldSpace → WeightedPhotonKernel :=
  profileMomentumKernel physicalRadiationCoordinates J rfl (tailProfile F hF J B hmult m)

def tailKernelBound (m : ℕ) : ℝ :=
  profileKernelBound physicalRadiationCoordinates J (tailProfile F hF J B hmult m)

theorem tailKernel_continuous (m : ℕ) : Continuous (tailKernel F hF J B hmult m) :=
  profileMomentumKernel_continuous physicalRadiationCoordinates J rfl (tailProfile F hF J B hmult m)

theorem tailKernel_bound (m : ℕ) (z : Fin 3 × FieldSpace) :
    ‖tailKernel F hF J B hmult m z‖ ≤ tailKernelBound F hF J B hmult m :=
  profileMomentumKernel_bound physicalRadiationCoordinates J rfl (tailProfile F hF J B hmult m) z

def channelKernel (m : ℕ) : Fin 3 × FieldSpace → ChannelKernel (physicalSplit m) :=
  profileChannelKernel physicalRadiationCoordinates J rfl (profile F hF J)
    (tailProfile F hF J B hmult m) m (tailProfile_l2 F hF J B hmult m)

def channelKernelBound (m : ℕ) : ℝ :=
  profileChannelKernelBound physicalRadiationCoordinates J (profile F hF J)
    (tailProfile F hF J B hmult m)

theorem channelKernel_continuous (m : ℕ) : Continuous (channelKernel F hF J B hmult m) :=
  profileChannelKernel_continuous physicalRadiationCoordinates J rfl (profile F hF J)
    (tailProfile F hF J B hmult m) m (tailProfile_l2 F hF J B hmult m)

theorem channelKernel_bound (m : ℕ) (z : Fin 3 × FieldSpace) :
    ‖channelKernel F hF J B hmult m z‖ ≤ channelKernelBound F hF J B hmult m :=
  profileChannelKernel_bound physicalRadiationCoordinates J rfl (profile F hF J)
    (tailProfile F hF J B hmult m) m (tailProfile_l2 F hF J B hmult m) z

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (BT : StandardNormalTraceBackground) (CF : StandardClosedFormBackground)
  (N : ℕ) (e : ℝ)

theorem radiationSource_support (l : ℕ) (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (hsupport : ∀ i : Fin N × Fin 3, ∀ᵐ x ∂volume,
      PhysicalFreeForm.inclusion (Fin N × Fin 3) q x ≠ 0 → ‖particle x i.1‖ ≤ l) :
    ∀ i : Fin N × Fin 3, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖particle x i.1‖ ≤ l := by
  intro i
  have hi : PhysicalFreeForm.inclusion (Fin N × Fin 3) q =ᵐ[volume]
      fun x => radiationGraphInclusion (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x) := by
    have h := radiationGraphInclusion.coeFn_compLpL
      (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q)
    exact (congrArg (fun v : FullHilbert N => v =ᵐ[volume] fun x =>
      radiationGraphInclusion (PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x))
      (PhysicalFreeReferenceCore.value_matching (Fin N × Fin 3) q)).mpr h
  filter_upwards [hsupport i, hi] with x hx hi
  intro hu
  apply hx
  intro hz
  apply hu
  apply radiationGraphInclusion_injective
  exact hi.symm.trans (hz.trans (map_zero radiationGraphInclusion).symm)

def kineticDilation (l m : ℕ) (q : PhysicalFreeForm.Reference (Fin N × Fin 3))
    (hsupport : ∀ i : Fin N × Fin 3, ∀ᵐ x ∂volume,
      PhysicalFreeReferenceCore.radiationSource (Fin N × Fin 3) q x ≠ 0 →
        ‖particle x i.1‖ ≤ l) :
    KineticDilationSource (A := (BT.realization (FullHilbert N)).rank) (ι := Fin N × Fin 3)
      (PhysicalCovariantKinetic.normalEnergy N C (particleKernel F hF J N)
        (particleKernel_measurable F hF J N) (kernelBound F hF J)
        (particleKernel_bound F hF J N) e BT CF)
      (PhysicalFreeForm.normalEnergy (Fin N × Fin 3) BT CF)
      (physicalKraus BF N m) (PhysicalFreeForm.inclusion (Fin N × Fin 3) q)
      e (cutoffError F J B l m) 3
      (dilationDerivativeConstant N C (particleKernel F hF J N)
        (particleKernel_measurable F hF J N) (kernelBound F hF J)
        (particleKernel_bound F hF J N) e) := by
  let κ := fun (i : Fin N × Fin 3) (x : Configuration N) => channelKernel F hF J B hmult m (i.2, particle x i.1)
  let t := fun (i : Fin N × Fin 3) (x : Configuration N) => tailKernel F hF J B hmult m (i.2, particle x i.1)
  have hκ (i : Fin N × Fin 3) : AEStronglyMeasurable (κ i) volume :=
    ((channelKernel_continuous F hF J B hmult m).comp
      (continuous_const.prodMk (particleLinear i.1).continuous_of_finiteDimensional)).aestronglyMeasurable
  have ht (i : Fin N × Fin 3) : AEStronglyMeasurable (t i) volume :=
    ((tailKernel_continuous F hF J B hmult m).comp
      (continuous_const.prodMk (particleLinear i.1).continuous_of_finiteDimensional)).aestronglyMeasurable
  apply physicalKineticDilation N C (particleKernel F hF J N)
    (particleKernel_measurable F hF J N) (kernelBound F hF J) (particleKernel_bound F hF J N) e
    B J hmult BF BT CF m κ hκ (channelKernelBound F hF J B hmult m)
    (fun i => ae_of_all _ fun x => channelKernel_bound F hF J B hmult m (i.2, particle x i.1))
    t ht (tailKernelBound F hF J B hmult m)
    (fun i => ae_of_all _ fun x => tailKernel_bound F hF J B hmult m (i.2, particle x i.1))
    (fun _ => ae_of_all _ fun _ => rfl) (fun _ => ae_of_all _ fun _ => rfl)
    q (cutoffError F J B l m) (cutoffError_nonneg F J B l m)
  · intro i
    filter_upwards [hsupport i] with x hx
    intro hu
    have hb := (cutoff_components F hF J B hmult l m (i.2, particle x i.1) (hx hu)).2.1
    exact (profileMomentumKernel_negative_norm physicalRadiationCoordinates J rfl
      (tailProfile F hF J B hmult m) (i.2, particle x i.1)).le.trans hb
  · intro i
    filter_upwards [hsupport i] with x hx
    intro hu
    have hb := (cutoff_components F hF J B hmult l m (i.2, particle x i.1) (hx hu)).1
    exact (profileMomentumKernel_l2_norm physicalRadiationCoordinates J rfl
      (tailProfile F hF J B hmult m) (i.2, particle x i.1)).le.trans hb
  · intro i
    filter_upwards [hsupport i] with x hx
    intro hu
    have hb := (cutoff_components F hF J B hmult l m (i.2, particle x i.1) (hx hu)).2.2
    have he := profileChannelKernel_mass_loss physicalRadiationCoordinates J rfl (profile F hF J)
      (tailProfile F hF J B hmult m) m (tailProfile_l2 F hF J B hmult m) (i.2, particle x i.1)
    exact he.le.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end GptLean.PhysicalFock.PhysicalProfiles
