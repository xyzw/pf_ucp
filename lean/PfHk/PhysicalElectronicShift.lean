import PfHk.ElectronicShiftH1
import PfHk.PhysicalFreeOperator

/-! Arbitrary electronic translations with the photon vector unchanged.
The field profile is translated at the same time. This applies when the
electron centers are shifted independently. -/

noncomputable section
namespace PfHk.PhysicalElectronicShift

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.TransformationsAffine GptLean.TransformationsTranslation
  PfHk.PhysicalCutoffCommutator
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000
set_option Elab.async false

local instance shiftPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.referenceSubspace
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.value ElectronicH1Complex.derivative
  radiationGraphInclusion radiationGraphDerivative

variable {I : Type} [Fintype I] [DecidableEq I] (c : Position I)

local instance shiftWaveDirectInner : InnerProductSpace ℂ (WaveSpace I) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace I)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace I)) }

private theorem inner_shift (v u : WaveSpace I) :
    ⟪shiftL2 c v, shiftL2 c u⟫_ℂ = ⟪v, u⟫_ℂ :=
  LinearIsometry.inner_map_map (𝕜 := ℂ) (shiftL2 (I := I) (F := PhotonFock) c) v u

private theorem electronic_value (u : Reference I (fun _ => 0)) :
    ElectronicH1Complex.value (E := PhotonFock) (I := I)
        (h1Shift (I := I) (H := PhotonFock) c (electronic I (fun _ => 0) u)) =
      shiftL2 c (inclusion I (fun _ => 0) u) :=
  h1Shift_value (I := I) (H := PhotonFock) c (electronic I (fun _ => 0) u)

private theorem radiation_value (u : Reference I (fun _ => 0)) :
    spatialRadiationInclusion volume (shiftL2 c (radiationSource I (fun _ => 0) u)) =
      shiftL2 c (inclusion I (fun _ => 0) u) :=
  (shiftL2_compLpL c radiationGraphInclusion (radiationSource I (fun _ => 0) u)).symm.trans
    (congrArg (shiftL2 c) (radiation_matches I (fun _ => 0) u))

private theorem zero_potential (u : WaveSpace I) :
    ((u, 0) : WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun _ : Position I => (Real.sqrt (0 : ℝ) : ℂ)) := by
  change ∀ᵐ x ∂volume, (0 : WaveSpace I) x = (Real.sqrt (0 : ℝ) : ℂ) • u x
  filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))] with x hx
  simpa only [Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul] using hx

/-- Translation on all actual free reference coordinates. -/
private def assembleFreeReference (q : ElectronicGraph I) (r : RadiationGraph I) (w : WaveSpace I)
    (hq : ElectronicH1Complex.value (E := PhotonFock) (I := I) q = w) (hr : spatialRadiationInclusion volume r = w) :
    Reference I (fun _ => 0) :=
  ⟨(q, r, ⟨(w, 0), zero_potential _⟩), by
    unfold referenceSubspace
    change (ElectronicH1Complex.value (E := PhotonFock) (I := I) q - spatialRadiationInclusion volume r,
      ElectronicH1Complex.value (E := PhotonFock) (I := I) q - w) = (0, 0)
    exact Prod.ext (sub_eq_zero.mpr (hq.trans hr.symm)) (sub_eq_zero.mpr hq)⟩

def shiftReference (u : Reference I (fun _ => 0)) : Reference I (fun _ => 0) :=
  assembleFreeReference (h1Shift (I := I) (H := PhotonFock) c (electronic I (fun _ => 0) u))
    (shiftL2 c (radiationSource I (fun _ => 0) u)) (shiftL2 c (inclusion I (fun _ => 0) u))
    (electronic_value c u) (radiation_value c u)

theorem inclusion_shift (u : Reference I (fun _ => 0)) :
    inclusion I (fun _ => 0) (shiftReference c u) = shiftL2 c (inclusion I (fun _ => 0) u) :=
  electronic_value c u

theorem inclusion_shift_ae (u : Reference I (fun _ => 0)) :
    inclusion I (fun _ => 0) (shiftReference c u) =ᵐ[volume]
      fun x => inclusion I (fun _ => 0) u (x + c) :=
  (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace I => ⇑z) (inclusion_shift c u))).trans
    (shiftL2_ae c (inclusion I (fun _ => 0) u))

theorem inclusion_shift_supported (u : Reference I (fun _ => 0)) {s : Set (Position I)}
    (hu : ∀ᵐ x ∂volume, x ∉ s → inclusion I (fun _ => 0) u x = 0) :
    ∀ᵐ x ∂volume, x + c ∉ s → inclusion I (fun _ => 0) (shiftReference c u) x = 0 := by
  filter_upwards [inclusion_shift_ae c u, ae_shift c hu] with x hx hs
  exact fun hxs => hx.trans (hs hxs)

theorem source_shift_supported (f : WaveSpace I) {s : Set (Position I)}
    (hf : ∀ᵐ x ∂volume, x ∉ s → f x = 0) :
    ∀ᵐ x ∂volume, x + c ∉ s → shiftL2 c f x = 0 := by
  filter_upwards [shiftL2_ae c f, ae_shift c hf] with x hx hs
  exact fun hxs => hx.trans (hs hxs)

theorem ordinary_shift (u : Reference I (fun _ => 0)) (i : I) :
    ordinary I (fun _ => 0) i (shiftReference c u) =
      shiftL2 c (ordinary I (fun _ => 0) i u) :=
  h1Shift_derivative (I := I) (H := PhotonFock) c (electronic I (fun _ => 0) u) i

theorem radiationSource_shift (u : Reference I (fun _ => 0)) :
    radiationSource I (fun _ => 0) (shiftReference c u) =
      shiftL2 c (radiationSource I (fun _ => 0) u) := rfl

theorem radiation_shift (u : Reference I (fun _ => 0)) :
    radiation I (fun _ => 0) (shiftReference c u) =
      shiftL2 c (radiation I (fun _ => 0) u) :=
  (shiftL2_compLpL c radiationGraphDerivative (radiationSource I (fun _ => 0) u)).symm

theorem potential_shift (u : Reference I (fun _ => 0)) :
    potential I (fun _ => 0) (shiftReference c u) = 0 := rfl

attribute [local irreducible] shiftReference PhysicalPFReference.ordinary
  PhysicalPFReference.inclusion PhysicalPFReference.radiation PhysicalPFReference.potential

theorem shiftReference_neg (u : Reference I (fun _ => 0)) :
    shiftReference (-c) (shiftReference c u) = u := by
  apply inclusion_injective I (fun _ => 0)
  exact (inclusion_shift (-c) (shiftReference c u)).trans
    ((congrArg (shiftL2 (-c)) (inclusion_shift c u)).trans (shiftL2_neg c _))

theorem shiftReference_neg_right (u : Reference I (fun _ => 0)) :
    shiftReference c (shiftReference (-c) u) = u := by
  simpa only [neg_neg] using shiftReference_neg (-c) u

include c in
theorem free_potential_zero (u : Reference I (fun _ => 0)) :
    potential I (fun _ => 0) u = 0 :=
  (congrArg (potential I (fun _ => 0)) (shiftReference_neg_right c u)).symm.trans
    (potential_shift c (shiftReference (-c) u))

theorem potential_transport (u : Reference I (fun _ => 0)) :
    potential I (fun _ => 0) (shiftReference c u) =
      shiftL2 c (potential I (fun _ => 0) u) :=
  (potential_shift c u).trans ((map_zero (shiftL2 c)).symm.trans
    (congrArg (shiftL2 c) (free_potential_zero c u).symm))

def shiftedProfile (κ : I → Position I → WeightedPhotonKernel) :
    I → Position I → WeightedPhotonKernel := fun i x => κ i (x + c)

theorem shifted_measurable (κ : I → Position I → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume) (i : I) :
    AEStronglyMeasurable (shiftedProfile c κ i) volume :=
  (hκ i).comp_measurePreserving (measurePreserving_add_right volume c)

theorem shifted_bound (κ : I → Position I → WeightedPhotonKernel) (M : ℝ)
    (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (i : I) :
    ∀ᵐ x ∂volume, ‖shiftedProfile c κ i x‖ ≤ M := ae_shift c (hbound i)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ κ' : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (hκ' : ∀ i, AEStronglyMeasurable (κ' i) volume)
  (M : ℝ) (hb : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hb' : ∀ i, ∀ᵐ x ∂volume, ‖κ' i x‖ ≤ M)
  (hshift : ∀ i, ∀ᵐ x ∂volume, κ' i x = κ i (x + c))

include hshift in
theorem field_shift (u : Reference I (fun _ => 0)) (i : I) :
    field I (fun _ => 0) C κ' hκ' M hb' i (shiftReference c u) =
      shiftL2 c (field I (fun _ => 0) C κ hκ M hb i u) := by
  apply Lp.ext
  have hs := radiationSource_shift c u
  have ha := (Filter.EventuallyEq.of_eq (congrArg (fun z : RadiationGraph I => ⇑z) hs)).trans
    (shiftL2_ae c (radiationSource I (fun _ => 0) u))
  have hnew : field I (fun _ => 0) C κ' hκ' M hb' i (shiftReference c u) =ᵐ[volume]
      fun x => kernelField C (κ' i x) (radiationSource I (fun _ => 0) (shiftReference c u) x) := by
    simpa only [PhysicalPFReference.field, ContinuousLinearMap.comp_apply] using
      spatialField_ae volume C (κ' i) (hκ' i) M (hb' i)
        (radiationSource I (fun _ => 0) (shiftReference c u))
  have hold : field I (fun _ => 0) C κ hκ M hb i u =ᵐ[volume]
      fun x => kernelField C (κ i x) (radiationSource I (fun _ => 0) u x) := by
    simpa only [PhysicalPFReference.field, ContinuousLinearMap.comp_apply] using
      spatialField_ae volume C (κ i) (hκ i) M (hb i) (radiationSource I (fun _ => 0) u)
  filter_upwards [hnew, ha, hshift i,
    shiftL2_ae c (field I (fun _ => 0) C κ hκ M hb i u),
    ae_shift c hold] with x h₁ h₂ h₃ h₄ h₅
  exact h₁.trans ((congrArg₂ (fun k q => kernelField C k q) h₃ h₂).trans
    (h₅.symm.trans h₄.symm))

include hshift in
theorem covariant_shift (e : ℝ) (u : Reference I (fun _ => 0)) (i : I) :
    covariant I (fun _ => 0) C κ' hκ' M hb' e i (shiftReference c u) =
      shiftL2 c (covariant I (fun _ => 0) C κ hκ M hb e i u) :=
  (covariant_apply I (fun _ => 0) C κ' hκ' M hb' e i (shiftReference c u)).trans
    ((congrArg₂ (fun a b : WaveSpace I => (-Complex.I) • a - (e : ℂ) • b)
      (ordinary_shift c u i) (field_shift c C κ κ' hκ hκ' M hb hb' hshift u i)).trans
      ((congrArg₂ (· - ·) (map_smul (shiftL2 c) (-Complex.I) _).symm
        (map_smul (shiftL2 c) (e : ℂ) _).symm).trans
        ((map_sub (shiftL2 c) _ _).symm.trans
          (congrArg (shiftL2 c) (covariant_apply I (fun _ => 0) C κ hκ M hb e i u).symm))))

include hshift in
theorem form_shift (e : ℝ) (v u : Reference I (fun _ => 0)) :
    PhysicalLocalEnergy.form (fun _ => 0) C κ' hκ' M hb' e
        (shiftReference c v) (shiftReference c u) =
      PhysicalLocalEnergy.form (fun _ => 0) C κ hκ M hb e v u := by
  have hk (i : I) :
      ⟪covariant I (fun _ => 0) C κ' hκ' M hb' e i (shiftReference c v),
        covariant I (fun _ => 0) C κ' hκ' M hb' e i (shiftReference c u)⟫_ℂ =
      ⟪covariant I (fun _ => 0) C κ hκ M hb e i v,
        covariant I (fun _ => 0) C κ hκ M hb e i u⟫_ℂ :=
    (congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
      (covariant_shift c C κ κ' hκ hκ' M hb hb' hshift e v i)
      (covariant_shift c C κ κ' hκ hκ' M hb hb' hshift e u i)).trans
        (inner_shift c _ _)
  have hr := (congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
    (radiation_shift c v) (radiation_shift c u)).trans (inner_shift c _ _)
  have hp := (congrArg₂ (fun a b : WaveSpace I => ⟪a, b⟫_ℂ)
    (potential_transport c v) (potential_transport c u)).trans (inner_shift c _ _)
  exact congrArg₂ (fun a b : ℂ => a + b)
    (congrArg₂ (fun a b : ℂ => a + b)
      (congrArg (fun z : ℂ => (1 / 2 : ℂ) * z)
        (Finset.sum_congr rfl fun i _ => hk i)) hr) hp

include hshift in
/-- The actual free form-realized graph transports to the translated
profile. Arbitrary test vectors are pulled back by the inverse shift. -/
theorem operatorPair_shift (e : ℝ) {u : Reference I (fun _ => 0)} {f : WaveSpace I}
    (hu : IsOperatorPair (fun _ => 0) C κ hκ M hb e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      u (zeroExternalDomain (fun _ => 0) u) f) :
    IsOperatorPair (fun _ => 0) C κ' hκ' M hb' e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      (shiftReference c u) (zeroExternalDomain (fun _ => 0) (shiftReference c u)) (shiftL2 c f) := by
  apply (isOperatorPair_zero_iff (fun _ => 0) C κ' hκ' M hb' e _ _).mpr
  have h := (isOperatorPair_zero_iff (fun _ => 0) C κ hκ M hb e u f).mp hu
  intro v
  let w := shiftReference (-c) v
  have hv : shiftReference c w = v := shiftReference_neg_right c v
  have he := (congrArg (fun z : Reference I (fun _ => 0) =>
    PhysicalLocalEnergy.form (fun _ => 0) C κ' hκ' M hb' e z (shiftReference c u)) hv).symm
  have hform := he.trans ((form_shift c C κ κ' hκ hκ' M hb hb' hshift e w u).trans (h w))
  have hi : shiftL2 c (inclusion I (fun _ => 0) w) = inclusion I (fun _ => 0) v :=
    (inclusion_shift c w).symm.trans (congrArg (inclusion I (fun _ => 0)) hv)
  exact hform.trans ((inner_shift c (inclusion I (fun _ => 0) w) f).symm.trans
    (congrArg (fun z : WaveSpace I => ⟪z, shiftL2 c f⟫_ℂ) hi))

/-- Explicit two-profile specialization. No covariance of the original
profile under translations is required. -/
theorem operatorPair_shiftedProfile (e : ℝ)
    {u : Reference I (fun _ => 0)} {f : WaveSpace I}
    (hu : IsOperatorPair (fun _ => 0) C κ hκ M hb e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      u (zeroExternalDomain (fun _ => 0) u) f) :
    IsOperatorPair (fun _ => 0) C (shiftedProfile c κ) (shifted_measurable c κ hκ)
      M (shifted_bound c κ M hb) e
      (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      (shiftReference c u) (zeroExternalDomain (fun _ => 0) (shiftReference c u)) (shiftL2 c f) :=
  operatorPair_shift c C κ (shiftedProfile c κ) hκ (shifted_measurable c κ hκ)
    M hb (shifted_bound c κ M hb) (fun _ => Filter.Eventually.of_forall fun _ => rfl) e hu

end PfHk.PhysicalElectronicShift
