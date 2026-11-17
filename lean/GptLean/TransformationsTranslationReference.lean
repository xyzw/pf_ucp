import GptLean.TransformationsAffine
import GptLean.TransformationsFockPointwise
import GptLean.ElectronicH1Map
import GptLean.PhysicalPFReference

/-!
Translations on the actual common Pauli--Fierz reference domain.

For a configuration-space vector `c` and a pointwise one-photon unitary `U`
preserving the photon dispersion, the map

`(T Ψ)(x) = Γ(U) Ψ(x + c)`

acts on all three graph coordinates of the reference domain: the electronic
H1 graph by the affine pullback and the fibre Fock map, the spatial radiation
graph by the induced radiation-graph map, and the Coulomb multiplication graph
when the potential is invariant. It commutes with the ordinary derivatives and
with the radiation and Coulomb square roots. If the field kernels obey the
covariance `κ i x = U κ i (x + c)`, it also commutes with the spatial field,
hence with the covariant derivatives, and preserves the Pauli--Fierz energy.
With `c` the diagonal shift by `-b` and `U` the photon translation `t_b`, this
is `prop-translation-covariance`.
-/

noncomputable section

namespace GptLean.TransformationsTranslation

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsAffine TransformationsFock
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

section Lp

variable {I : Type} [Fintype I] [DecidableEq I] (c : EuclideanSpace ℝ I)
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- Pullback by the translation `x ↦ x + c` on vector-valued L². -/
def shiftL2 : Lp F 2 (volume : Measure (EuclideanSpace ℝ I)) →ₗᵢ[ℂ]
    Lp F 2 (volume : Measure (EuclideanSpace ℝ I)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + c) (measurePreserving_add_right volume c)

theorem shiftL2_ae (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    shiftL2 c v =ᵐ[volume] fun x => v (x + c) :=
  Lp.coeFn_compMeasurePreserving v (measurePreserving_add_right volume c)

theorem ae_shift {P : EuclideanSpace ℝ I → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ I)), P (x + c) :=
  (measurePreserving_add_right volume c).quasiMeasurePreserving.ae h

theorem shiftL2_compLpL (L : F →L[ℂ] F') (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    shiftL2 c (L.compLpL 2 volume v) = L.compLpL 2 volume (shiftL2 c v) := by
  apply Lp.ext
  filter_upwards [shiftL2_ae c (L.compLpL 2 volume v), ae_shift c (L.coeFn_compLpL v),
    L.coeFn_compLpL (shiftL2 c v), shiftL2_ae c v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

theorem shiftL2_neg (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    shiftL2 (-c) (shiftL2 c v) = v := by
  apply Lp.ext
  filter_upwards [shiftL2_ae (-c) (shiftL2 c v), ae_shift (-c) (shiftL2_ae c v)] with x h₁ h₂
  rw [h₁, h₂, neg_add_cancel_right]

theorem pull_eq_shiftL2 [NormedSpace ℝ F] [CompleteSpace F]
    (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    (AffineIsometry.translation c).pull ℂ v = shiftL2 c v := by
  apply Lp.ext
  filter_upwards [(AffineIsometry.translation c).pull_ae ℂ v, shiftL2_ae c v] with x h₁ h₂
  rw [h₁, h₂]
  rfl

end Lp

variable {I : Type} [Fintype I] [DecidableEq I] (c : EuclideanSpace ℝ I)
  (U : PointwiseUnitary photonMeasure) (hU : ∀ p, ‖(U.map p).1‖ = ‖p.1‖)

/-- The fibre Fock map `Γ(U)`. -/
def fockCLM : PhotonFock →L[ℂ] PhotonFock := (fockMap U).toLinearIsometry.toContinuousLinearMap

/-- The induced map of the radiation graph. -/
def radiationCLM : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  (radiationGraphMap U hU).toLinearIsometry.toContinuousLinearMap

theorem radiationGraphInclusion_comp :
    radiationGraphInclusion.comp (radiationCLM U hU) = (fockCLM U).comp radiationGraphInclusion :=
  ContinuousLinearMap.ext fun q => radiationGraphInclusion_map U hU q

theorem radiationGraphDerivative_comp :
    radiationGraphDerivative.comp (radiationCLM U hU) =
      (fockCLM U).comp radiationGraphDerivative :=
  ContinuousLinearMap.ext fun q => radiationGraphDerivative_map U hU q

/-- `(T v)(x) = Γ(U) v(x + c)` on the physical wave space. -/
def waveMap (v : WaveSpace I) : WaveSpace I := shiftL2 c ((fockCLM U).compLpL 2 volume v)

theorem waveMap_ae (v : WaveSpace I) :
    waveMap c U v =ᵐ[volume] fun x => fockMap U (v (x + c)) := by
  unfold waveMap
  filter_upwards [shiftL2_ae c ((fockCLM U).compLpL 2 volume v),
    ae_shift c ((fockCLM U).coeFn_compLpL v)] with x h₁ h₂
  exact h₁.trans h₂

theorem waveMap_add (v w : WaveSpace I) :
    waveMap c U (v + w) = waveMap c U v + waveMap c U w :=
  (congrArg (shiftL2 c) (map_add ((fockCLM U).compLpL 2 volume) v w)).trans
    (map_add (shiftL2 c) _ _)

theorem waveMap_smul (a : ℂ) (v : WaveSpace I) : waveMap c U (a • v) = a • waveMap c U v :=
  (congrArg (shiftL2 c) (map_smul ((fockCLM U).compLpL 2 volume) a v)).trans
    (map_smul (shiftL2 c) a _)

theorem waveMap_sub (v w : WaveSpace I) :
    waveMap c U (v - w) = waveMap c U v - waveMap c U w :=
  (congrArg (shiftL2 c) (map_sub ((fockCLM U).compLpL 2 volume) v w)).trans
    (map_sub (shiftL2 c) _ _)

theorem norm_fockCompLpL (v : WaveSpace I) : ‖(fockCLM U).compLpL 2 volume v‖ = ‖v‖ := by
  have h : eLpNorm ((fockCLM U).compLpL 2 volume v) 2 volume = eLpNorm v 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [(fockCLM U).coeFn_compLpL v] with x hx
    exact (congrArg norm hx).trans ((fockMap U).norm_map (v x))
  exact congrArg ENNReal.toReal h

theorem norm_waveMap (v : WaveSpace I) : ‖waveMap c U v‖ = ‖v‖ :=
  ((shiftL2 c).norm_map _).trans (norm_fockCompLpL U v)

theorem sectorMap_symm_eq (n : ℕ) (f : FullSector photonMeasure n) :
    sectorMap U.symm n f = (sectorMap U n).symm f := by
  apply (sectorMap U n).injective
  refine Eq.trans ?_ ((sectorMap U n).apply_symm_apply f).symm
  apply Lp.ext
  filter_upwards [sectorMap_ae U n (sectorMap U.symm n f),
    (U.power n).preserving.quasiMeasurePreserving.ae (sectorMap_ae U.symm n f)] with k h₁ h₂
  have hk : (U.power n).map k = fun i => U.map (k i) := rfl
  rw [hk] at h₂
  refine h₁.trans ?_
  rw [h₂]
  simp only [PointwiseUnitary.symm_weight, PointwiseUnitary.symm_map_apply,
    MeasurableEquiv.symm_apply_apply]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp only [mul_inv_cancel₀ (U.weight_ne_zero _), Finset.prod_const_one, one_mul]

theorem fockMap_symm_eq (u : PhotonFock) : fockMap U.symm u = (fockMap U).symm u := by
  apply lp.ext
  funext n
  exact Subtype.ext (sectorMap_symm_eq U n (u n).val)

/-- The opposite translation with the inverse photon map inverts `waveMap`. -/
theorem waveMap_neg (v : WaveSpace I) : waveMap (-c) U.symm (waveMap c U v) = v := by
  apply Lp.ext
  filter_upwards [waveMap_ae (-c) U.symm (waveMap c U v), ae_shift (-c) (waveMap_ae c U v)]
    with x h₁ h₂
  refine h₁.trans ((congrArg (fockMap U.symm) h₂).trans ?_)
  have hx : x + -c + c = x := neg_add_cancel_right x c
  exact (congrArg (fun y => fockMap U.symm (fockMap U (v y))) hx).trans
    ((fockMap_symm_eq U _).trans ((fockMap U).symm_apply_apply (v x)))

/-! ### The three graph coordinates -/

/-- The electronic graph map `w ↦ (Γ(U) w)(· + c)`. -/
def electronicMap (w : ElectronicGraph I) : ElectronicGraph I :=
  (AffineIsometry.translation c).pullH1 (ElectronicH1Map.map (fockCLM U) w)

theorem value_electronicMap (w : ElectronicGraph I) :
    ElectronicH1Complex.value (electronicMap c U w) =
      waveMap c U (ElectronicH1Complex.value w) :=
  pull_eq_shiftL2 c ((fockCLM U).compLpL 2 volume (ElectronicH1Complex.value w))

theorem derivative_electronicMap (i : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative i (electronicMap c U w) =
      waveMap c U (ElectronicH1Complex.derivative i w) :=
  (congrArg ((AffineIsometry.translation c).pull ℂ)
    (AffineIsometry.translation_sum c i fun j =>
      ElectronicH1Complex.derivative j (ElectronicH1Map.map (fockCLM U) w))).trans
    (pull_eq_shiftL2 c ((fockCLM U).compLpL 2 volume (ElectronicH1Complex.derivative i w)))

/-- The radiation-graph map `r ↦ (Γ(U) r)(· + c)`. -/
def radiationMap (r : RadiationGraph I) : RadiationGraph I :=
  shiftL2 c ((radiationCLM U hU).compLpL 2 volume r)

theorem inclusion_radiationMap (r : RadiationGraph I) :
    spatialRadiationInclusion volume (radiationMap c U hU r) =
      waveMap c U (spatialRadiationInclusion volume r) :=
  ((shiftL2_compLpL c radiationGraphInclusion ((radiationCLM U hU).compLpL 2 volume r)).symm.trans
    (congrArg (shiftL2 c) ((ElectronicH1Map.compLpL_comp radiationGraphInclusion
      (radiationCLM U hU) r).trans ((congrArg (fun L => L.compLpL 2 volume r)
        (radiationGraphInclusion_comp U hU)).trans
          (ElectronicH1Map.compLpL_comp (fockCLM U) radiationGraphInclusion r).symm))))

theorem derivative_radiationMap (r : RadiationGraph I) :
    spatialRadiationDerivative volume (radiationMap c U hU r) =
      waveMap c U (spatialRadiationDerivative volume r) :=
  ((shiftL2_compLpL c radiationGraphDerivative ((radiationCLM U hU).compLpL 2 volume r)).symm.trans
    (congrArg (shiftL2 c) ((ElectronicH1Map.compLpL_comp radiationGraphDerivative
      (radiationCLM U hU) r).trans ((congrArg (fun L => L.compLpL 2 volume r)
        (radiationGraphDerivative_comp U hU)).trans
          (ElectronicH1Map.compLpL_comp (fockCLM U) radiationGraphDerivative r).symm))))

theorem radiationMap_ae (r : RadiationGraph I) :
    radiationMap c U hU r =ᵐ[volume] fun x => radiationGraphMap U hU (r (x + c)) := by
  unfold radiationMap
  filter_upwards [shiftL2_ae c ((radiationCLM U hU).compLpL 2 volume r),
    ae_shift c ((radiationCLM U hU).coeFn_compLpL r)] with x h₁ h₂
  exact h₁.trans h₂

variable (V : Position I → ℝ) (hV : ∀ x, V (x + c) = V x)

include hV in
theorem potentialMap_mem (p : PotentialGraph I V) :
    ((waveMap c U p.val.1, waveMap c U p.val.2) : WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun x => (Real.sqrt (V x) : ℂ)) := by
  have hp : ∀ᵐ x ∂volume, p.val.2 x = (Real.sqrt (V x) : ℂ) • p.val.1 x := p.property
  change ∀ᵐ x ∂volume, waveMap c U p.val.2 x = (Real.sqrt (V x) : ℂ) • waveMap c U p.val.1 x
  filter_upwards [ae_shift c hp, waveMap_ae c U p.val.1, waveMap_ae c U p.val.2]
    with x hx h₁ h₂
  refine h₂.trans ((congrArg (fockMap U) hx).trans ((map_smul (fockMap U) _ _).trans ?_))
  refine (congrArg (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) • fockMap U (p.val.1 (x + c))) (hV x)).trans ?_
  exact congrArg (fun z : PhotonFock => (Real.sqrt (V x) : ℂ) • z) h₁.symm

/-- The Coulomb-graph map. -/
def potentialMap (p : PotentialGraph I V) : PotentialGraph I V :=
  ⟨(waveMap c U p.val.1, waveMap c U p.val.2), potentialMap_mem c U V hV p⟩

/-- The translation on the common reference domain. -/
def translate (u : Reference I V) : Reference I V :=
  ⟨(electronicMap c U (electronic I V u), radiationMap c U hU (radiationSource I V u),
      potentialMap c U V hV (potentialSource I V u)), by
    change (ElectronicH1Complex.value (electronicMap c U (electronic I V u)) -
        spatialRadiationInclusion volume (radiationMap c U hU (radiationSource I V u)),
      ElectronicH1Complex.value (electronicMap c U (electronic I V u)) -
        waveMap c U (potentialSource I V u).val.1) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((value_electronicMap c U (electronic I V u)).trans
        ((congrArg (waveMap c U) (radiation_matches I V u).symm).trans
          (inclusion_radiationMap c U hU (radiationSource I V u)).symm))
    · exact sub_eq_zero.mpr ((value_electronicMap c U (electronic I V u)).trans
        (congrArg (waveMap c U) (potential_matches I V u).symm))⟩

theorem inclusion_translate (u : Reference I V) :
    inclusion I V (translate c U hU V hV u) = waveMap c U (inclusion I V u) :=
  value_electronicMap c U (electronic I V u)

theorem ordinary_translate (i : I) (u : Reference I V) :
    ordinary I V i (translate c U hU V hV u) = waveMap c U (ordinary I V i u) :=
  derivative_electronicMap c U i (electronic I V u)

theorem radiation_translate (u : Reference I V) :
    radiation I V (translate c U hU V hV u) = waveMap c U (radiation I V u) :=
  derivative_radiationMap c U hU (radiationSource I V u)

theorem potential_translate (u : Reference I V) :
    potential I V (translate c U hU V hV u) = waveMap c U (potential I V u) := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hcov : ∀ i, ∀ᵐ x ∂volume, κ i x = kernelMap U hU (κ i (x + c)))

include hcov in
/-- Covariant field kernels make the translation commute with the field. -/
theorem field_translate (i : I) (u : Reference I V) :
    field I V C κ hκ M hbound i (translate c U hU V hV u) =
      waveMap c U (field I V C κ hκ M hbound i u) := by
  apply Lp.ext
  have hf := spatialField_ae volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u)
  filter_upwards [spatialField_ae volume C (κ i) (hκ i) M (hbound i)
      (radiationMap c U hU (radiationSource I V u)),
    radiationMap_ae c U hU (radiationSource I V u), hcov i,
    waveMap_ae c U (field I V C κ hκ M hbound i u), ae_shift c hf] with x h₁ h₂ h₃ h₄ h₅
  change spatialField volume C (κ i) (hκ i) M (hbound i)
      (radiationMap c U hU (radiationSource I V u)) x = _
  refine h₁.trans ((congrArg₂ (fun k q => kernelField C k q) h₃ h₂).trans
    ((kernelField_map U hU C _ _).trans ?_))
  refine (congrArg (fockMap U) h₅.symm).trans ?_
  exact h₄.symm

include hcov in
theorem covariant_translate (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i (translate c U hU V hV u) =
      waveMap c U (covariant I V C κ hκ M hbound e i u) :=
  (covariant_apply I V C κ hκ M hbound e i (translate c U hU V hV u)).trans
    ((congrArg₂ (fun a b : WaveSpace I => (-Complex.I) • a - (e : ℂ) • b)
      (ordinary_translate c U hU V hV i u)
      (field_translate c U hU V hV C κ hκ M hbound hcov i u)).trans
      ((congrArg₂ (· - ·) (waveMap_smul c U (-Complex.I) (ordinary I V i u)).symm
        (waveMap_smul c U (e : ℂ) (field I V C κ hκ M hbound i u)).symm).trans
        ((waveMap_sub c U _ _).symm.trans
          (congrArg (waveMap c U) (covariant_apply I V C κ hκ M hbound e i u).symm))))

include hcov in
/-- Translation covariance preserves the Pauli--Fierz energy. -/
theorem energy_translate (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (translate c U hU V hV u) =
      energy I V C κ hκ M hbound e u := by
  have hk (i : I) : ‖covariant I V C κ hκ M hbound e i (translate c U hU V hV u)‖ =
      ‖covariant I V C κ hκ M hbound e i u‖ :=
    (congrArg norm (covariant_translate c U hU V hV C κ hκ M hbound hcov e i u)).trans
      (norm_waveMap c U _)
  have hr : ‖radiation I V (translate c U hU V hV u)‖ = ‖radiation I V u‖ :=
    (congrArg norm (radiation_translate c U hU V hV u)).trans (norm_waveMap c U _)
  have hp : ‖potential I V (translate c U hU V hV u)‖ = ‖potential I V u‖ :=
    norm_waveMap c U _
  unfold energy kineticEnergy
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun i _ =>
      congrArg (· ^ 2) (hk i))) (congrArg (· ^ 2) hr)) (congrArg (· ^ 2) hp)

end GptLean.TransformationsTranslation
