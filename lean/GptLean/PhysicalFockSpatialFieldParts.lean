import GptLean.PhysicalFockSpatialField

/-!
The actual annihilation and creation parts of the spatial field.
Continuous dependence on weighted kernels gives their L2 realizations,
and the sector CCR supplies the integrated creation estimate.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

theorem kernelAnnihilation_opNorm_le (k : WeightedPhotonKernel) :
    ‖kernelAnnihilation k‖ ≤ ‖radiationGraphDerivative‖ * ‖k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    _ ≤ ‖k.val.2‖ * ‖radiationGraphDerivative u‖ :=
      annihilationRadiation_norm_le k.val.1 k.val.2 k.property u
    _ ≤ ‖k‖ * (‖radiationGraphDerivative‖ * ‖u‖) := by
      gcongr
      · exact norm_snd_le k.val
      · exact radiationGraphDerivative.le_opNorm u
    _ = _ := by ring

def kernelAnnihilationMap : WeightedPhotonKernel →L[ℝ]
    (RadiationGraphSpace →L[ℂ] PhotonFock) :=
  LinearMap.mkContinuous
    { toFun := kernelAnnihilation
      map_add' := kernelAnnihilation_add
      map_smul' c k := by
        simpa only [RingHom.id_apply] using kernelAnnihilation_real_smul c k }
    ‖radiationGraphDerivative‖ kernelAnnihilation_opNorm_le

theorem kernelCreation_opNorm_le (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel) :
    ‖kernelCreation C k‖ ≤ (‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * ‖k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    _ ≤ ‖k.val.2‖ * ‖radiationGraphDerivative u‖ + ‖k.val.1‖ * ‖radiationGraphInclusion u‖ :=
      creationGraphOutput_norm_le C k.val.1 k.val.2 k.property u
    _ ≤ ‖k‖ * (‖radiationGraphDerivative‖ * ‖u‖) +
        ‖k‖ * (‖radiationGraphInclusion‖ * ‖u‖) := by
      gcongr
      · exact norm_snd_le k.val
      · exact radiationGraphDerivative.le_opNorm u
      · exact norm_fst_le k.val
      · exact radiationGraphInclusion.le_opNorm u
    _ = _ := by ring

def kernelCreationMap (C : CanonicalSectorCCR photonMeasure) : WeightedPhotonKernel →L[ℝ]
    (RadiationGraphSpace →L[ℂ] PhotonFock) :=
  LinearMap.mkContinuous
    { toFun := kernelCreation C
      map_add' := kernelCreation_add C
      map_smul' c k := by
        simpa only [RingHom.id_apply] using kernelCreation_real_smul C c k }
    (‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) (kernelCreation_opNorm_le C)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure) (κ : X → WeightedPhotonKernel)
  (hκ : AEStronglyMeasurable κ μ) (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)

def spatialAnnihilation : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ :=
  spatialOperator μ (fun x => kernelAnnihilation (κ x))
    (kernelAnnihilationMap.continuous.comp_aestronglyMeasurable hκ)
    (‖radiationGraphDerivative‖ * M) (by
      filter_upwards [hb] with x hx
      exact (kernelAnnihilation_opNorm_le (κ x)).trans (by gcongr))

def spatialCreation : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ :=
  spatialOperator μ (fun x => kernelCreation C (κ x))
    ((kernelCreationMap C).continuous.comp_aestronglyMeasurable hκ)
    ((‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * M) (by
      filter_upwards [hb] with x hx
      exact (kernelCreation_opNorm_le C (κ x)).trans (by gcongr))

theorem spatialAnnihilation_ae (u : SpatialRadiationGraph μ) :
    spatialAnnihilation μ κ hκ M hb u =ᵐ[μ] fun x => kernelAnnihilation (κ x) (u x) :=
  spatialOperator_ae μ _ _ _ _ u

theorem spatialCreation_ae (u : SpatialRadiationGraph μ) :
    spatialCreation μ C κ hκ M hb u =ᵐ[μ] fun x => kernelCreation C (κ x) (u x) :=
  spatialOperator_ae μ _ _ _ _ u

attribute [irreducible] spatialAnnihilation spatialCreation

theorem spatialField_eq_parts :
    spatialField μ C κ hκ M hb = spatialAnnihilation μ κ hκ M hb + spatialCreation μ C κ hκ M hb := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [spatialField_ae μ C κ hκ M hb u, spatialAnnihilation_ae μ κ hκ M hb u,
    spatialCreation_ae μ C κ hκ M hb u,
    Lp.coeFn_add (spatialAnnihilation μ κ hκ M hb u) (spatialCreation μ C κ hκ M hb u)]
    with x hf ha hc hs
  exact hf.trans ((congrArg₂ (fun a c : PhotonFock => a + c) ha hc).symm.trans hs.symm)

theorem spatialAnnihilation_bound (A : ℝ)
    (hnegative : ∀ᵐ x ∂μ, ‖(κ x).val.2‖ ≤ A) (u : SpatialRadiationGraph μ) :
    ‖spatialAnnihilation μ κ hκ M hb u‖ ≤ A * ‖spatialRadiationDerivative μ u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hd : spatialRadiationDerivative μ u =ᵐ[μ]
      fun x => radiationGraphDerivative (u x) := radiationGraphDerivative.coeFn_compLpL u
  filter_upwards [spatialAnnihilation_ae μ κ hκ M hb u, hd, hnegative] with x ha hd hn
  exact (congrArg norm ha).le.trans
    (((annihilationRadiation_norm_le (κ x).val.1 (κ x).val.2 (κ x).property (u x)).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))).trans_eq
        (congrArg (fun v : PhotonFock => A * ‖v‖) hd.symm))

theorem spatialCreation_bound (B : ℝ) (_hB : 0 ≤ B)
    (hl2 : ∀ᵐ x ∂μ, ‖(κ x).val.1‖ ≤ B) (u : SpatialRadiationGraph μ) :
    ‖spatialCreation μ C κ hκ M hb u‖ ^ 2 ≤
      ‖spatialAnnihilation μ κ hκ M hb u‖ ^ 2 + B ^ 2 * ‖spatialRadiationInclusion μ u‖ ^ 2 := by
  let : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ PhotonFock
  have h := l2_square_bound μ (spatialCreation μ C κ hκ M hb u)
    (spatialAnnihilation μ κ hκ M hb u) (spatialRadiationInclusion μ u) 1 (B ^ 2)
  simp only [one_mul] at h
  apply h
  have hi : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  filter_upwards [spatialCreation_ae μ C κ hκ M hb u, spatialAnnihilation_ae μ κ hκ M hb u,
    hi, hl2] with x hc ha hi hk
  have he := creationRadiation_norm_sq C (κ x).val.1 (κ x).val.2 (κ x).property (u x)
  change ‖kernelCreation C (κ x) (u x)‖ ^ 2 =
    ‖kernelAnnihilation (κ x) (u x)‖ ^ 2 +
      ‖(κ x).val.1‖ ^ 2 * ‖radiationGraphInclusion (u x)‖ ^ 2 at he
  have hp := he.le.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hk 2) (sq_nonneg _)))
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hc).le.trans (hp.trans_eq
    (congrArg₂ (fun a v : PhotonFock => ‖a‖ ^ 2 + B ^ 2 * ‖v‖ ^ 2) ha.symm hi.symm))

/-- A compact kernel bound is needed only where the source graph vector is nonzero. -/
theorem spatialAnnihilation_supported_bound (A : ℝ) (u : SpatialRadiationGraph μ)
    (hnegative : ∀ᵐ x ∂μ, u x ≠ 0 → ‖(κ x).val.2‖ ≤ A) :
    ‖spatialAnnihilation μ κ hκ M hb u‖ ≤ A * ‖spatialRadiationDerivative μ u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hd : spatialRadiationDerivative μ u =ᵐ[μ]
      fun x => radiationGraphDerivative (u x) := radiationGraphDerivative.coeFn_compLpL u
  filter_upwards [spatialAnnihilation_ae μ κ hκ M hb u, hd, hnegative] with x ha hd hn
  have hpoint : ‖kernelAnnihilation (κ x) (u x)‖ ≤
      A * ‖radiationGraphDerivative (u x)‖ := by
    by_cases hu : u x = 0
    · simp only [hu, map_zero, norm_zero, mul_zero, le_refl]
    · exact (annihilationRadiation_norm_le (κ x).val.1 (κ x).val.2 (κ x).property (u x)).trans
        (mul_le_mul_of_nonneg_right (hn hu) (norm_nonneg _))
  exact (congrArg norm ha).le.trans (hpoint.trans_eq
    (congrArg (fun v : PhotonFock => A * ‖v‖) hd.symm))

theorem spatialCreation_supported_bound (B : ℝ) (u : SpatialRadiationGraph μ)
    (hl2 : ∀ᵐ x ∂μ, u x ≠ 0 → ‖(κ x).val.1‖ ≤ B) :
    ‖spatialCreation μ C κ hκ M hb u‖ ^ 2 ≤
      ‖spatialAnnihilation μ κ hκ M hb u‖ ^ 2 + B ^ 2 * ‖spatialRadiationInclusion μ u‖ ^ 2 := by
  let : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ PhotonFock
  have h := l2_square_bound μ (spatialCreation μ C κ hκ M hb u)
    (spatialAnnihilation μ κ hκ M hb u) (spatialRadiationInclusion μ u) 1 (B ^ 2)
  simp only [one_mul] at h
  apply h
  have hi : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  filter_upwards [spatialCreation_ae μ C κ hκ M hb u, spatialAnnihilation_ae μ κ hκ M hb u,
    hi, hl2] with x hc ha hi hk
  have hp : ‖kernelCreation C (κ x) (u x)‖ ^ 2 ≤
      ‖kernelAnnihilation (κ x) (u x)‖ ^ 2 +
        B ^ 2 * ‖radiationGraphInclusion (u x)‖ ^ 2 := by
    by_cases hu : u x = 0
    · simp only [hu, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, le_refl]
    · have he := creationRadiation_norm_sq C (κ x).val.1 (κ x).val.2 (κ x).property (u x)
      change ‖kernelCreation C (κ x) (u x)‖ ^ 2 =
        ‖kernelAnnihilation (κ x) (u x)‖ ^ 2 +
          ‖(κ x).val.1‖ ^ 2 * ‖radiationGraphInclusion (u x)‖ ^ 2 at he
      exact he.le.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hk hu) 2) (sq_nonneg _)))
  exact (congrArg (fun v : PhotonFock => ‖v‖ ^ 2) hc).le.trans (hp.trans_eq
    (congrArg₂ (fun a v : PhotonFock => ‖a‖ ^ 2 + B ^ 2 * ‖v‖ ^ 2) ha.symm hi.symm))

private theorem field_parts_bound {a c d v ε : ℝ}
    (ha0 : 0 ≤ a) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (hv0 : 0 ≤ v) (hε : 0 ≤ ε)
    (ha : a ≤ ε * d) (hc : c ^ 2 ≤ a ^ 2 + ε ^ 2 * v ^ 2) :
    a + c ≤ ε * (2 * d + v) := by
  have ha2 := pow_le_pow_left₀ ha0 ha 2
  have hcre : c ≤ ε * d + ε * v := by
    apply (sq_le_sq₀ hc0 (by positivity)).mp
    nlinarith only [hc, ha2, mul_nonneg (mul_nonneg hε hd0) (mul_nonneg hε hv0)]
  linarith

/-- The compact profile error controls the actual field on a supported
source through its radiation derivative and mass. -/
theorem spatialField_supported_norm_le (ε : ℝ) (hε : 0 ≤ ε) (u : SpatialRadiationGraph μ)
    (hnegative : ∀ᵐ x ∂μ, u x ≠ 0 → ‖(κ x).val.2‖ ≤ ε)
    (hl2 : ∀ᵐ x ∂μ, u x ≠ 0 → ‖(κ x).val.1‖ ≤ ε) :
    ‖spatialField μ C κ hκ M hb u‖ ≤
      ε * (2 * ‖spatialRadiationDerivative μ u‖ + ‖spatialRadiationInclusion μ u‖) := by
  have ha := spatialAnnihilation_supported_bound μ κ hκ M hb ε u hnegative
  have hc := spatialCreation_supported_bound μ C κ hκ M hb ε u hl2
  have he : spatialField μ C κ hκ M hb u =
      spatialAnnihilation μ κ hκ M hb u + spatialCreation μ C κ hκ M hb u :=
    congrArg (fun A : SpatialRadiationGraph μ →L[ℂ] SpatialPhotonSpace μ => A u)
      (spatialField_eq_parts μ C κ hκ M hb)
  exact (congrArg norm he).le.trans ((norm_add_le _ _).trans
    (field_parts_bound (norm_nonneg (spatialAnnihilation μ κ hκ M hb u))
      (norm_nonneg (spatialCreation μ C κ hκ M hb u))
      (norm_nonneg (spatialRadiationDerivative μ u))
      (norm_nonneg (spatialRadiationInclusion μ u)) hε ha hc))

end GptLean.PhysicalFock
