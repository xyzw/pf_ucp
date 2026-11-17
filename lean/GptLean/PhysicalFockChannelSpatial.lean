import GptLean.PhysicalFockChannelKernel
import GptLean.PhysicalFockKrausL2

/-!
The constructed channel field and vacuum correction act pointwise in the
electronic variable. Their L2 outputs use the same Kraus coordinates as
the physical electronic channel. The field decomposition and vacuum
orthogonality are therefore identities on that common model.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

private def channelSequenceIdentity : Space (fun _ : ℕ => PhotonFock) →ₗᵢ[ℂ]
    Space (fun _ : ℕ => PhotonFock) := LinearIsometry.id

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
  (κ : X → ChannelKernel j) (hκ : AEStronglyMeasurable κ μ)
  (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)

private def channelFieldSpatialOutput : SpatialRadiationGraph μ →L[ℂ]
    Lp (Space (fun _ : ℕ => PhotonFock)) 2 μ :=
  spatialOperator μ (fun x => channelKernelField j BF C (κ x))
    ((channelKernelFieldMap j BF C).continuous.comp_aestronglyMeasurable hκ)
    ((2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * M)
    (by
      filter_upwards [hb] with x hx
      exact (channelKernelField_opNorm_le j BF C (κ x)).trans (by gcongr))

private def channelVacuumSpatialOutput : SpatialRadiationGraph μ →L[ℂ]
    Lp (Space (fun _ : ℕ => PhotonFock)) 2 μ :=
  spatialOperator μ (fun x => channelKernelVacuum j BF C (κ x))
    ((channelKernelVacuumMap j BF C).continuous.comp_aestronglyMeasurable hκ)
    (‖radiationGraphInclusion‖ * M)
    (by
      filter_upwards [hb] with x hx
      exact (channelKernelVacuum_opNorm_le j BF C (κ x)).trans (by gcongr))

def spatialChannelField : SpatialRadiationGraph μ →L[ℂ]
    Space (fun _ : ℕ => SpatialPhotonSpace μ) :=
  (KrausL2.lift μ channelSequenceIdentity).toContinuousLinearMap.comp
    (channelFieldSpatialOutput μ BF C j κ hκ M hb)

def spatialChannelVacuum : SpatialRadiationGraph μ →L[ℂ]
    Space (fun _ : ℕ => SpatialPhotonSpace μ) :=
  (KrausL2.lift μ channelSequenceIdentity).toContinuousLinearMap.comp
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb)

theorem spatialChannelField_ae (u : SpatialRadiationGraph μ) (a : ℕ) :
    spatialChannelField μ BF C j κ hκ M hb u a =ᵐ[μ]
      fun x => channelKernelField j BF C (κ x) (u x) a := by
  have h₁ := KrausL2.lift_coordinate_ae μ
    channelSequenceIdentity
    (channelFieldSpatialOutput μ BF C j κ hκ M hb u) a
  have h₂ : channelFieldSpatialOutput μ BF C j κ hκ M hb u =ᵐ[μ]
      fun x => channelKernelField j BF C (κ x) (u x) := spatialOperator_ae μ _ _ _ _ u
  filter_upwards [h₁, h₂] with x hx hy
  exact hx.trans (congrArg (fun z : Space (fun _ : ℕ => PhotonFock) => z a) hy)

theorem spatialChannelVacuum_ae (u : SpatialRadiationGraph μ) (a : ℕ) :
    spatialChannelVacuum μ BF C j κ hκ M hb u a =ᵐ[μ]
      fun x => channelKernelVacuum j BF C (κ x) (u x) a := by
  have h₁ := KrausL2.lift_coordinate_ae μ
    channelSequenceIdentity
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u) a
  have h₂ : channelVacuumSpatialOutput μ BF C j κ hκ M hb u =ᵐ[μ]
      fun x => channelKernelVacuum j BF C (κ x) (u x) := spatialOperator_ae μ _ _ _ _ u
  filter_upwards [h₁, h₂] with x hx hy
  exact hx.trans (congrArg (fun z : Space (fun _ : ℕ => PhotonFock) => z a) hy)

include hκ in
private theorem retainedProfile_measurable :
    AEStronglyMeasurable (fun x => (κ x).val.2) μ :=
  (continuous_snd.comp continuous_subtype_val).comp_aestronglyMeasurable hκ

include hb in
private theorem retainedProfile_bound : ∀ᵐ x ∂μ, ‖(κ x).val.2‖ ≤ M := by
  filter_upwards [hb] with x hx
  exact (norm_snd_le (κ x).val).trans hx

/-- The retained graph field is the channel image of the pulled-back field
plus its constructed complementary vacuum correction. -/
theorem spatialChannelField_decomposition (u : SpatialRadiationGraph μ) :
    spatialChannelField μ BF C j κ hκ M hb u =
      KrausL2.lift μ ((photonFactorization BF).factor j)
        (spatialField μ C (fun x => (κ x).val.2) (retainedProfile_measurable μ j κ hκ)
          M (retainedProfile_bound μ j κ M hb) u) +
      spatialChannelVacuum μ BF C j κ hκ M hb u := by
  apply lp.ext
  funext a
  apply Lp.ext
  let w := spatialField μ C (fun x => (κ x).val.2) (retainedProfile_measurable μ j κ hκ)
    M (retainedProfile_bound μ j κ M hb) u
  have hw : w =ᵐ[μ] fun x => kernelField C (κ x).val.2 (u x) :=
    spatialField_ae μ C _ _ _ _ u
  filter_upwards [spatialChannelField_ae μ BF C j κ hκ M hb u a,
    spatialChannelVacuum_ae μ BF C j κ hκ M hb u a,
    KrausL2.lift_coordinate_ae μ ((photonFactorization BF).factor j) w a, hw,
    Lp.coeFn_add (KrausL2.lift μ ((photonFactorization BF).factor j) w a)
      (spatialChannelVacuum μ BF C j κ hκ M hb u a)] with x hf hv hu hw ha
  change spatialChannelField μ BF C j κ hκ M hb u a x =
    (KrausL2.lift μ ((photonFactorization BF).factor j) w a +
      spatialChannelVacuum μ BF C j κ hκ M hb u a) x
  have hpoint := congrArg (fun z : Space (fun _ : ℕ => PhotonFock) => z a)
    (channelField_eq_factor_add_vacuum BF C j (κ x).val.1 (κ x).val.2 (κ x).property (u x))
  have hup := hu.trans (congrArg
    (fun v : PhotonFock => (photonFactorization BF).factor j v a) hw)
  exact hf.trans (hpoint.trans ((congrArg₂ (fun v w : PhotonFock => v + w)
    hup.symm hv.symm).trans ha.symm))

private theorem lifted_pointwise (v : SpatialPhotonSpace μ) :
    (((photonFactorization BF).factor j).toContinuousLinearMap.compLpL 2 μ v) =ᵐ[μ]
      fun x => (photonFactorization BF).factor j (v x) :=
  ((photonFactorization BF).factor j).toContinuousLinearMap.coeFn_compLpL v

private theorem lift_pointwise_eq (v : SpatialPhotonSpace μ) :
    KrausL2.lift μ channelSequenceIdentity
      (((photonFactorization BF).factor j).toContinuousLinearMap.compLpL 2 μ v) =
        KrausL2.lift μ ((photonFactorization BF).factor j) v := by
  apply lp.ext
  funext a
  apply Lp.ext
  filter_upwards [KrausL2.lift_coordinate_ae μ
      channelSequenceIdentity
      (((photonFactorization BF).factor j).toContinuousLinearMap.compLpL 2 μ v) a,
    lifted_pointwise μ BF j v,
    KrausL2.lift_coordinate_ae μ ((photonFactorization BF).factor j) v a] with x hl hp hr
  exact hl.trans ((congrArg (fun z : Space (fun _ : ℕ => PhotonFock) => z a) hp).trans hr.symm)

/-- The vacuum correction is orthogonal to the complete electronic channel range. -/
theorem spatialChannelVacuum_orthogonal (u : SpatialRadiationGraph μ) (v : SpatialPhotonSpace μ) :
    ⟪KrausL2.lift μ ((photonFactorization BF).factor j) v,
      spatialChannelVacuum μ BF C j κ hκ M hb u⟫_ℂ = 0 := by
  have he := congrArg (fun z : Space (fun _ : ℕ => SpatialPhotonSpace μ) =>
    ⟪z, spatialChannelVacuum μ BF C j κ hκ M hb u⟫_ℂ) (lift_pointwise_eq μ BF j v)
  have hinner := (KrausL2.lift μ channelSequenceIdentity).inner_map_map
    (((photonFactorization BF).factor j).toContinuousLinearMap.compLpL 2 μ v)
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u)
  apply he.symm.trans (hinner.trans ?_)
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hv : channelVacuumSpatialOutput μ BF C j κ hκ M hb u =ᵐ[μ]
      fun x => channelKernelVacuum j BF C (κ x) (u x) := spatialOperator_ae μ _ _ _ _ u
  filter_upwards [lifted_pointwise μ BF j v, hv] with x hx hy
  exact (congrArg₂ (fun z w : Space (fun _ : ℕ => PhotonFock) => ⟪z, w⟫_ℂ) hx hy).trans
    (channelVacuum_orthogonal_left BF C j (κ x).val.1 (κ x).val.2 (κ x).property (u x) (v x))

private theorem vacuum_loss_bound (p : ChannelKernel j) (ε : ℝ) (hε : 0 ≤ ε)
    (u : RadiationGraphSpace)
    (hloss : u ≠ 0 → ‖p.val.1‖ ^ 2 - ‖p.val.2.val.1‖ ^ 2 ≤ ε ^ 2) :
    ‖channelKernelVacuum j BF C p u‖ ≤ ε * ‖radiationGraphInclusion u‖ := by
  by_cases hu : u = 0
  · simpa only [hu, map_zero, norm_zero, mul_zero] using (le_refl (0 : ℝ))
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))).mp
    exact (channelVacuum_norm_sq BF C j p.val.1 p.val.2 p.property u).le.trans
      ((mul_le_mul_of_nonneg_right (hloss hu) (sq_nonneg ‖radiationGraphInclusion u‖)).trans_eq
        (mul_pow ε ‖radiationGraphInclusion u‖ 2).symm)

/-- A physical one-photon mass loss bound supplies the integrated vacuum
bound, with no photon-number or output-radiation hypothesis. -/
theorem spatialChannelVacuum_norm_le (ε : ℝ) (hε : 0 ≤ ε)
    (hloss : ∀ᵐ x ∂μ, ‖(κ x).val.1‖ ^ 2 - ‖(κ x).val.2.val.1‖ ^ 2 ≤ ε ^ 2)
    (u : SpatialRadiationGraph μ) :
    ‖spatialChannelVacuum μ BF C j κ hκ M hb u‖ ≤
      ε * ‖spatialRadiationInclusion μ u‖ := by
  change ‖KrausL2.lift μ channelSequenceIdentity
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u)‖ ≤ _
  refine ((KrausL2.lift μ channelSequenceIdentity).norm_map
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u)).le.trans ?_
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hv : channelVacuumSpatialOutput μ BF C j κ hκ M hb u =ᵐ[μ]
      fun x => channelKernelVacuum j BF C (κ x) (u x) := spatialOperator_ae μ _ _ _ _ u
  have hi : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  filter_upwards [hv, hi, hloss] with x hv hi hl
  exact (congrArg norm hv).le.trans
    ((vacuum_loss_bound BF C j (κ x) ε hε (u x) (fun _ => hl)).trans_eq
      (congrArg (fun w : PhotonFock => ε * ‖w‖) hi.symm))

/-- The mass-loss bound is only needed on the electronic support of the source. -/
theorem spatialChannelVacuum_supported_norm_le (ε : ℝ) (hε : 0 ≤ ε)
    (u : SpatialRadiationGraph μ)
    (hloss : ∀ᵐ x ∂μ, u x ≠ 0 →
      ‖(κ x).val.1‖ ^ 2 - ‖(κ x).val.2.val.1‖ ^ 2 ≤ ε ^ 2) :
    ‖spatialChannelVacuum μ BF C j κ hκ M hb u‖ ≤
      ε * ‖spatialRadiationInclusion μ u‖ := by
  change ‖KrausL2.lift μ channelSequenceIdentity
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u)‖ ≤ _
  refine ((KrausL2.lift μ channelSequenceIdentity).norm_map
    (channelVacuumSpatialOutput μ BF C j κ hκ M hb u)).le.trans ?_
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hv : channelVacuumSpatialOutput μ BF C j κ hκ M hb u =ᵐ[μ]
      fun x => channelKernelVacuum j BF C (κ x) (u x) := spatialOperator_ae μ _ _ _ _ u
  have hi : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  filter_upwards [hv, hi, hloss] with x hv hi hl
  exact (congrArg norm hv).le.trans
    ((vacuum_loss_bound BF C j (κ x) ε hε (u x) hl).trans_eq
      (congrArg (fun w : PhotonFock => ε * ‖w‖) hi.symm))

/-- Once the actual output radiation graph is constructed, the channel
field coordinate equals the physical spatial field on that graph. -/
theorem spatialChannelField_output
    (g : X → WeightedPhotonKernel) (hg : AEStronglyMeasurable g μ)
    (L : ℝ) (hL : ∀ᵐ x ∂μ, ‖g x‖ ≤ L)
    (hfull : ∀ᵐ x ∂μ, (g x).val.1 = (κ x).val.1)
    (u v : SpatialRadiationGraph μ) (a : ℕ)
    (hv : spatialRadiationInclusion μ v =
      KrausL2.lift μ ((photonFactorization BF).factor j) (spatialRadiationInclusion μ u) a) :
    spatialField μ C g hg L hL v = spatialChannelField μ BF C j κ hκ M hb u a := by
  apply Lp.ext
  have hi : spatialRadiationInclusion μ u =ᵐ[μ]
      fun x => radiationGraphInclusion (u x) := radiationGraphInclusion.coeFn_compLpL u
  have ho : spatialRadiationInclusion μ v =ᵐ[μ]
      fun x => radiationGraphInclusion (v x) := radiationGraphInclusion.coeFn_compLpL v
  filter_upwards [spatialField_ae μ C g hg L hL v,
    spatialChannelField_ae μ BF C j κ hκ M hb u a, hfull, hi, ho,
    KrausL2.lift_coordinate_ae μ ((photonFactorization BF).factor j)
      (spatialRadiationInclusion μ u) a] with x hf hc hg hi ho hk
  have hvalue := congrArg (fun w : SpatialPhotonSpace μ => w x) hv
  exact hf.trans ((channelField_output BF C j (κ x).val.1 (κ x).val.2 (κ x).property (g x) hg
    (u x) (v x) a (ho.symm.trans (hvalue.trans (hk.trans
      (congrArg (fun w : PhotonFock => (photonFactorization BF).factor j w a) hi))))).trans hc.symm)

end GptLean.PhysicalFock
