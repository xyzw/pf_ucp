import GptLean.PhysicalFockChannelSpatial
import GptLean.PhysicalFockSpatialFieldParts
import GptLean.ElectronicH1Map

/-!
Actual weak electronic derivatives commute with the bounded Kraus maps.
Combining that identity with the constructed spatial channel field gives
the covariant derivative identity on every source in the common H1 and
radiation domain. The noise has the sign dictated by D = -i partial - e A.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel ElectronicH1Complex
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

variable {I : Type} [Fintype I] [DecidableEq I]
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)
  (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
    WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

def channelH1 (a : ℕ) : ComplexH1 PhotonFock I →L[ℂ] ComplexH1 PhotonFock I :=
  ElectronicH1Map.map ((lp.evalCLM ℂ (fun _ : ℕ => PhotonFock) 2 a).comp
    ((photonFactorization BF).factor j).toContinuousLinearMap)

theorem channelH1_value (a : ℕ) (u : ComplexH1 PhotonFock I) :
    value (channelH1 BF j a u) =
      KrausL2.lift volume ((photonFactorization BF).factor j) (value u) a := rfl

theorem channelH1_derivative (a : ℕ) (u : ComplexH1 PhotonFock I) (i : I) :
    derivative i (channelH1 BF j a u) =
      KrausL2.lift volume ((photonFactorization BF).factor j) (derivative i u) a := rfl

variable (κ : EuclideanSpace ℝ I → ChannelKernel j) (hκ : AEStronglyMeasurable κ volume)
  (M : ℝ) (hb : ∀ᵐ x ∂volume, ‖κ x‖ ≤ M)
  (g t : EuclideanSpace ℝ I → WeightedPhotonKernel)
  (hg : AEStronglyMeasurable g volume) (ht : AEStronglyMeasurable t volume)
  (L K : ℝ) (hL : ∀ᵐ x ∂volume, ‖g x‖ ≤ L) (hK : ∀ᵐ x ∂volume, ‖t x‖ ≤ K)

omit [DecidableEq I] in
private theorem retainedField_eq_sub
    (hretained : ∀ᵐ x ∂volume, (κ x).val.2 = g x - t x)
    (u : SpatialRadiationGraph (volume : Measure (EuclideanSpace ℝ I)))
    (hkr : AEStronglyMeasurable (fun x => (κ x).val.2) volume)
    (hMr : ∀ᵐ x ∂volume, ‖(κ x).val.2‖ ≤ M) :
    spatialField volume C (fun x => (κ x).val.2) hkr M hMr u =
      spatialField volume C g hg L hL u - spatialField volume C t ht K hK u := by
  apply Lp.ext
  filter_upwards [spatialField_ae volume C _ hkr M hMr u,
    spatialField_ae volume C g hg L hL u, spatialField_ae volume C t ht K hK u,
    Lp.coeFn_sub (spatialField volume C g hg L hL u) (spatialField volume C t ht K hK u),
    hretained] with x hr hg ht hs hk
  have hfield := congrArg (fun k : WeightedPhotonKernel => kernelField C k (u x)) hk
  have hsub := congrArg (fun A : RadiationGraphSpace →L[ℂ] PhotonFock => A (u x))
    ((kernelFieldMap C).map_sub (g x) (t x))
  exact hr.trans (hfield.trans (hsub.trans
    ((congrArg₂ (fun a b : PhotonFock => a - b) hg ht).symm.trans hs.symm)))

omit [DecidableEq I] in
/-- The actual output field equals the channel image of the original
field minus the tail field, plus the complementary vacuum term. -/
theorem channelField_output_decomposition
    (hfull : ∀ᵐ x ∂volume, (g x).val.1 = (κ x).val.1)
    (hretained : ∀ᵐ x ∂volume, (κ x).val.2 = g x - t x)
    (u v : SpatialRadiationGraph (volume : Measure (EuclideanSpace ℝ I))) (a : ℕ)
    (hv : spatialRadiationInclusion volume v =
      KrausL2.lift volume ((photonFactorization BF).factor j)
        (spatialRadiationInclusion volume u) a) :
    spatialField volume C g hg L hL v =
      KrausL2.lift volume ((photonFactorization BF).factor j)
        (spatialField volume C g hg L hL u - spatialField volume C t ht K hK u) a +
        spatialChannelVacuum volume BF C j κ hκ M hb u a := by
  have hf := spatialChannelField_output volume BF C j κ hκ M hb g hg L hL hfull u v a hv
  have hkr : AEStronglyMeasurable (fun x => (κ x).val.2) volume :=
    (continuous_snd.comp continuous_subtype_val).comp_aestronglyMeasurable hκ
  have hMr : ∀ᵐ x ∂volume, ‖(κ x).val.2‖ ≤ M := by
    filter_upwards [hb] with x hx
    exact (norm_snd_le (κ x).val).trans hx
  have hd := congrArg
    (fun z : Space (fun _ : ℕ => SpatialPhotonSpace (volume : Measure (EuclideanSpace ℝ I))) => z a)
    (spatialChannelField_decomposition volume BF C j κ hκ M hb u)
  change spatialChannelField volume BF C j κ hκ M hb u a =
    KrausL2.lift volume ((photonFactorization BF).factor j)
      (spatialField volume C (fun x => (κ x).val.2) hkr M hMr u) a +
      spatialChannelVacuum volume BF C j κ hκ M hb u a at hd
  have hr := retainedField_eq_sub C j κ M g t hg ht L K hL hK hretained u hkr hMr
  exact hf.trans (hd.trans (congrArg
    (fun w : SpatialPhotonSpace (volume : Measure (EuclideanSpace ℝ I)) =>
      KrausL2.lift volume ((photonFactorization BF).factor j) w a +
        spatialChannelVacuum volume BF C j κ hκ M hb u a) hr))

private theorem covariant_algebra {H K : Type*}
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
    (U : H →ₗ[ℂ] K) (d f t : H) (v : K) (e : ℂ) :
    (-Complex.I) • U d - e • (U (f - t) + v) =
      U ((-Complex.I) • d - e • f + e • t) - e • v := by
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub]
  abel

/-- Full-domain covariant transport. Radiation sources are actual graph
vectors, and the ordinary derivative identity comes from weak H1. -/
theorem channel_covariant_identity
    (hfull : ∀ᵐ x ∂volume, (g x).val.1 = (κ x).val.1)
    (hretained : ∀ᵐ x ∂volume, (κ x).val.2 = g x - t x)
    (q : ComplexH1 PhotonFock I)
    (u v : SpatialRadiationGraph (volume : Measure (EuclideanSpace ℝ I)))
    (hu : spatialRadiationInclusion volume u = value q) (a : ℕ)
    (hv : spatialRadiationInclusion volume v = value (channelH1 BF j a q))
    (e : ℝ) (i : I) :
    (-Complex.I) • derivative i (channelH1 BF j a q) -
        (e : ℂ) • spatialField volume C g hg L hL v =
      KrausL2.lift volume ((photonFactorization BF).factor j)
        (((-Complex.I) • derivative i q - (e : ℂ) • spatialField volume C g hg L hL u) +
          (e : ℂ) • spatialField volume C t ht K hK u) a -
      (e : ℂ) • spatialChannelVacuum volume BF C j κ hκ M hb u a := by
  have hv' : spatialRadiationInclusion volume v =
      KrausL2.lift volume ((photonFactorization BF).factor j)
        (spatialRadiationInclusion volume u) a :=
    hv.trans ((channelH1_value BF j a q).trans (congrArg
      (fun w : SpatialPhotonSpace (volume : Measure (EuclideanSpace ℝ I)) =>
        KrausL2.lift volume ((photonFactorization BF).factor j) w a) hu.symm))
  have hd := channelH1_derivative BF j a q i
  have hf := channelField_output_decomposition BF C j κ hκ M hb
    g t hg ht L K hL hK hfull hretained u v a hv'
  exact (congrArg₂ (fun d f : SpatialPhotonSpace (volume : Measure (EuclideanSpace ℝ I)) =>
    (-Complex.I) • d - (e : ℂ) • f) hd hf).trans
    (covariant_algebra (KrausL2.coordinate volume ((photonFactorization BF).factor j) a).toLinearMap
      (derivative i q) (spatialField volume C g hg L hL u)
      (spatialField volume C t ht K hK u)
      (spatialChannelVacuum volume BF C j κ hκ M hb u a) (e : ℂ))

end GptLean.PhysicalFock
