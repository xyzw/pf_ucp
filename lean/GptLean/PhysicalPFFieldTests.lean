import GptLean.PhysicalPFReference
import GptLean.PhysicalFockFieldSymmetry
import GptLean.PhotonLocalizationLocalForms

/-! Real bounded multipliers preserve symmetry of the physical field pairing. -/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalization
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem l2_inner_eq_of_ae {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v w z : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, ⟪u x, v x⟫_ℂ = ⟪w x, z x⟫_ℂ) : ⟪u, v⟫_ℂ = ⟪w, z⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_congr_ae h

private theorem weighted_pair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : ℝ) (u v Au Av : H) (h : ⟪Au, v⟫_ℂ = ⟪u, Av⟫_ℂ) :
    ⟪u, a • Av⟫_ℂ = ⟪a • Au, v⟫_ℂ := by
  rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul, h]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (C : CanonicalSectorCCR photonMeasure) (κ : X → WeightedPhotonKernel)
  (hκ : AEStronglyMeasurable κ μ) (M : ℝ)
  (hbound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)

theorem weighted_spatialField_symmetric (a : X → ℝ)
    (ha : AEStronglyMeasurable a μ) (c : ℝ) (hc : ∀ᵐ x ∂μ, |a x| ≤ c)
    (u v : SpatialRadiationGraph μ) :
    ⟪spatialRadiationInclusion μ u,
      realL2Multiplier a ha c hc (spatialField μ C κ hκ M hbound v)⟫_ℂ =
    ⟪realL2Multiplier a ha c hc (spatialField μ C κ hκ M hbound u),
      spatialRadiationInclusion μ v⟫_ℂ := by
  apply l2_inner_eq_of_ae
  filter_upwards [radiationGraphInclusion.coeFn_compLpL u,
    radiationGraphInclusion.coeFn_compLpL v,
    spatialField_ae μ C κ hκ M hbound u,
    spatialField_ae μ C κ hκ M hbound v,
    realL2Multiplier_apply a ha c hc (spatialField μ C κ hκ M hbound u),
    realL2Multiplier_apply a ha c hc (spatialField μ C κ hκ M hbound v)]
    with x hiu hiv hfu hfv hau hav
  have hu := hau.trans (congrArg (fun w : PhotonFock => a x • w) hfu)
  have hv := hav.trans (congrArg (fun w : PhotonFock => a x • w) hfv)
  exact (congrArg₂ (fun w z : PhotonFock => ⟪w, z⟫_ℂ) hiu hv).trans
    ((weighted_pair (a x) _ _ _ _ (kernelField_symmetric C (κ x) (u x) (v x))).trans
      (congrArg₂ (fun w z : PhotonFock => ⟪w, z⟫_ℂ) hu.symm hiv.symm))

end GptLean.PhysicalFock

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock PhotonLocalization
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

theorem weighted_field_symmetric (i : I) (a : Position I → ℝ)
    (ha : AEStronglyMeasurable a volume) (c : ℝ)
    (hc : ∀ᵐ x ∂volume, |a x| ≤ c) (u v : Reference I V) :
    ⟪inclusion I V u, realL2Multiplier a ha c hc (field I V C κ hκ M hbound i v)⟫_ℂ =
    ⟪realL2Multiplier a ha c hc (field I V C κ hκ M hbound i u), inclusion I V v⟫_ℂ := by
  have h := weighted_spatialField_symmetric volume C (κ i) (hκ i) M (hbound i)
    a ha c hc (radiationSource I V u) (radiationSource I V v)
  exact (congrArg (fun f : WaveSpace I =>
    ⟪f, realL2Multiplier a ha c hc (field I V C κ hκ M hbound i v)⟫_ℂ)
      (radiation_matches I V u).symm).trans
    (h.trans (congrArg (fun f : WaveSpace I =>
      ⟪realL2Multiplier a ha c hc (field I V C κ hκ M hbound i u), f⟫_ℂ)
        (radiation_matches I V v)))

end GptLean.PhysicalPFReference
