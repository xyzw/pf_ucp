import GptLean.PhysicalPFFieldTests
import GptLean.ElectronicH1Symmetry

/-! Symmetry of every actual covariant derivative on the common reference domain. -/

noncomputable section

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock PhotonLocalization
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem multiplier_one {X H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (u : Lp H 2 μ) :
    realL2Multiplier (fun _ : X => (1 : ℝ)) aestronglyMeasurable_const 1
      (ae_of_all _ fun _ => by norm_num) u = u := by
  apply Lp.ext
  filter_upwards [realL2Multiplier_apply (fun _ : X => (1 : ℝ))
    aestronglyMeasurable_const 1 (ae_of_all _ fun _ => by norm_num) u] with x hx
  simpa only [one_smul] using hx

private theorem covariant_pair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v du dv fu fv : H) (e : ℝ)
    (hd : ⟪u, dv⟫_ℂ = -⟪du, v⟫_ℂ) (hf : ⟪u, fv⟫_ℂ = ⟪fu, v⟫_ℂ) :
    ⟪u, (-Complex.I) • dv - (e : ℂ) • fv⟫_ℂ =
      ⟪(-Complex.I) • du - (e : ℂ) • fu, v⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal, hd, hf]
  ring

theorem spatial_field_symmetric {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (C : CanonicalSectorCCR photonMeasure) (κ : X → WeightedPhotonKernel)
    (hκ : AEStronglyMeasurable κ μ) (M : ℝ) (hbound : ∀ᵐ x ∂μ, ‖κ x‖ ≤ M)
    (u v : SpatialRadiationGraph μ) :
    ⟪spatialRadiationInclusion μ u, spatialField μ C κ hκ M hbound v⟫_ℂ =
      ⟪spatialField μ C κ hκ M hbound u, spatialRadiationInclusion μ v⟫_ℂ := by
  have h := weighted_spatialField_symmetric μ C κ hκ M hbound (fun _ => 1)
    aestronglyMeasurable_const 1 (ae_of_all _ fun _ => by norm_num) u v
  exact (congrArg (fun w : Lp PhotonFock 2 μ => ⟪spatialRadiationInclusion μ u, w⟫_ℂ)
    (multiplier_one (spatialField μ C κ hκ M hbound v)).symm).trans
      (h.trans (congrArg (fun w : Lp PhotonFock 2 μ => ⟪w, spatialRadiationInclusion μ v⟫_ℂ)
        (multiplier_one (spatialField μ C κ hκ M hbound u))))

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

theorem field_symmetric (i : I) (u v : Reference I V) :
    ⟪inclusion I V u, field I V C κ hκ M hbound i v⟫_ℂ =
      ⟪field I V C κ hκ M hbound i u, inclusion I V v⟫_ℂ := by
  have h := weighted_field_symmetric I V C κ hκ M hbound i (fun _ => 1)
    aestronglyMeasurable_const 1 (ae_of_all _ fun _ => by norm_num) u v
  exact (congrArg (fun w : WaveSpace I => ⟪inclusion I V u, w⟫_ℂ)
    (multiplier_one (field I V C κ hκ M hbound i v)).symm).trans
      (h.trans (congrArg (fun w : WaveSpace I => ⟪w, inclusion I V v⟫_ℂ)
        (multiplier_one (field I V C κ hκ M hbound i u))))

theorem covariant_symmetric (e : ℝ) (i : I) (u v : Reference I V) :
    ⟪inclusion I V u, covariant I V C κ hκ M hbound e i v⟫_ℂ =
      ⟪covariant I V C κ hκ M hbound e i u, inclusion I V v⟫_ℂ := by
  exact covariant_pair (inclusion I V u) (inclusion I V v)
    (ordinary I V i u) (ordinary I V i v)
    (field I V C κ hκ M hbound i u) (field I V C κ hκ M hbound i v) e
    (ElectronicH1Symmetry.integration_by_parts
      (ElectronicH1Complex.realEquiv (electronic I V u))
      (ElectronicH1Complex.realEquiv (electronic I V v)) i)
    (field_symmetric I V C κ hκ M hbound i u v)

end GptLean.PhysicalPFReference
