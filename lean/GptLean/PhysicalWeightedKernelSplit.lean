import GptLean.PhysicalFockKernelField
import GptLean.PhysicalPhotonHardSoft

/-!
Sharp momentum restriction of both components of an actual weighted photon
kernel. The inverse-frequency relation is preserved pointwise. The resulting
continuous maps are contractions and give the exact hard/soft decomposition.
-/

noncomputable section

namespace GptLean.PhysicalFock.WeightedPhotonKernel

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The ordinary component determines a weighted physical kernel. -/
theorem ext_fst {k l : WeightedPhotonKernel} (h : k.val.1 = l.val.1) : k = l := by
  apply Subtype.ext
  refine Prod.ext h ?_
  apply Lp.ext
  have hn : ∀ᵐ p ∂photonMeasure, p.1 ≠ (0 : Gaussian.FieldSpace) :=
    (Measure.quasiMeasurePreserving_fst (ν := (Measure.count : Measure (Fin 2)))).ae
      (volume.ae_ne 0)
  filter_upwards [k.property, l.property, hn] with p hk hl hn
  have he : (Real.sqrt ‖p.1‖ : ℂ) * k.val.2 p =
      (Real.sqrt ‖p.1‖ : ℂ) * l.val.2 p :=
    hk.symm.trans ((congrArg (fun f : Lp ℂ 2 photonMeasure => f p) h).trans hl)
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_iff.mpr hn)))) he

variable (s : Set PhotonMode) (hs : MeasurableSet s)

private theorem projection_mem (k : WeightedPhotonKernel) :
    (MomentumSplit.projection photonMeasure s hs k.val.1,
      MomentumSplit.projection photonMeasure s hs k.val.2) ∈ weightedKernelSubspace := by
  filter_upwards [k.property, MomentumSplit.projection_ae photonMeasure s hs k.val.1,
    MomentumSplit.projection_ae photonMeasure s hs k.val.2] with p hk h₁ h₂
  change MomentumSplit.projection photonMeasure s hs k.val.1 p =
    (Real.sqrt ‖p.1‖ : ℂ) * MomentumSplit.projection photonMeasure s hs k.val.2 p
  rw [h₁, h₂]
  classical
  by_cases hp : p ∈ s <;> simp [hp, hk]

/-- Simultaneous sharp restriction of the ordinary and inverse-frequency components. -/
def projection : WeightedPhotonKernel →L[ℂ] WeightedPhotonKernel :=
  (((MomentumSplit.projection photonMeasure s hs).prodMap
      (MomentumSplit.projection photonMeasure s hs)).comp weightedKernelSubspace.subtypeL).codRestrict
    weightedKernelSubspace (projection_mem s hs)

@[simp] theorem projection_fst (k : WeightedPhotonKernel) :
    (projection s hs k).val.1 = MomentumSplit.projection photonMeasure s hs k.val.1 := rfl

@[simp] theorem projection_snd (k : WeightedPhotonKernel) :
    (projection s hs k).val.2 = MomentumSplit.projection photonMeasure s hs k.val.2 := rfl

theorem projection_fst_ae (k : WeightedPhotonKernel) :
    (projection s hs k).val.1 =ᵐ[photonMeasure] s.indicator k.val.1 :=
  MomentumSplit.projection_ae photonMeasure s hs k.val.1

theorem projection_snd_ae (k : WeightedPhotonKernel) :
    (projection s hs k).val.2 =ᵐ[photonMeasure] s.indicator k.val.2 :=
  MomentumSplit.projection_ae photonMeasure s hs k.val.2

private theorem scalar_projection_norm_le (u : Lp ℂ 2 photonMeasure) :
    ‖MomentumSplit.projection photonMeasure s hs u‖ ≤ ‖u‖ := by
  calc
    _ ≤ 1 * ‖u‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MomentumSplit.projection_ae photonMeasure s hs u] with p hp
      rw [hp]
      classical
      by_cases h : p ∈ s <;> simp [h]
    _ = _ := one_mul _

theorem projection_norm_le (k : WeightedPhotonKernel) : ‖projection s hs k‖ ≤ ‖k‖ := by
  change max ‖MomentumSplit.projection photonMeasure s hs k.val.1‖
      ‖MomentumSplit.projection photonMeasure s hs k.val.2‖ ≤ max ‖k.val.1‖ ‖k.val.2‖
  exact max_le_max (scalar_projection_norm_le s hs k.val.1)
    (scalar_projection_norm_le s hs k.val.2)

theorem projection_add_compl (k : WeightedPhotonKernel) :
    projection s hs k + projection sᶜ hs.compl k = k := by
  apply Subtype.ext
  exact Prod.ext (MomentumSplit.projection_add_compl photonMeasure s hs k.val.1)
    (MomentumSplit.projection_add_compl photonMeasure s hs k.val.2)

/-- The actual sharp soft-kernel map. -/
def soft (κ : ℝ) : WeightedPhotonKernel →L[ℂ] WeightedPhotonKernel :=
  projection (softMomentumSet κ) (softMomentumSet_measurable κ)

/-- The complementary hard-kernel map. -/
def hard (κ : ℝ) : WeightedPhotonKernel →L[ℂ] WeightedPhotonKernel :=
  projection (softMomentumSet κ)ᶜ (softMomentumSet_measurable κ).compl

theorem soft_add_hard (κ : ℝ) (k : WeightedPhotonKernel) : soft κ k + hard κ k = k :=
  projection_add_compl _ _ k

theorem hard_add_soft (κ : ℝ) (k : WeightedPhotonKernel) : hard κ k + soft κ k = k := by
  rw [add_comm, soft_add_hard]

theorem soft_norm_le (κ : ℝ) (k : WeightedPhotonKernel) : ‖soft κ k‖ ≤ ‖k‖ :=
  projection_norm_le _ _ k

theorem hard_norm_le (κ : ℝ) (k : WeightedPhotonKernel) : ‖hard κ k‖ ≤ ‖k‖ :=
  projection_norm_le _ _ k

@[simp] theorem soft_fst (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.1 = MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) k.val.1 := rfl

@[simp] theorem soft_snd (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.2 = MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) k.val.2 := rfl

@[simp] theorem hard_fst (κ : ℝ) (k : WeightedPhotonKernel) :
    (hard κ k).val.1 = MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl k.val.1 := rfl

@[simp] theorem hard_snd (κ : ℝ) (k : WeightedPhotonKernel) :
    (hard κ k).val.2 = MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
      (softMomentumSet_measurable κ).compl k.val.2 := rfl

theorem soft_fst_mem (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.1 ∈ softOnePhoton κ :=
  MomentumSplit.projection_mem_supported _ _ _ _

theorem soft_snd_mem (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.2 ∈ softOnePhoton κ :=
  MomentumSplit.projection_mem_supported _ _ _ _

theorem hard_fst_mem (κ : ℝ) (k : WeightedPhotonKernel) :
    (hard κ k).val.1 ∈ hardOnePhoton κ :=
  MomentumSplit.projection_mem_supported _ _ _ _

theorem hard_snd_mem (κ : ℝ) (k : WeightedPhotonKernel) :
    (hard κ k).val.2 ∈ hardOnePhoton κ :=
  MomentumSplit.projection_mem_supported _ _ _ _

private theorem scalar_soft_mem_hard_orthogonal (κ : ℝ) (u : Lp ℂ 2 photonMeasure) :
    MomentumSplit.projection photonMeasure (softMomentumSet κ)
      (softMomentumSet_measurable κ) u ∈ (hardOnePhoton κ)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  have hp := MomentumSplit.projection_of_supported photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl ⟨v, hv⟩
  change MomentumSplit.projection photonMeasure (softMomentumSet κ)ᶜ
    (softMomentumSet_measurable κ).compl v = v at hp
  rw [← hp]
  exact MomentumSplit.projection_inner_compl photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) u v

theorem soft_fst_mem_hard_orthogonal (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.1 ∈ (hardOnePhoton κ)ᗮ :=
  scalar_soft_mem_hard_orthogonal κ k.val.1

theorem soft_snd_mem_hard_orthogonal (κ : ℝ) (k : WeightedPhotonKernel) :
    (soft κ k).val.2 ∈ (hardOnePhoton κ)ᗮ :=
  scalar_soft_mem_hard_orthogonal κ k.val.2

theorem soft_hard_inner (κ : ℝ) (k l : WeightedPhotonKernel) :
    inner ℂ (soft κ k).val.1 (hard κ l).val.1 = 0 :=
  MomentumSplit.projection_inner_compl photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) k.val.1 l.val.1

theorem soft_hard_norm_partition (κ : ℝ) (k : WeightedPhotonKernel) :
    ‖(soft κ k).val.1‖ ^ 2 + ‖(hard κ k).val.1‖ ^ 2 = ‖k.val.1‖ ^ 2 :=
  MomentumSplit.projection_norm_partition photonMeasure (softMomentumSet κ)
    (softMomentumSet_measurable κ) k.val.1

end GptLean.PhysicalFock.WeightedPhotonKernel
