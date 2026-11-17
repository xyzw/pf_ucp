import GptLean.PhysicalFockCreation

/-! Linearity of the concrete tensor insertion in its one-photon kernel. -/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

section Product

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ}

theorem productL2_add_left (f h : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productL2 (f + h) g = productL2 f g + productL2 h g := by
  apply Lp.ext
  filter_upwards [productL2_ae (f + h) g, productL2_ae f g, productL2_ae h g,
    (Measure.quasiMeasurePreserving_fst (ν := ν)).ae (Lp.coeFn_add f h),
    Lp.coeFn_add (productL2 f g) (productL2 h g)] with z ha hb hc hd he
  rw [ha, he, Pi.add_apply, hb, hc, hd, Pi.add_apply, add_mul]

theorem productL2_smul_left (f : Lp ℂ 2 μ) (c : ℂ) (g : Lp ℂ 2 ν) :
    productL2 (c • f) g = c • productL2 f g := by
  apply Lp.ext
  filter_upwards [productL2_ae (c • f) g, productL2_ae f g,
    (Measure.quasiMeasurePreserving_fst (ν := ν)).ae (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (productL2 f g)] with z ha hb hc hd
  rw [ha, hd, Pi.smul_apply, hb, hc, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

end Product

section Sectors

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem tensorInsertion_add (n : ℕ) (f g : Lp ℂ 2 μ) :
    tensorInsertion μ n (f + g) = tensorInsertion μ n f + tensorInsertion μ n g := by
  apply ContinuousLinearMap.ext
  intro u
  change (Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 (f + g) u) =
    (Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 f u) +
      (Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 g u)
  rw [productL2_add_left, map_add]

theorem tensorInsertion_smul (n : ℕ) (f : Lp ℂ 2 μ) (c : ℂ) :
    tensorInsertion μ n (c • f) = c • tensorInsertion μ n f := by
  apply ContinuousLinearMap.ext
  intro u
  change (Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 (c • f) u) =
    c • (Lp.compMeasurePreservingₗᵢ ℂ _ _) (productL2 f u)
  rw [productL2_smul_left, map_smul]

theorem creationSector_add (n : ℕ) (f g : Lp ℂ 2 μ) :
    creationSector μ n (f + g) = creationSector μ n f + creationSector μ n g := by
  unfold creationSector
  rw [tensorInsertion_add]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add]

theorem creationSector_smul (n : ℕ) (f : Lp ℂ 2 μ) (c : ℂ) :
    creationSector μ n (c • f) = c • creationSector μ n f := by
  unfold creationSector
  rw [tensorInsertion_smul]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  exact smul_comm _ _ _

theorem annihilationSector_add (n : ℕ) (f g : Lp ℂ 2 μ) :
    annihilationSector μ n (f + g) = annihilationSector μ n f + annihilationSector μ n g := by
  unfold annihilationSector
  rw [creationSector_add, map_add]

theorem annihilationSector_smul (n : ℕ) (f : Lp ℂ 2 μ) (c : ℂ) :
    annihilationSector μ n (c • f) = starRingEnd ℂ c • annihilationSector μ n f := by
  unfold annihilationSector
  rw [creationSector_smul, map_smulₛₗ]

end Sectors

end GptLean.PhysicalFock
