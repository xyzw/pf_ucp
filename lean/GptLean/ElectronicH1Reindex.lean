import GptLean.ElectronicH1Core
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
Changing the finite coordinate index preserves the actual H1 graph.
This transports the proved smooth compact core from Fin d to any finite
index, including particle-coordinate pairs, with no new density premise.
-/

noncomputable section

namespace GptLean.ElectronicH1Reindex

open MeasureTheory Filter ElectronicH1Space SymmetricLift
open scoped ENNReal ContDiff Topology

set_option backward.isDefEq.respectTransparency.types false

variable {I J E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def coordinates (e : I ≃ J) : EuclideanSpace ℝ I ≃ₗᵢ[ℝ] EuclideanSpace ℝ J :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

omit [DecidableEq I] [DecidableEq J] in
@[simp] theorem coordinates_symm (e : I ≃ J) : (coordinates e).symm = coordinates e.symm :=
  LinearIsometryEquiv.piLpCongrLeft_symm e

@[simp] theorem coordinates_single (e : I ≃ J) (i : I) :
    coordinates e (EuclideanSpace.single i 1) = EuclideanSpace.single (e i) 1 :=
  LinearIsometryEquiv.piLpCongrLeft_single e i 1

def pull (e : I ≃ J) : L2 E I →ₗᵢ[ℝ] L2 E J :=
  Lp.compMeasurePreservingₗᵢ ℝ (coordinates e).symm (coordinates e).symm.measurePreserving

omit [DecidableEq I] [DecidableEq J] [CompleteSpace E] in
theorem pull_ae (e : I ≃ J) (v : L2 E I) :
    pull e v =ᵐ[volume] fun x => v ((coordinates e).symm x) :=
  Lp.coeFn_compMeasurePreserving v (coordinates e).symm.measurePreserving

omit [DecidableEq I] [DecidableEq J] [CompleteSpace E] in
theorem pull_symm_pull (e : I ≃ J) (v : L2 E I) : pull e.symm (pull e v) = v := by
  apply Lp.ext
  have hp := (coordinates e.symm).symm.measurePreserving.quasiMeasurePreserving.ae (pull_ae e v)
  filter_upwards [pull_ae e.symm (pull e v), hp] with x hx hy
  rw [hx, hy]
  simp only [← coordinates_symm, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.symm_apply_apply]

omit [DecidableEq I] [DecidableEq J] [CompleteSpace E] in
theorem pull_test_integral (e : I ≃ J) (v : L2 E I) (φ : EuclideanSpace ℝ J → ℝ) :
    (∫ x, φ x • pull e v x) = ∫ z, φ (coordinates e z) • v z := by
  calc
    _ = ∫ x, φ (coordinates e ((coordinates e).symm x)) •
        v ((coordinates e).symm x) := by
      apply integral_congr_ae
      filter_upwards [pull_ae e v] with x hx
      rw [hx]
      rw [(coordinates e).apply_symm_apply]
    _ = _ := (coordinates e).symm.measurePreserving.integral_comp
      (coordinates e).symm.toMeasurableEquiv.measurableEmbedding
      (fun z => φ (coordinates e z) • v z)

theorem pull_test_fderiv (e : I ≃ J) (j : J) (φ : EuclideanSpace ℝ J → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (z : EuclideanSpace ℝ I) :
    fderiv ℝ (φ ∘ coordinates e) z (EuclideanSpace.single (e.symm j) 1) =
      fderiv ℝ φ (coordinates e z) (EuclideanSpace.single j 1) := by
  have hh : fderiv ℝ (φ ∘ coordinates e) z =
      (fderiv ℝ φ (coordinates e z)).comp (coordinates e).toContinuousLinearEquiv.toContinuousLinearMap :=
    ((hφ.differentiable (by simp) _).hasFDerivAt.comp z
      (coordinates e).toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, coordinates_single, e.apply_symm_apply]

theorem weak_pull (e : I ≃ J) (u : H1 E I) :
    HasWeakH1Local (pull e (value u)) (fun j => pull e (derivative (e.symm j) u)) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun j K _ => (Lp.memLp _).restrict K, ?_⟩
  intro j φ hφ hs
  rw [pull_test_integral, pull_test_integral]
  have htest : ContDiff ℝ ∞ (φ ∘ coordinates e) :=
    hφ.comp (coordinates e).toContinuousLinearEquiv.contDiff
  have hcompact : HasCompactSupport (φ ∘ coordinates e) :=
    hs.comp_homeomorph (coordinates e).toHomeomorph
  have h := (weak u).weak (e.symm j) _ htest hcompact
  simpa only [Function.comp_apply, pull_test_fderiv e j φ hφ] using h

def reindexed (e : I ≃ J) (u : H1 E I) : H1 E J :=
  ⟨(pull e (value u), fun j => pull e (derivative (e.symm j) u)), weak_pull e u⟩

@[simp] theorem value_reindexed (e : I ≃ J) (u : H1 E I) :
    value (reindexed e u) = pull e (value u) := rfl

@[simp] theorem derivative_reindexed (e : I ≃ J) (u : H1 E I) (j : J) :
    derivative j (reindexed e u) = pull e (derivative (e.symm j) u) := rfl

theorem gradient_reindexed_norm (e : I ≃ J) (u : H1 E I) :
    ‖gradient (reindexed e u)‖ = ‖gradient u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    change ‖pull e (derivative (e.symm j) u)‖ ≤ _
    rw [(pull e).norm_map]
    exact norm_le_pi_norm (gradient u) (e.symm j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm (gradient (reindexed e u)) (e i)
    change ‖pull e (derivative (e.symm (e i)) u)‖ ≤ _ at h
    change ‖derivative i u‖ ≤ _
    simpa only [(pull e).norm_map, e.symm_apply_apply] using h

def reindex (e : I ≃ J) : H1 E I ≃ₗᵢ[ℝ] H1 E J where
  toFun := reindexed e
  invFun := reindexed e.symm
  left_inv u := value_injective (by simp only [value_reindexed, pull_symm_pull])
  right_inv u := value_injective (by
    simp only [value_reindexed]
    exact pull_symm_pull e.symm (value u))
  map_add' u v := value_injective (by simp only [value_reindexed, map_add])
  map_smul' c u := value_injective (by simp only [value_reindexed, map_smul, RingHom.id_apply])
  norm_map' u := by
    change ‖reindexed e u‖ = ‖u‖
    rw [norm_eq_max, value_reindexed, (pull e).norm_map, gradient_reindexed_norm, ← norm_eq_max]

def genericSmoothCore (E I : Type*) [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] : Set (H1 E I) :=
  {u | ∃ (f : EuclideanSpace ℝ I → E) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f), u = ofSmoothCompact f hf hs}

theorem reindex_smoothCore (e : I ≃ J) {u : H1 E I}
    (hu : u ∈ genericSmoothCore E I) : reindex e u ∈ genericSmoothCore E J := by
  obtain ⟨f, hf, hs, rfl⟩ := hu
  let g := f ∘ (coordinates e).symm
  have hg : ContDiff ℝ ∞ g := hf.comp (coordinates e).symm.toContinuousLinearEquiv.contDiff
  have hgs : HasCompactSupport g := hs.comp_homeomorph (coordinates e).symm.toHomeomorph
  have hf2 : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hs
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgs
  refine ⟨g, hg, hgs, value_injective ?_⟩
  apply Lp.ext
  have ha := (coordinates e).symm.measurePreserving.quasiMeasurePreserving.ae
    hf2.coeFn_toLp
  filter_upwards [pull_ae e (value (ofSmoothCompact f hf hs)), ha,
    hg2.coeFn_toLp] with x hx hy hz
  change value (reindexed e (ofSmoothCompact f hf hs)) x = value (ofSmoothCompact g hg hgs) x
  rw [value_reindexed, hx]
  exact hy.trans hz.symm

/-- Smooth compact representatives are dense for every finite coordinate index. -/
theorem dense_genericSmoothCore : Dense (genericSmoothCore E I) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have h : Dense ((reindex (E := E) e) '' ElectronicH1Core.smoothCore E (Fintype.card I)) :=
    (reindex e).surjective.denseRange.dense_image (reindex e).continuous ElectronicH1Core.dense_smoothCore
  apply h.mono
  rintro _ ⟨u, hu, rfl⟩
  exact reindex_smoothCore e hu

end GptLean.ElectronicH1Reindex
