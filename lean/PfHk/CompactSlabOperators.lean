import PfHk.OrdinaryPolarSobolevChart
import GptLean.PhysicalFockSpatialField

/-! Continuous bounded-operator families on a finite polar slab give
actual bounded multiplication operators on L2. The bound is derived from
compactness. This supplies closed-form continuity for test approximation. -/

noncomputable section
namespace PfHk.CompactSlabOperators

open MeasureTheory GptLean.PhysicalFock PfHk.OrdinaryPolarSobolevChart
  PfHk.PolarCalculus
open scoped ENNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

variable {N : ℕ} {Q H : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private theorem exists_bound (a b : ℝ) (T : Slab N → Q →L[ℂ] H) (hT : Continuous T) :
    ∃ M : ℝ, ∀ᵐ p ∂slabMeasure N a b, ‖T p‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_univ : IsCompact (Set.univ : Set (PfHk.SphereAngularField.Sphere N)))).exists_bound_of_continuousOn hT.continuousOn
  refine ⟨M, ?_⟩
  have ht : ∀ᵐ p ∂slabMeasure N a b, p.1 ∈ Set.Icc a b :=
    (Measure.quasiMeasurePreserving_fst (ν := sphereMeasure (Fin N × Fin 3))).ae
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  exact hM p ⟨hp, Set.mem_univ p.2⟩

def bound (a b : ℝ) (T : Slab N → Q →L[ℂ] H) (hT : Continuous T) : ℝ :=
  Classical.choose (exists_bound a b T hT)

theorem bound_ae (a b : ℝ) (T : Slab N → Q →L[ℂ] H) (hT : Continuous T) :
    ∀ᵐ p ∂slabMeasure N a b, ‖T p‖ ≤ bound a b T hT :=
  Classical.choose_spec (exists_bound a b T hT)

def lift (a b : ℝ) (T : Slab N → Q →L[ℂ] H) (hT : Continuous T) :
    Lp Q 2 (slabMeasure N a b) →L[ℂ] Lp H 2 (slabMeasure N a b) :=
  spatialOperator (slabMeasure N a b) T hT.aestronglyMeasurable
    (bound a b T hT) (bound_ae a b T hT)

theorem lift_ae (a b : ℝ) (T : Slab N → Q →L[ℂ] H) (hT : Continuous T)
    (u : Lp Q 2 (slabMeasure N a b)) :
    lift a b T hT u =ᵐ[slabMeasure N a b] fun p => T p (u p) :=
  spatialOperator_ae _ _ _ _ _ _

end PfHk.CompactSlabOperators
