import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Canonical embeddings of different chart targets into one finite Hilbert sum. -/

noncomputable section
namespace GptLean.SymmetricLift
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → Type*) [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]

/-- No common local target is assumed. Each chart embeds into the actual
finite Hilbert direct sum of all chart targets. -/
def chartTargetEmbedding (i : ι) : K i →ₗᵢ[ℂ] PiLp 2 K where
  toFun := PiLp.single 2 i
  map_add' u v := PiLp.single_add 2 i
  map_smul' c u := by
    apply (WithLp.ext_iff 2).mpr
    change Pi.single i (c • u) = c • Pi.single i u
    exact Pi.single_smul i c u
  norm_map' u := PiLp.norm_single 2 K i u

theorem chartTargetEmbedding_inner (i : ι) (u v : K i) :
    inner ℂ (chartTargetEmbedding K i u) (chartTargetEmbedding K i v) = inner ℂ u v :=
  (chartTargetEmbedding K i).inner_map_map u v

variable {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [∀ i, NormedSpace ℝ (K i)] [∀ i, IsScalarTower ℝ ℂ (K i)]

theorem chartTargetEmbedding_contDiffOn (i : ι) {D : Set X}
    {V : X → H →L[ℂ] K i} (hV : ContDiffOn ℝ ∞ V D) :
    ContDiffOn ℝ ∞ (fun x => (chartTargetEmbedding K i).toContinuousLinearMap.comp (V x)) D := by
  exact ((ContinuousLinearMap.compL ℂ H (K i) (PiLp 2 K)
    (chartTargetEmbedding K i).toContinuousLinearMap).restrictScalars ℝ).contDiff.comp_contDiffOn hV

end GptLean.SymmetricLift
