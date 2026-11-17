import PfHk.OrdinaryCoordinateLpMultiplier
import PfHk.OrdinaryH1Norm
import GptLean.PhysicalPairH1Sobolev

/-! Critical coordinate multiplication on the actual ordinary H1 graph.
The constant is constructed by the closed-graph theorem from the proved
Hilbert-valued three-dimensional Sobolev membership theorem. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.OrdinaryCoordinateH1Multiplier

open MeasureTheory GptLean GptLean.ElectronicH1Space
open GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
open GptLean.PhysicalSourceFubini PfHk.CoordinateSobolev
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option maxHeartbeats 200000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

private instance six_fact : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

def sourceTwo (n : Fin N) : H1 H (Fin N × Fin 3) →L[ℝ]
    Lp (Lp H 2 (volume : Measure (Spectator n))) 2 (volume : Measure Position) :=
  ((particleMap (H := H) n).toContinuousLinearMap.restrictScalars ℝ).comp value

theorem sourceTwo_six (n : Fin N) (u : H1 H (Fin N × Fin 3)) :
    MemLp (sourceTwo n u) 6 volume := particleSource_memLp_six n u

def sourceSix (n : Fin N) : H1 H (Fin N × Fin 3) →L[ℝ]
    Lp (Lp H 2 (volume : Measure (Spectator n))) 6 (volume : Measure Position) :=
  PhysicalLpUpgrade.map (sourceTwo n) (sourceTwo_six n)

theorem sourceTwo_apply (n : Fin N) (u : H1 H (Fin N × Fin 3)) :
    sourceTwo n u = particleMap (H := H) n (value (E := H) (I := Fin N × Fin 3) u) := rfl

attribute [local irreducible] sourceTwo sourceSix value gradient particleMap

def constant (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (n : Fin N) : ℝ :=
  ‖sourceSix (H := H) n‖ ^ 2

theorem constant_nonneg (n : Fin N) : 0 ≤ constant H n := sq_nonneg _

attribute [local irreducible] constant

theorem source_norm_bound (n : Fin N) (u : H1 H (Fin N × Fin 3)) :
    (eLpNorm (particleMap (H := H) n (value (E := H) (I := Fin N × Fin 3) u)) 6 volume).toReal ≤ ‖sourceSix (H := H) n‖ * ‖u‖ := by
  have h := OrdinaryH1Norm.lp_upgrade_bound (sourceTwo (H := H) n) (sourceTwo_six n) u
  unfold sourceSix
  
  exact (congrArg (fun z : Lp (Lp H 2 (volume : Measure (Spectator n))) 2 (volume : Measure Position) => (eLpNorm z 6 volume).toReal)
    (sourceTwo_apply n u)).symm.le.trans h

theorem multiplier (n : Fin N) (b : Position → ℝ) (hb : MemLp b 3 volume)
    (u : H1 H (Fin N × Fin 3)) :
    ∃ hm : MemLp (fun x => coordinateCoefficient n b x • value (E := H) (I := Fin N × Fin 3) u x) 2 volume,
      ‖hm.toLp (fun x => coordinateCoefficient n b x • value (E := H) (I := Fin N × Fin 3) u x)‖ ^ 2 ≤
        constant H n * (eLpNorm b 3 volume).toReal ^ 2 * ‖u‖ ^ 2 := by
  have hs : MemLp (particleMap (H := H) n (value (E := H) (I := Fin N × Fin 3) u)) 6 volume := by
    rw [← sourceTwo_apply n u]
    exact sourceTwo_six n u
  have hex := OrdinaryCoordinateLpMultiplier.multiplier n b hb
    (value (E := H) (I := Fin N × Fin 3) u) hs (‖sourceSix (H := H) n‖ * ‖u‖)
    (source_norm_bound n u)
  let hm := Classical.choose hex
  have hn := Classical.choose_spec hex
  refine ⟨hm, ?_⟩
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (by unfold constant; ring)

omit [TopologicalSpace.SeparableSpace H] in
theorem h1_norm_sq_bound {I : Type*} [Fintype I] [DecidableEq I]
    (u : H1 H I) : ‖u‖ ^ 2 ≤ ‖value u‖ ^ 2 + derivativeEnergy u :=
  OrdinaryH1Norm.h1_norm_sq_bound (H := H) (I := I) u

end PfHk.OrdinaryCoordinateH1Multiplier

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
