import GptLean.PhysicalSourceMarginal
import GptLean.SymmetricLift.MetricGeometry
import Mathlib.MeasureTheory.Group.Prod

/-!
The actual relative coordinate x_i-x_j is obtained by a triangular,
measure-preserving shear. Its selected-coordinate H1 source follows from
the proved weak Fubini transport, giving relative L6 regularity directly.
-/

noncomputable section

namespace GptLean.PhysicalRelativeCoordinates

open MeasureTheory GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
open GptLean.ElectronicH1Space

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

def spectatorParticle (i : Fin N) (j : {j : Fin N // j ≠ i}) : Spectator i →L[ℝ] Position :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun a => y (j, a))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def shear (i : Fin N) (B : Spectator i →L[ℝ] Position) :
    (Position × Spectator i) ≃L[ℝ] (Position × Spectator i) where
  toFun p := (p.1 - B p.2, p.2)
  invFun p := (p.1 + B p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
    · rfl
  map_smul' c p := by simp [smul_sub]
  continuous_toFun := (continuous_fst.sub (B.continuous.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add (B.continuous.comp continuous_snd)).prodMk continuous_snd

theorem shear_measurePreserving (i : Fin N) (B : Spectator i →L[ℝ] Position) :
    MeasurePreserving (shear i B)
      ((volume : Measure Position).prod (volume : Measure (Spectator i)))
      ((volume : Measure Position).prod (volume : Measure (Spectator i))) := by
  have hk : MeasurePreserving (fun p : Spectator i × Position => (p.1, p.2 - B p.1))
      ((volume : Measure (Spectator i)).prod volume)
      ((volume : Measure (Spectator i)).prod volume) :=
    (MeasurePreserving.id (volume : Measure (Spectator i))).skew_product
      (continuous_snd.sub (B.continuous.comp continuous_fst)).measurable
      (ae_of_all _ fun y => (measurePreserving_sub_right (volume : Measure Position) (B y)).map_eq)
  exact Measure.measurePreserving_swap.comp (hk.comp Measure.measurePreserving_swap)

def relativeSplit (i j : Fin N) (hij : i ≠ j) :
    Configuration N ≃L[ℝ] Position × Spectator i :=
  (split i).trans (shear i (spectatorParticle i ⟨j, hij.symm⟩))

theorem relativeSplit_fst (i j : Fin N) (hij : i ≠ j) (x : Configuration N) :
    (relativeSplit i j hij x).1 = SymmetricLift.particle x i - SymmetricLift.particle x j := by
  ext a
  rfl

theorem relativeSplit_single_selected (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    relativeSplit i j hij (EuclideanSpace.single (i, a) 1) = (EuclideanSpace.single a 1, 0) := by
  change shear i (spectatorParticle i ⟨j, hij.symm⟩)
    (split i (EuclideanSpace.single (i, a) 1)) = _
  rw [split_single_selected]
  simp [shear]

theorem relativeSplit_measurePreserving (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (relativeSplit i j hij) volume
      ((volume : Measure Position).prod (volume : Measure (Spectator i))) :=
  (shear_measurePreserving i (spectatorParticle i ⟨j, hij.symm⟩)).comp (split_measurePreserving i)

theorem relativeSplit_symm_measurePreserving (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (relativeSplit i j hij).symm
      ((volume : Measure Position).prod (volume : Measure (Spectator i))) volume := by
  exact (show MeasurePreserving (relativeSplit i j hij).toHomeomorph.toMeasurableEquiv
    volume (volume.prod volume) from relativeSplit_measurePreserving i j hij).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

def relativeSource (i j : Fin N) (hij : i ≠ j) (u : H1 H (Fin N × Fin 3)) :
    H1 (Lp H 2 (volume : Measure (Spectator i))) (Fin 3) :=
  ofSplitH1 (relativeSplit i j hij) (relativeSplit_symm_measurePreserving i j hij)
    (fun a => (i, a)) (relativeSplit_single_selected i j hij) u

@[simp] theorem value_relativeSource (i j : Fin N) (hij : i ≠ j)
    (u : H1 H (Fin N × Fin 3)) :
    value (relativeSource i j hij u) =
      sourceMap (relativeSplit i j hij) (relativeSplit_symm_measurePreserving i j hij) (value u) := rfl

@[simp] theorem derivative_relativeSource (i j : Fin N) (hij : i ≠ j)
    (u : H1 H (Fin N × Fin 3)) (a : Fin 3) :
    derivative a (relativeSource i j hij u) =
      sourceMap (relativeSplit i j hij) (relativeSplit_symm_measurePreserving i j hij)
        (derivative (i, a) u) := rfl

theorem relativeSource_memLp_six (i j : Fin N) (hij : i ≠ j)
    (u : H1 H (Fin N × Fin 3)) : MemLp (value (relativeSource i j hij u)) 6 volume := by
  let := InnerProductSpace.rclikeToReal ℂ (Lp H 2 (volume : Measure (Spectator i)))
  exact PhysicalPairH1Sobolev.value_memLp_six (relativeSource i j hij u)

end GptLean.PhysicalRelativeCoordinates
