import GptLean.PhysicalSectorCoordinates
import GptLean.SymmetricLift.Geometry

/-! Coordinate formulas for the actual finite-sector isometry. -/

noncomputable section
namespace GptLean.PhysicalSectorCoordinates

open MeasureTheory PhysicalFock PhysicalSectorMeasures

theorem finitePosition_apply (N M : ℕ)
    (u : PhysicalFiniteSectorCoordinates.numberSubspace (Sector photonMeasure)
      (volume : Measure (Configuration N)) M) (m : Fin (M + 1)) :
    finitePosition N M u m = spatialSectorPosition N m.val
      (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m.val u.val) := rfl

theorem configurationSplit_particle_fst (N m : ℕ) (x : Configuration (N + m)) (i : Fin N) :
    SymmetricLift.particle (configurationSplit N m x).1 i =
      SymmetricLift.particle x (Fin.castAdd m i) := by
  ext a
  rfl

theorem configurationSplit_particle_snd (N m : ℕ) (x : Configuration (N + m)) (i : Fin m) :
    SymmetricLift.particle (configurationSplit N m x).2 i =
      SymmetricLift.particle x (Fin.natAdd N i) := by
  ext a
  rfl

end GptLean.PhysicalSectorCoordinates
