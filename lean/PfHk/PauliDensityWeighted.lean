import PfHk.PauliCurrentGroundState
import PfHk.PhysicalShiftedFormEnergyFubini

/-! Integrable, possibly unbounded tests of the full spin-summed density. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliDensityWeighted

open MeasureTheory GptLean GptLean.PhysicalSourceCoordinates
  GptLean.PhysicalSourceMarginal GptLean.PhysicalPairSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 70000

attribute [local irreducible] PhysicalElectronicDensity.density

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
theorem particle_integrable (n : Fin N) (u : ElectronicH1Space.L2 H (Fin N × Fin 3))
    (w : PhysicalSourceCoordinates.Position → ℝ)
    (hi : Integrable (fun X => w ((split n) X).1 * ‖u X‖ ^ 2) volume) :
    Integrable (fun x => w x * ‖particleMap n u x‖ ^ 2) volume := by
  have hp := (split_symm_measurePreserving n).integrable_comp_of_integrable hi
  change Integrable (fun p : PhysicalSourceCoordinates.Position × Spectator n =>
    w ((split n) ((split n).symm p)).1 * ‖u ((split n).symm p)‖ ^ 2)
    (volume.prod volume) at hp
  have hp' : Integrable (fun p : PhysicalSourceCoordinates.Position × Spectator n =>
      w p.1 * ‖u ((split n).symm p)‖ ^ 2) (volume.prod volume) := by
    simpa only [(split n).apply_symm_apply] using hp
  apply hp'.integral_prod_left.congr
  filter_upwards [PhysicalSourcePair.particleMap_norm_sq_ae n u] with x hx
  rw [integral_const_mul, hx]

theorem density_integral (u : ElectronicH1Space.L2 H (Fin N × Fin 3))
    (w : PhysicalSourceCoordinates.Position → ℝ)
    (hi : ∀ n, Integrable (fun X => w ((split n) X).1 * ‖u X‖ ^ 2) volume) :
    (∫ x, w x * PhysicalElectronicDensity.density u x) =
      ∑ n, ∫ X, w ((split n) X).1 * ‖u X‖ ^ 2 := by
  calc
    _ = ∫ x, ∑ n, w x * ‖particleMap n u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [PhysicalElectronicDensity.density_ae (N := N) (H := H) u] with x hx
      have hs : w x * PhysicalElectronicDensity.densityFunction u x =
          ∑ n, w x * ‖particleMap n u x‖ ^ 2 :=
        Finset.mul_sum _ _ _
      exact (congrArg (fun r : ℝ => w x * r) hx).trans hs
    _ = ∑ n, ∫ x, w x * ‖particleMap n u x‖ ^ 2 :=
      integral_finsetSum _ (fun n _ => particle_integrable n u w (hi n))
    _ = _ := Finset.sum_congr rfl fun n _ =>
      PhysicalShiftedFormEnergyFubini.particleMap_weighted_norm_sq n u w (hi n)

theorem pair_density_integral (hN : 0 < N) (u : PauliCurrent.Components (N := N))
    (d : PauliCurrent.Derivatives (N := N)) (w : PhysicalSourceCoordinates.Position → ℝ)
    (hi : ∀ n, Integrable (fun X => w ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2) volume) :
    (∫ x, w x * densityL1 (PauliCurrent.pair u d) x) =
      ∑ n, ∫ X, w ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2 := by
  rw [PauliCurrent.density_eq hN]
  exact density_integral (PauliCurrent.wave u) w hi

end PfHk.PauliDensityWeighted

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
