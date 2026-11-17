import PfHk.PauliExternalEnergyLp
import PfHk.PhysicalShiftedFormEnergyBase

/-! Unbounded scalar and vector tests of all spin-summed particle marginals. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliExternalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.PhysicalSourceCoordinates
  PfHk.PauliSpin PfHk.PauliCurrentAlgebra PfHk.PhysicalShiftedFormEnergy
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 80000

variable {N : ℕ}
attribute [local irreducible] ElectronicH1Complex.value PauliCurrent.source
  PauliCurrent.wave PauliCurrent.pauliVelocity PhysicalPFReference.referenceSubspace

theorem current_ae (n : Fin N) (u : PauliCurrent.Components (N := N))
    (d : PauliCurrent.Derivatives (N := N)) (a : Fin 3) :
    (fun X => (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re) =ᵐ[volume]
      fun X => current n (fun s => ElectronicH1Complex.value (u s) X)
        (fun b s => d (n, b) s X) a := by
  unfold PauliCurrent.wave PauliCurrent.pauliVelocity
  exact PauliExternalEnergyLp.bundle_current_ae (N := N)
    (X := GptLean.SymmetricLift.Configuration N) (H := PhotonFock) n
    (fun s => ElectronicH1Complex.value (u s)) (fun b => d (n, b)) a

theorem scalar_particle_pairing (v : ScalarPotential) (n : Fin N)
    (u : PauliCurrent.Components (N := N)) (d : PauliCurrent.Derivatives (N := N))
    (hi : Integrable (fun X => v.val ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2) volume) :
    scalarPairing v (PauliCurrent.particlePair n u d) =
      (N : ℝ) * ∫ X, v.val ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2 := by
  have hs := PauliCurrent.source_value u
  have hsi : Integrable (fun X => v.val ((split n) X).1 *
      ‖ElectronicH1Space.value (PauliCurrent.source u) X‖ ^ 2) volume :=
    (congrArg (fun w : PauliCurrent.Wave (N := N) =>
      Integrable (fun X => v.val ((split n) X).1 * ‖w X‖ ^ 2) volume) hs).mpr hi
  exact (scalarPairing_eq_integral v (PauliCurrent.particlePair n u d)).trans
    ((PhysicalShiftedFormEnergyFubini.density_ofWaveFunction (N := N) (H := Fiber N PhotonFock) n (PauliCurrent.source u)
      (fun a => PauliCurrent.pauliVelocity d n a) (v.val : PhysicalSourceCoordinates.Position → ℝ) hsi).trans
      (congrArg (fun w : PauliCurrent.Wave (N := N) =>
        (N : ℝ) * ∫ X, v.val ((split n) X).1 * ‖w X‖ ^ 2) hs))

theorem vector_particle_pairing (A : VectorPotential) (n : Fin N)
    (u : PauliCurrent.Components (N := N)) (d : PauliCurrent.Derivatives (N := N))
    (hi : ∀ a, Integrable (fun X => A.val ((split n) X).1 a *
      (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re) volume) :
    vectorPairing A (PauliCurrent.particlePair n u d) =
      (N : ℝ) * ∑ a, ∫ X, A.val ((split n) X).1 a *
        (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re := by
  have hs := PauliCurrent.source_value u
  have hrow (a : Fin 3) :
      (∫ x, A.val x a * currentL1 (PauliCurrent.particlePair n u d) x a) =
        (N : ℝ) * ∫ X, A.val ((split n) X).1 a *
          (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re := by
    have hsi : Integrable (fun X => A.val ((split n) X).1 a *
        (inner ℂ (ElectronicH1Space.value (PauliCurrent.source u) X)
          (PauliCurrent.pauliVelocity d n a X)).re) volume :=
      (congrArg (fun w : PauliCurrent.Wave (N := N) =>
        Integrable (fun X => A.val ((split n) X).1 a *
          (inner ℂ (w X) (PauliCurrent.pauliVelocity d n a X)).re) volume) hs).mpr (hi a)
    exact (PhysicalShiftedFormEnergyFubini.current_ofWaveFunction (N := N) (H := Fiber N PhotonFock) n (PauliCurrent.source u)
      (fun b => PauliCurrent.pauliVelocity d n b) a (fun x => A.val x a) hsi).trans
      (congrArg (fun w : PauliCurrent.Wave (N := N) =>
        (N : ℝ) * ∫ X, A.val ((split n) X).1 a *
          (inner ℂ (w X) (PauliCurrent.pauliVelocity d n a X)).re) hs)
  exact (vectorPairing_eq_sum_integrals A (PauliCurrent.particlePair n u d)).trans
    ((Finset.sum_congr rfl (fun a _ => hrow a)).trans (Finset.mul_sum _ _ _).symm)

private theorem average_apply (hN : 0 < N) (L : Pair →L[ℝ] ℝ)
    (P : Fin N → Pair) (f : Fin N → ℝ) (h : ∀ n, L (P n) = (N : ℝ) * f n) :
    L ((N : ℝ)⁻¹ • ∑ n, P n) = ∑ n, f n := by
  rw [map_smul, map_sum]
  simp only [h, smul_eq_mul, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_mul]

theorem pairing_scalar (hN : 0 < N) (v : ScalarPotential)
    (u : PauliCurrent.Components (N := N)) (d : PauliCurrent.Derivatives (N := N))
    (hi : ∀ n, Integrable (fun X => v.val ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2) volume) :
    scalarPairing v (PauliCurrent.pair u d) =
      ∑ n, ∫ X, v.val ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2 := by
  let L : Pair →L[ℝ] ℝ :=
    (pairing (α := PhysicalSourceCoordinates.Position) (E := ℝ) (μ := volume)
      (p := (3 : ℝ≥0∞)) (q := (3 / 2 : ℝ≥0∞)) v).comp (ContinuousLinearMap.fst ℝ _ _)
  exact average_apply hN L (fun n => PauliCurrent.particlePair n u d)
    (fun n => ∫ X, v.val ((split n) X).1 * ‖PauliCurrent.wave u X‖ ^ 2)
    (fun n => scalar_particle_pairing v n u d (hi n))

theorem pairing_vector (hN : 0 < N) (A : VectorPotential)
    (u : PauliCurrent.Components (N := N)) (d : PauliCurrent.Derivatives (N := N))
    (hi : ∀ n a, Integrable (fun X => A.val ((split n) X).1 a *
      (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re) volume) :
    vectorPairing A (PauliCurrent.pair u d) =
      ∑ n, ∑ a, ∫ X, A.val ((split n) X).1 a *
        (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re := by
  let L : Pair →L[ℝ] ℝ :=
    (pairing (α := PhysicalSourceCoordinates.Position) (E := PhysicalPairSpace.Vector) (μ := volume)
      (p := (3 / 2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞)) A).comp (ContinuousLinearMap.snd ℝ _ _)
  exact average_apply hN L (fun n => PauliCurrent.particlePair n u d)
    (fun n => ∑ a, ∫ X, A.val ((split n) X).1 a *
      (inner ℂ (PauliCurrent.wave u X) (PauliCurrent.pauliVelocity d n a X)).re)
    (fun n => vector_particle_pairing A n u d (hi n))

end PfHk.PauliExternalEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
