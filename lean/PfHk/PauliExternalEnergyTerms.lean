import PfHk.PauliExternalEnergyPairing
import PfHk.PauliCurrentGroundState
import PfHk.PhysicalShiftedScalarEnergy
import PfHk.PhysicalDiamagneticPotential

/-! The physical configuration integrals in the spinful external energy. -/

attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

noncomputable section
namespace PfHk.PauliExternalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.PhysicalPolarization
  GptLean.SymmetricLift PfHk.PauliSpin PfHk.PauliCurrentAlgebra
  PfHk.PauliGroundState PfHk.PhysicalCommonFormDomain PfHk.PhysicalLocalEnergy
  PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 90000

attribute [local irreducible] referenceSubspace inclusion covariant radiation
  roughMultiply PauliReference.wave

variable {N : ℕ}

def components (u : Ref N) : PauliCurrent.Components (N := N) :=
  fun s => electronic (Fin N × Fin 3) (fun _ => 0) (u s)

theorem components_value (u : Ref N) (s : SpinIndex N) :
    ElectronicH1Complex.value (components u s) = inclusion (Fin N × Fin 3) (fun _ => 0) (u s) := by
  unfold components inclusion
  rfl

theorem components_wave (u : Ref N) : PauliCurrent.wave (components u) = PauliReference.wave u := by
  unfold PauliCurrent.wave PauliReference.wave
  exact congrArg FiniteFiberL2.bundle (funext (components_value u))

theorem components_norm_sq_ae (u : Ref N) :
    (fun X => ‖PauliCurrent.wave (components u) X‖ ^ 2) =ᵐ[volume]
      fun X => ∑ s, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
  unfold PauliCurrent.wave
  simp only [components_value]
  exact FiniteFiberL2.norm_sq_ae _

def scalarTerm (v : ScalarPotential) (u : Ref N) : ℝ :=
  ∑ s, PhysicalShiftedFormEnergy.scalarSum v (u s)

def squareTerm (A : VectorPotential) (u : Ref N) : ℝ :=
  ∑ s, PhysicalShiftedFormEnergy.squareSum A (u s)

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

def vectorTerm (A : VectorPotential) (u : Ref N) : ℝ :=
  ∑ n : Fin N, ∑ a : Fin 3, ∫ X, vector A (n, a) X *
    current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
      (fun b s => covariants C e F χ u (n, b) s X) a

theorem vector_term_integrable (A : VectorPotential) (u : Ref N) (n : Fin N) (a : Fin 3) :
    Integrable (fun X => vector A (n, a) X *
      current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariants C e F χ u (n, b) s X) a) volume :=
  PauliExternalEnergyLp.current_integrable n
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun b => covariants C e F χ u (n, b)) a (vector A (n, a))
    (fun s => (externalDomain A (0 : ScalarPotential) 0 le_rfl (u s)).vector (n, a))

theorem pairing_data_vector (hN : 0 < N) (A : VectorPotential) (u : Ref N) :
    PhysicalShiftedFormEnergy.vectorPairing A (data C e F χ u) = vectorTerm C e F χ A u := by
  have he (n : Fin N) (a : Fin 3) :
      (fun X => A.val (PhysicalSourceCoordinates.split n X).1 a *
        (inner ℂ (PauliCurrent.wave (components u) X)
          (PauliCurrent.pauliVelocity (covariants C e F χ u) n a X)).re) =ᵐ[volume]
      fun X => vector A (n, a) X * current n
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariants C e F χ u (n, b) s X) a := by
    have h := current_ae n (components u) (covariants C e F χ u) a
    simp only [components_value] at h
    exact h.mono fun X hX => congrArg (fun r : ℝ => vector A (n, a) X * r) hX
  have hi (n : Fin N) (a : Fin 3) :=
    (vector_term_integrable C e F χ A u n a).congr (he n a).symm
  exact (pairing_vector hN A (components u) (covariants C e F χ u) hi).trans
    (Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ => integral_congr_ae (he n a))

theorem scalar_wave_integrable (v : ScalarPotential) (u : Ref N) (n : Fin N) :
    Integrable (fun X => v.val (PhysicalSourceCoordinates.split n X).1 *
      ‖PauliCurrent.wave (components u) X‖ ^ 2) volume := by
  have h := integrable_finsetSum Finset.univ fun s _ =>
    PhysicalShiftedFormEnergy.scalar_integrable v n (u s)
  apply h.congr
  filter_upwards [components_norm_sq_ae u] with X hX
  change (∑ s, v.val (PhysicalSourceCoordinates.split n X).1 *
    ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) = _
  exact (Finset.mul_sum _ _ _).symm.trans
    (congrArg (fun r : ℝ => v.val (PhysicalSourceCoordinates.split n X).1 * r) hX.symm)

theorem pairing_data_scalar (hN : 0 < N) (v : ScalarPotential) (u : Ref N) :
    PhysicalShiftedFormEnergy.scalarPairing v (data C e F χ u) = scalarTerm v u := by
  have hrow (n : Fin N) :
      (∫ X, v.val (PhysicalSourceCoordinates.split n X).1 *
        ‖PauliCurrent.wave (components u) X‖ ^ 2) =
      ∑ s, ∫ X, CoordinateSobolev.coordinateCoefficient n
        (v.val : PhysicalSourceCoordinates.Position → ℝ) X *
          ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
    calc
      _ = ∫ X, ∑ s, v.val (PhysicalSourceCoordinates.split n X).1 *
          ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [components_norm_sq_ae u] with X hX
        exact (congrArg (fun r : ℝ => v.val (PhysicalSourceCoordinates.split n X).1 * r) hX).trans
          (Finset.mul_sum _ _ _)
      _ = _ := integral_finsetSum _ (fun s _ => PhysicalShiftedFormEnergy.scalar_integrable v n (u s))
  exact (pairing_scalar hN v (components u) (covariants C e F χ u)
    (scalar_wave_integrable v u)).trans
    ((Finset.sum_congr rfl (fun n _ => hrow n)).trans Finset.sum_comm)

theorem scalarTerm_shift (A : VectorPotential) (v : ScalarPotential) (u : Ref N) :
    scalarTerm (PhysicalDiamagneticPotential.shifted v A).1 u =
      scalarTerm v u + (1 / 2 : ℝ) * squareTerm A u := by
  unfold scalarTerm squareTerm
  simp only [PhysicalShiftedFormEnergy.scalarSum_shift A v
    (PhysicalDiamagneticPotential.shifted v A).1
    (PhysicalDiamagneticPotential.shifted_scalar_sum_ae v A),
    Finset.sum_add_distrib, ← Finset.mul_sum]

theorem pairing_data_shifted (hN : 0 < N) (A : VectorPotential) (v : ScalarPotential)
    (u : Ref N) :
    pairPotential (PhysicalDiamagneticPotential.shifted v A) (data C e F χ u) =
      scalarTerm v u + vectorTerm C e F χ A u + (1 / 2 : ℝ) * squareTerm A u := by
  change PhysicalShiftedFormEnergy.scalarPairing (PhysicalDiamagneticPotential.shifted v A).1
      (data C e F χ u) + PhysicalShiftedFormEnergy.vectorPairing A (data C e F χ u) = _
  rw [pairing_data_scalar C e F χ hN, pairing_data_vector C e F χ hN, scalarTerm_shift]
  ring

end PfHk.PauliExternalEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
