import PfHk.SpinfulCounterexampleMagneticEnergy
import PfHk.SpinfulCounterexamplePotentials
import PfHk.PauliZeroCouplingEnergy

/-! Identification of the actual Pauli energy with the two electronic
spin blocks and the nonnegative photon energy, on every reference spinor. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.SpinfulCounterexamplePhysicalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliExternalEnergy
  PfHk.CenteredPhysicalReference PfHk.SpinfulCounterexampleState
  PfHk.SpinfulCounterexampleSpectral

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
attribute [local irreducible] referenceSubspace inclusion ordinary radiation covariant
  ElectronicH1Complex.value ElectronicH1Complex.derivative

abbrev Index := Fin 1 × Fin 3
abbrev OrbitalRef := PhysicalOneParticleState.Ref

/-! Scalar integral algebra on abstract real functions. Instantiating these
once avoids rewriting inside the physical reference terms. -/

private theorem integral_mul_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b c n : α → ℝ) (hab : ∀ᵐ x ∂μ, a x = b x + c x)
    (hb : Integrable (fun x => b x * n x) μ) (hc : Integrable (fun x => c x * n x) μ) :
    (∫ x, a x * n x ∂μ) = (∫ x, b x * n x ∂μ) + ∫ x, c x * n x ∂μ := by
  rw [← integral_add hb hc]
  refine integral_congr_ae ?_
  filter_upwards [hab] with x hx
  rw [hx, add_mul]

private theorem integral_mul_scaled {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b n : α → ℝ) (t : ℝ) (hab : ∀ᵐ x ∂μ, a x = t * b x) :
    (∫ x, a x * n x ∂μ) = t * ∫ x, b x * n x ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hab] with x hx
  rw [hx, mul_assoc]

private theorem integral_scaled {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b c : α → ℝ) (t : ℝ) (h : ∀ᵐ x ∂μ, a x * b x = t * c x) :
    (∫ x, a x * b x ∂μ) = t * ∫ x, c x ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae h

private theorem scalarSum_add (v w : ScalarPotential) (u : OrbitalRef) :
    PhysicalShiftedFormEnergy.scalarSum (v + w) u =
      PhysicalShiftedFormEnergy.scalarSum v u + PhysicalShiftedFormEnergy.scalarSum w u := by
  have hab : ∀ᵐ X ∂volume, CoordinateSobolev.coordinateCoefficient (0 : Fin 1)
      ((v + w).val : PhysicalSourceCoordinates.Position → ℝ) X =
      CoordinateSobolev.coordinateCoefficient 0 (v.val : PhysicalSourceCoordinates.Position → ℝ) X +
      CoordinateSobolev.coordinateCoefficient 0
        (w.val : PhysicalSourceCoordinates.Position → ℝ) X := by
    filter_upwards [ScalarCoordinateFormBound.coordinate_ae (N := 1) (0 : Fin 1)
      (AEEqFun.coeFn_add v.val w.val)] with X hX
    exact hX
  have h := integral_mul_add _ _ _ (fun X => ‖inclusion Index (fun _ => 0) u X‖ ^ 2) hab
    (PhysicalShiftedFormEnergy.scalar_integrable v 0 u)
    (PhysicalShiftedFormEnergy.scalar_integrable w 0 u)
  unfold PhysicalShiftedFormEnergy.scalarSum
  simp only [Fin.sum_univ_one]
  exact h

private theorem scalarSum_zeeman (t : ℝ) (u : OrbitalRef) :
    PhysicalShiftedFormEnergy.scalarSum (SpinfulCounterexamplePotentials.zeeman t) u =
      t * upWeight (electronic Index (fun _ => 0) u) := by
  have hw : upWeight (electronic Index (fun _ => 0) u) =
      ∫ X, SpinfulCounterexampleField.weight (SymmetricLift.particle X 0) ^ 2 *
        ‖inclusion Index (fun _ => 0) u X‖ ^ 2 := by
    unfold upWeight
    exact congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index =>
      ∫ X, SpinfulCounterexampleField.weight (SymmetricLift.particle X 0) ^ 2 * ‖w X‖ ^ 2)
      (CounterexamplePhysicalEnergy.value_electronic u)
  have hab : ∀ᵐ X ∂volume, CoordinateSobolev.coordinateCoefficient (0 : Fin 1)
      ((SpinfulCounterexamplePotentials.zeeman t).val : PhysicalSourceCoordinates.Position → ℝ) X =
      t * SpinfulCounterexampleField.weight (SymmetricLift.particle X 0) ^ 2 := by
    filter_upwards [ScalarCoordinateFormBound.coordinate_ae (N := 1) (0 : Fin 1)
      (SpinfulCounterexamplePotentials.zeeman_ae t)] with X hX
    exact hX
  have h := integral_mul_scaled _ _ (fun X => ‖inclusion Index (fun _ => 0) u X‖ ^ 2) t hab
  unfold PhysicalShiftedFormEnergy.scalarSum
  simp only [Fin.sum_univ_one]
  exact h.trans (congrArg (fun r : ℝ => t * r) hw.symm)

variable (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff)

private theorem current_ae (u : Ref 1) (j : Fin 3) :
    (fun X => PauliCurrentAlgebra.current 0
      (fun s => inclusion Index (fun _ => 0) (u s) X)
      (fun b s => covariants C 0 F χ u (0,b) s X) j) =ᵐ[volume]
    fun X => PauliBoundedMagneticPairing.current (components u) 0 j X := by
  have hd (b : Fin 3) (s : SpinIndex 1) :=
    Lp.coeFn_smul (-Complex.I) (ordinary Index (fun _ => 0) (0,b) (u s))
  filter_upwards [ae_all_iff.mpr (fun b => ae_all_iff.mpr (hd b))] with X hX
  have hcov : (fun b s => covariants C 0 F χ u (0,b) s X) =
      fun b s => (-Complex.I) • ordinary Index (fun _ => 0) (0,b) (u s) X :=
    funext fun b => funext fun s =>
      (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
        (PauliZeroCouplingEnergy.covariants_zero C F χ u (0,b) s)).trans (hX b s)
  have hval : (fun s => inclusion Index (fun _ => 0) (u s) X) =
      fun s => ElectronicH1Complex.value (components u s) X :=
    funext fun s => (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
      (components_value u s)).symm
  have hder : (fun b s => (-Complex.I) • ordinary Index (fun _ => 0) (0,b) (u s) X) =
      fun b s => (-Complex.I) • ElectronicH1Complex.derivative (0,b) (components u s) X :=
    funext fun b => funext fun s =>
      (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => (-Complex.I) • w X)
        (CounterexamplePhysicalEnergy.derivative_electronic (u s) (0,b))).symm
  exact congrArg₂ (fun (v : SpinIndex 1 → PhotonFock) (w : Fin 3 → SpinIndex 1 → PhotonFock) =>
    PauliCurrentAlgebra.current (0 : Fin 1) v w j) hval (hcov.trans hder)

/-- The spin term comes from integrating the actual Pauli current, not
from inserting a separate magnetic-energy assumption. -/
theorem vectorTerm (t : ℝ) (u : Ref 1) :
    PauliExternalEnergy.vectorTerm C 0 F χ (SpinfulCounterexamplePotentials.vector t) u =
      t * (rotationForm (components u up) + rotationForm (components u down) +
        upWeight (components u up) - upWeight (components u down)) := by
  have hrow (j : Fin 3) :
      (∫ X, PhysicalCommonFormDomain.vector (SpinfulCounterexamplePotentials.vector t) (0,j) X *
        PauliCurrentAlgebra.current 0 (fun s => inclusion Index (fun _ => 0) (u s) X)
          (fun b s => covariants C 0 F χ u (0,b) s X) j) =
      t * ∫ X, SpinfulCounterexampleField.field (position X) j *
        PauliBoundedMagneticPairing.current (components u) 0 j X := by
    refine integral_scaled _ _ _ t ?_
    filter_upwards [ScalarCoordinateFormBound.coordinate_ae (N := 1) (0 : Fin 1)
      (SpinfulCounterexamplePotentials.vector_ae t), current_ae C F χ u j] with X hA hj
    have ha : PhysicalCommonFormDomain.vector (SpinfulCounterexamplePotentials.vector t) (0,j) X =
        t * SpinfulCounterexampleField.field (position X) j :=
      congrArg (fun x : SpinfulCounterexampleField.Space => x j) hA
    exact (congrArg₂ (· * ·) ha hj).trans (mul_assoc _ _ _)
  have hv : PauliExternalEnergy.vectorTerm C 0 F χ (SpinfulCounterexamplePotentials.vector t) u =
      ∑ j : Fin 3, ∫ X,
        PhysicalCommonFormDomain.vector (SpinfulCounterexamplePotentials.vector t) (0,j) X *
        PauliCurrentAlgebra.current 0 (fun s => inclusion Index (fun _ => 0) (u s) X)
          (fun b s => covariants C 0 F χ u (0,b) s X) j := by
    unfold PauliExternalEnergy.vectorTerm
    exact Fin.sum_univ_one _
  exact hv.trans ((Finset.sum_congr rfl fun j _ => hrow j).trans ((Finset.mul_sum _ _ _).symm.trans
    (congrArg (fun x : ℝ => t * x)
      (SpinfulCounterexampleMagneticEnergy.current_pairing (components u)))))

/-- The scalar pairing: Coulomb attraction plus the compensating Zeeman term. -/
theorem scalarTerm_eq (Z t : ℝ) (u : Ref 1) :
    PauliExternalEnergy.scalarTerm (PhysicalDiamagneticPotential.shifted
      (SpinfulCounterexamplePotentials.scalar Z t) (SpinfulCounterexamplePotentials.vector t)).1 u =
      (-Z * CounterexampleSpectral.coulomb (components u up) + t * upWeight (components u up)) +
      (-Z * CounterexampleSpectral.coulomb (components u down) +
        t * upWeight (components u down)) := by
  have hshift : (PhysicalDiamagneticPotential.shifted (SpinfulCounterexamplePotentials.scalar Z t)
      (SpinfulCounterexamplePotentials.vector t)).1 =
      SpinfulCounterexamplePotentials.coulomb Z + SpinfulCounterexamplePotentials.zeeman t :=
    congrArg Prod.fst (SpinfulCounterexamplePotentials.shifted_eq Z t)
  have hrow (s : SpinIndex 1) :
      PhysicalShiftedFormEnergy.scalarSum
        (SpinfulCounterexamplePotentials.coulomb Z + SpinfulCounterexamplePotentials.zeeman t) (u s) =
      -Z * CounterexampleSpectral.coulomb (components u s) + t * upWeight (components u s) :=
    (scalarSum_add _ _ (u s)).trans (congrArg₂ (· + ·)
      (CounterexamplePhysicalEnergy.scalarSum Z (u s)) (scalarSum_zeeman t (u s)))
  calc
    _ = ∑ s, PhysicalShiftedFormEnergy.scalarSum
        (SpinfulCounterexamplePotentials.coulomb Z + SpinfulCounterexamplePotentials.zeeman t) (u s) :=
      (congrArg (fun v => PauliExternalEnergy.scalarTerm v u) hshift).trans rfl
    _ = ∑ s, (-Z * CounterexampleSpectral.coulomb (components u s) +
        t * upWeight (components u s)) := Finset.sum_congr rfl fun s _ => hrow s
    _ = _ := sum_spin _

/-- The exact global physical energy identity for the cylindrical family. -/
theorem energy (Z t c : ℝ) (hc : 0 ≤ c) (u : Ref 1) :
    PauliGroundState.energy C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc u =
      spinEnergy Z t (components u up) (components u down) +
        ‖radiation Index (fun _ => 0) (u up)‖ ^ 2 +
        ‖radiation Index (fun _ => 0) (u down)‖ ^ 2 := by
  have h1 := PauliZeroCouplingEnergy.energy_one C F χ (SpinfulCounterexamplePotentials.vector t)
    (SpinfulCounterexamplePotentials.scalar Z t) c hc u
  have hK : (∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s))) =
      CounterexampleSpectral.kinetic (components u up) +
        CounterexampleSpectral.kinetic (components u down) :=
    sum_spin (fun s => CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s)))
  have hR : (∑ s, ‖radiation Index (fun _ => 0) (u s)‖ ^ 2) =
      ‖radiation Index (fun _ => 0) (u up)‖ ^ 2 + ‖radiation Index (fun _ => 0) (u down)‖ ^ 2 :=
    sum_spin (fun s => ‖radiation Index (fun _ => 0) (u s)‖ ^ 2)
  have hS := scalarTerm_eq Z t u
  have hV := vectorTerm C F χ t u
  have hE : spinEnergy Z t (components u up) (components u down) =
      (CounterexampleSpectral.kinetic (components u up) -
        Z * CounterexampleSpectral.coulomb (components u up)) +
      (CounterexampleSpectral.kinetic (components u down) -
        Z * CounterexampleSpectral.coulomb (components u down)) +
      t * (rotationForm (components u up) + rotationForm (components u down)) +
      2 * t * upWeight (components u up) := rfl
  linarith

end PfHk.SpinfulCounterexamplePhysicalEnergy
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
