import PfHk.PauliExternalEnergyTerms

/-! The full physical Pauli energy has the manuscript's integrated
external-potential dependence on the actual spin-summed density-current pair. -/

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
set_option maxHeartbeats 100000

attribute [local irreducible] referenceSubspace inclusion covariant radiation
  roughMultiply PauliReference.wave ElectronicH1Space.value ElectronicH1Complex.value

private theorem sum_shift {I : Type*} [Fintype I]
    (k d j q : I → ℝ) (h : ∀ i, k i = d i + j i + (1 / 2 : ℝ) * q i) :
    (∑ i, k i) = (∑ i, d i) + (∑ i, j i) + (1 / 2 : ℝ) * ∑ i, q i := by
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem sum_difference {I : Type*} [Fintype I]
    (p n v w : I → ℝ) (h : ∀ i, p i - n i = v i + w i) :
    (∑ i, p i) - (∑ i, n i) = (∑ i, v i) + ∑ i, w i := by
  rw [← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_add_distrib]

private theorem integral_sum_add {X I : Type*} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} (f : I → X → ℝ) (g : X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ) :
    (∫ x, (∑ i, f i x) + g x ∂μ) = (∑ i, ∫ x, f i x ∂μ) + ∫ x, g x ∂μ := by
  exact (integral_add (integrable_finsetSum Finset.univ (fun i _ => hf i)) hg).trans
    (congrArg (fun r : ℝ => r + ∫ x, g x ∂μ) (integral_finsetSum Finset.univ (fun i _ => hf i)))

private theorem scalar_distribution {I : Type*} [Fintype I] (f : I → ℝ) (c r : ℝ) :
    ((∑ i, f i) + c) * r = (∑ i, f i * r) + c * r := by
  rw [add_mul, Finset.sum_mul]

private theorem energy_accounting (k j q r p n v w : ℝ) (h : p - n = v + w) :
    (k + j + (1 / 2 : ℝ) * q) + r + p - n =
      (k + r + w) + v + j + (1 / 2 : ℝ) * q := by
  linarith only [h]

variable {N : ℕ}

def coulombTerm (c : ℝ) (u : Ref N) : ℝ :=
  ∑ s, ∫ X, (c * PhysicalCoulombH1.potential N X) *
    ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2

theorem squareTerm_eq (A : VectorPotential) (u : Ref N) :
    squareTerm A u = ∑ n : Fin N, ∑ a : Fin 3, ∫ X,
      vector A (n, a) X ^ 2 *
        density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  have hrow (n : Fin N) (a : Fin 3) :
      (∑ s, ∫ X, vector A (n, a) X ^ 2 *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) =
      ∫ X, vector A (n, a) X ^ 2 *
        density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
    exact (integral_finsetSum _ (fun s _ =>
      PhysicalShiftedFormEnergy.square_integrable A (n, a) (u s))).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun X =>
        (Finset.mul_sum (s := Finset.univ)
          (f := fun s => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
          (vector A (n, a) X ^ 2)).symm))
  have hswap : squareTerm A u = ∑ q : Fin N × Fin 3, ∑ s, ∫ X,
      vector A q X ^ 2 * ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 :=
    Finset.sum_comm
  exact hswap.trans ((Fintype.sum_prod_type (fun q : Fin N × Fin 3 =>
      ∑ s, ∫ X, vector A q X ^ 2 *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)).trans
      (Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ => hrow n a))

theorem scalar_integral (v : ScalarPotential) (c : ℝ) (u : Ref N) (s : SpinIndex N) :
    (∫ X, scalar v c X * ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) =
      PhysicalShiftedFormEnergy.scalarSum v (u s) +
      ∫ X, (c * PhysicalCoulombH1.potential N X) *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
  have hi := PhysicalCoulombH1.scaled_potential_integrable (N := N) (H := PhotonFock) c
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) (u s)))
  have hv : ElectronicH1Space.value (E := PhotonFock) (I := Fin N × Fin 3)
      (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
        (electronic (Fin N × Fin 3) (fun _ => 0) (u s))) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) :=
    (ElectronicH1Complex.value_realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) (u s))).trans (components_value u s)
  have hi' := (congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
    Integrable (fun X => (c * PhysicalCoulombH1.potential N X) * ‖w X‖ ^ 2) volume) hv).mp hi
  have he : (fun X => scalar v c X *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) =ᵐ[volume]
      fun X => (∑ n : Fin N, CoordinateSobolev.coordinateCoefficient n
        (v.val : PhysicalSourceCoordinates.Position → ℝ) X *
          ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) +
        (c * PhysicalCoulombH1.potential N X) *
          ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 :=
    Filter.Eventually.of_forall fun X => scalar_distribution
      (fun n : Fin N => CoordinateSobolev.coordinateCoefficient n
        (v.val : PhysicalSourceCoordinates.Position → ℝ) X)
      (c * PhysicalCoulombH1.potential N X)
      (‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
  exact (integral_congr_ae he).trans (integral_sum_add
    (fun n : Fin N => fun X => CoordinateSobolev.coordinateCoefficient n
      (v.val : PhysicalSourceCoordinates.Position → ℝ) X *
        ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    (fun X => (c * PhysicalCoulombH1.potential N X) *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2)
    (fun n => PhysicalShiftedFormEnergy.scalar_integrable v n (u s)) hi')

theorem scalar_energy (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) :
    (∑ s, ‖roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).positive)‖ ^ 2) -
      (∑ s, ‖roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        ((physicalDomain A v c hc u s).negative)‖ ^ 2) =
      scalarTerm v u + coulombTerm c u := by
  have hs (s : SpinIndex N) :
      ‖roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        ((physicalDomain A v c hc u s).positive)‖ ^ 2 -
      ‖roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        ((physicalDomain A v c hc u s).negative)‖ ^ 2 =
      PhysicalShiftedFormEnergy.scalarSum v (u s) +
        ∫ X, (c * PhysicalCoulombH1.potential N X) *
          ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2 := by
    unfold roughMultiply
    exact (PhysicalShiftedFormEnergyLp.signed_multiplier_difference
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (positive v c) (negative v c) (scalar v c)
      ((physicalDomain A v c hc u s).positive) ((physicalDomain A v c hc u s).negative)
      (Filter.Eventually.of_forall fun X =>
        SignedScalarMultiplier.amplitude_difference (scalar v c) X)).trans (scalar_integral v c u s)
  exact sum_difference
    (fun s => ‖roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).positive)‖ ^ 2)
    (fun s => ‖roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).negative)‖ ^ 2)
    (fun s => PhysicalShiftedFormEnergy.scalarSum v (u s))
    (fun s => ∫ X, (c * PhysicalCoulombH1.potential N X) *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X‖ ^ 2) hs

variable (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (F : Frame) (χ : ArticleCutoff)

def intrinsicEnergy (c : ℝ) (u : Ref N) : ℝ :=
  (∑ n, kinetic n (fun a => covariants C e F χ u (n, a))) +
    (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) + coulombTerm c u

theorem kinetic_expansion (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) (n : Fin N) :
    kinetic n (fun a => rawCovariant C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      u (physicalDomain A v c hc u) (n, a)) =
    kinetic n (fun a => covariants C e F χ u (n, a)) +
      (∑ a, ∫ X, vector A (n, a) X * current n
        (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariants C e F χ u (n, b) s X) a) +
      (1 / 2 : ℝ) * ∑ a, ∫ X, vector A (n, a) X ^ 2 *
        density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  apply PauliExternalEnergyLp.integrated_kinetic_shift n
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun a => covariants C e F χ u (n, a))
    (fun a => rawCovariant C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
      u (physicalDomain A v c hc u) (n, a)) (fun a => vector A (n, a))
    (fun a s => (physicalDomain A v c hc u s).vector (n, a))
  intro a s
  exact (Lp.coeFn_add
    (covariants C e F χ u (n, a) s)
    (roughMultiply (vector A (n, a)) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).vector (n, a)))).trans
    ((roughMultiply_ae (vector A (n, a))
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).vector (n, a))).mono fun X hX =>
        congrArg (fun z : PhotonFock => covariants C e F χ u (n, a) s X + z)
          (hX.trans (Complex.coe_smul _ _).symm))

theorem energy_expansion (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)
    (u : Ref N) :
    energy C e F χ A v c hc u = intrinsicEnergy C e F χ c u +
      scalarTerm v u + vectorTerm C e F χ A u + (1 / 2 : ℝ) * squareTerm A u := by
  let d := fun n a => rawCovariant C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
    u (physicalDomain A v c hc u) (n, a)
  let k := ∑ n, kinetic n (fun a => covariants C e F χ u (n, a))
  let j := fun n => ∑ a, ∫ X, vector A (n, a) X * current n
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
    (fun b s => covariants C e F χ u (n, b) s X) a
  let q := fun n => ∑ a, ∫ X, vector A (n, a) X ^ 2 *
    density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
  have hk := sum_shift (fun n => kinetic n (d n))
    (fun n => kinetic n (fun a => covariants C e F χ u (n, a))) j q
    (fun n => kinetic_expansion C e F χ A v c hc u n)
  have hkin : (1 / 2 : ℝ) * ∑ n, ∑ s,
      ‖rawContraction C (profile F χ 0) (profile_measurable F χ 0)
        (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
        u (physicalDomain A v c hc u) n s‖ ^ 2 = ∑ n, kinetic n (d n) :=
    Finset.mul_sum _ _ _
  have hsq : (∑ n, q n) = squareTerm A u := (squareTerm_eq A u).symm
  have hk' := hkin.trans (hk.trans
    (congrArg (fun r : ℝ => k + vectorTerm C e F χ A u + (1 / 2 : ℝ) * r) hsq))
  have he := rawEnergy_eq C (profile F χ 0) (profile_measurable F χ 0)
    (profileBound F χ) (profile_bound F χ 0) e (vector A) (positive v c) (negative v c)
    u (physicalDomain A v c hc u)
  change energy C e F χ A v c hc u = _ at he
  have hs := scalar_energy A v c hc u
  exact he.trans ((congrArg (fun t : ℝ => t +
    (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
    (∑ s, ‖roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).positive)‖ ^ 2) -
    ∑ s, ‖roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((physicalDomain A v c hc u s).negative)‖ ^ 2) hk').trans
    (energy_accounting k (vectorTerm C e F χ A u) (squareTerm A u) _ _ _
      (scalarTerm v u) (coulombTerm c u) hs))

theorem energy_decomposition (hN : 0 < N) (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref N) :
    energy C e F χ A v c hc u = intrinsicEnergy C e F χ c u +
      pairPotential (PhysicalDiamagneticPotential.shifted v A) (data C e F χ u) := by
  rw [energy_expansion C e F χ A v c hc u, pairing_data_shifted C e F χ hN A v u]
  ring

end PfHk.PauliExternalEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
