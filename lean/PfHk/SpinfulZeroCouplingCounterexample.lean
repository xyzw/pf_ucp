import PfHk.SpinfulCounterexamplePhysicalEnergy
import PfHk.SpinfulCounterexampleData
import PfHk.SpinfulCounterexampleRegularity
import PfHk.PhysicalReferenceVacuum

/-! The actual one-electron Pauli counterexample at zero photon coupling,
`prop-spinful-zero-coupling-counterexample` in `pf_ucp.tex`.
The ground-state lower bound and uniqueness follow from the checked
physical energy identity and the cylindrical angular estimate. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.SpinfulZeroCouplingCounterexample

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PauliExternalEnergy PfHk.SpinfulCounterexampleState
  PfHk.SpinfulCounterexampleSpectral

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
local instance referenceAddCommGroup : AddCommGroup (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := 1)
local instance referenceModule : Module ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := 1)
local instance referenceSMul : SMul ℂ (Reference (Fin 1 × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := 1)
local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  CounterexampleSpectral.photonRealInner
attribute [local irreducible] referenceSubspace inclusion electronic ordinary radiation
  ElectronicH1Complex.value ElectronicH1Complex.derivative

abbrev Index := Fin 1 × Fin 3

/-! The spin-up block of the proposed state vanishes. -/

private theorem lp_zero_ae : ∀ᵐ X ∂(volume : Measure CounterexampleSpectral.Space),
    (0 : ElectronicH1Space.L2 PhotonFock Index) X = 0 := by
  filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure CounterexampleSpectral.Space)]
    with X hX
  exact hX

private theorem kinetic_zero :
    CounterexampleSpectral.kinetic (0 : CounterexampleSpectral.Electronic) = 0 := by
  unfold CounterexampleSpectral.kinetic
  simp

private theorem coulomb_zero :
    CounterexampleSpectral.coulomb (0 : CounterexampleSpectral.Electronic) = 0 := by
  unfold CounterexampleSpectral.coulomb
  simp only [map_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [lp_zero_ae] with X hX
  rw [hX]
  simp

private theorem rotationForm_zero : rotationForm (0 : CounterexampleSpectral.Electronic) = 0 := by
  unfold rotationForm
  simp only [map_zero]
  apply Finset.sum_eq_zero
  intro j _
  apply integral_eq_zero_of_ae
  filter_upwards [lp_zero_ae] with X hX
  rw [hX]
  simp

private theorem upWeight_zero : upWeight (0 : CounterexampleSpectral.Electronic) = 0 := by
  unfold upWeight
  simp only [map_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [lp_zero_ae] with X hX
  rw [hX]
  simp

private theorem spinEnergy_zero_up (Z t : ℝ) (down : CounterexampleSpectral.Electronic) :
    spinEnergy Z t 0 down =
      (CounterexampleSpectral.kinetic down - Z * CounterexampleSpectral.coulomb down) +
        t * rotationForm down := by
  have h : spinEnergy Z t 0 down =
      (CounterexampleSpectral.kinetic 0 - Z * CounterexampleSpectral.coulomb 0) +
      (CounterexampleSpectral.kinetic down - Z * CounterexampleSpectral.coulomb down) +
      t * (rotationForm 0 + rotationForm down) + 2 * t * upWeight 0 := rfl
  simp only [kinetic_zero, coulomb_zero, rotationForm_zero, upWeight_zero, mul_zero, sub_zero,
    zero_add, add_zero] at h
  linarith

/-- The radial hydrogen orbital carries no cylindrical angular momentum. -/
private theorem hydrogen_rotation (Z : ℝ) (hZ : 0 < Z) :
    rotationForm (electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ)) = 0 := by
  unfold rotationForm
  apply Finset.sum_eq_zero
  intro j _
  apply integral_eq_zero_of_ae
  filter_upwards [CounterexampleVacuumState.reference_current Z hZ j] with X hX
  have hv : ElectronicH1Complex.value
      (electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ)) X =
      inclusion Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ) X :=
    congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
      (CounterexamplePhysicalEnergy.value_electronic _)
  have hd : ElectronicH1Complex.derivative (0, j)
      (electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ)) X =
      ordinary Index (fun _ => 0) (0, j) (CounterexampleVacuumState.reference Z hZ) X :=
    congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
      (CounterexamplePhysicalEnergy.derivative_electronic _ (0, j))
  have hre := (congrArg₂ (fun (a b : PhotonFock) => (inner ℂ a ((-Complex.I) • b)).re) hv hd).trans hX
  exact (congrArg (fun r : ℝ => SpinfulCounterexampleField.field (position X) j * r) hre).trans
    (mul_zero _)

private theorem normalization (p : State 1) :
    ‖ElectronicH1Complex.value (components p.vector up)‖ ^ 2 +
      ‖ElectronicH1Complex.value (components p.vector down)‖ ^ 2 = 1 := by
  simpa only [normSquared, sum_spin, components_value] using p.normalized

private theorem norm_eq_one_of_sq {E : Type*} [NormedAddCommGroup E] (x : E)
    (h : ‖x‖ ^ 2 = 1) : ‖x‖ = 1 := by
  have h0 := norm_nonneg x
  nlinarith

variable (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff)

/-- Direct evaluation of the actual Pauli form on the fixed hydrogen-vacuum spinor. -/
theorem state_energy (Z : ℝ) (hZ : 0 < Z) (t c : ℝ) (hc : 0 ≤ c) :
    energy C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc (state Z hZ).vector = -(Z ^ 2 / 2) := by
  have he := SpinfulCounterexamplePhysicalEnergy.energy C F χ Z t c hc (state Z hZ).vector
  have hup : components (state Z hZ).vector up = 0 := by
    simp only [components, state_vector, reference_up, map_zero]
  have hdown : components (state Z hZ).vector down =
      electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ) := by
    simp only [components, state_vector, reference_down]
  have hrup : ‖radiation Index (fun _ => 0) ((state Z hZ).vector up)‖ ^ 2 = 0 := by
    simp [state_vector, reference_up]
  have hrdown : ‖radiation Index (fun _ => 0) ((state Z hZ).vector down)‖ ^ 2 = 0 := by
    simp [state_vector, reference_down, CounterexampleVacuumState.reference_radiation]
  have hE := CounterexampleVacuumState.reference_electronic_energy Z hZ 0
  unfold CounterexampleSpectral.electronicEnergy at hE
  have h1 := spinEnergy_zero_up Z t
    (electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ))
  have h2 := congrArg₂ (spinEnergy Z t) hup hdown
  have h3 : t * rotationForm
      (electronic Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ)) = 0 :=
    (congrArg (fun r : ℝ => t * r) (hydrogen_rotation Z hZ)).trans (mul_zero t)
  linarith

/-- Every normalized physical spinor obeys the common hydrogenic lower bound. -/
theorem energy_lower_bound (D : StandardCylindricalDecomposition)
    (Z : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (c : ℝ) (hc : 0 ≤ c) (p : State 1) :
    -(Z ^ 2 / 2) ≤ energy C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc p.vector := by
  have hn := normalization p
  have hl := spin_energy_lower_bound D Z ht0 ht1 (components p.vector up)
    (components p.vector down)
  rw [hn, mul_one] at hl
  have he := SpinfulCounterexamplePhysicalEnergy.energy C F χ Z t c hc p.vector
  have h1 := sq_nonneg ‖radiation Index (fun _ => 0) (p.vector up)‖
  have h2 := sq_nonneg ‖radiation Index (fun _ => 0) (p.vector down)‖
  linarith

/-- The fixed spin-down hydrogen-vacuum vector minimizes the actual Pauli energy. -/
theorem ground_state (D : StandardCylindricalDecomposition)
    (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    (c : ℝ) (hc : 0 ≤ c) :
    IsGroundState C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc (state Z hZ) := by
  intro p
  exact (state_energy C F χ Z hZ t c hc).le.trans
    (energy_lower_bound C F χ D Z ht0.le ht1.le c hc p)

/-- At a minimizer the electronic spin blocks attain the hydrogenic level
and the down-spin radiation vanishes. -/
private theorem minimizer_parts (D : StandardCylindricalDecomposition)
    (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    (c : ℝ) (hc : 0 ≤ c) (p : State 1)
    (hp : IsGroundState C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc p) :
    spinEnergy Z t (components p.vector up) (components p.vector down) =
      -(Z ^ 2 / 2) *
        (‖ElectronicH1Complex.value (components p.vector up)‖ ^ 2 +
          ‖ElectronicH1Complex.value (components p.vector down)‖ ^ 2) ∧
    radiation Index (fun _ => 0) (p.vector down) = 0 := by
  have hn := normalization p
  have hupper := (hp (state Z hZ)).trans_eq (state_energy C F χ Z hZ t c hc)
  have he0 := SpinfulCounterexamplePhysicalEnergy.energy C F χ Z t c hc p.vector
  have hl := spin_energy_lower_bound D Z ht0.le ht1.le (components p.vector up)
    (components p.vector down)
  rw [hn, mul_one] at hl
  have hrup := sq_nonneg ‖radiation Index (fun _ => 0) (p.vector up)‖
  have hrdown := sq_nonneg ‖radiation Index (fun _ => 0) (p.vector down)‖
  refine ⟨?_, ?_⟩
  · rw [hn, mul_one]
    linarith only [hupper, he0, hl, hrup, hrdown]
  · have hz : ‖radiation Index (fun _ => 0) (p.vector down)‖ ^ 2 = 0 := by
      linarith only [hupper, he0, hl, hrup, hrdown]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz)

/-- The spectral equality case removes spin up and leaves a normalized
hydrogenic orbital times a fixed photon vector. -/
private theorem minimizer_spin_down (D : StandardCylindricalDecomposition)
    (S : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) (p : State 1)
    (he : spinEnergy Z t (components p.vector up) (components p.vector down) =
      -(Z ^ 2 / 2) *
        (‖ElectronicH1Complex.value (components p.vector up)‖ ^ 2 +
          ‖ElectronicH1Complex.value (components p.vector down)‖ ^ 2)) :
    p.vector up = 0 ∧ ‖inclusion Index (fun _ => 0) (p.vector down)‖ = 1 ∧
      ∃ v : PhotonFock, inclusion Index (fun _ => 0) (p.vector down) =ᵐ[volume] fun X =>
        (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) • v := by
  have hn := normalization p
  have hsr := spin_equality_radial D S O hZ ht0 ht1
    (components p.vector up) (components p.vector down) he
  rcases hsr with ⟨hup, v, hv⟩
  have hupref : p.vector up = 0 := by
    apply inclusion_injective Index (fun _ => 0)
    exact ((components_value p.vector up).symm.trans hup).trans
      (map_zero (inclusion Index (fun _ => 0))).symm
  have h0 : ‖ElectronicH1Complex.value (components p.vector up)‖ ^ 2 = 0 :=
    (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => ‖w‖ ^ 2) hup).trans
      (by simp)
  have h1 : ‖ElectronicH1Complex.value (components p.vector down)‖ ^ 2 =
      ‖inclusion Index (fun _ => 0) (p.vector down)‖ ^ 2 :=
    congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => ‖w‖ ^ 2)
      (components_value p.vector down)
  have hsq : ‖inclusion Index (fun _ => 0) (p.vector down)‖ ^ 2 = 1 := by
    linarith only [hn, h0, h1]
  refine ⟨hupref, norm_eq_one_of_sq _ hsq, v, ?_⟩
  filter_upwards [hv] with X hX
  exact (congrArg (fun w : ElectronicH1Space.L2 PhotonFock Index => w X)
    (components_value p.vector down)).symm.trans hX

/-- Equality forces spin down, the hydrogen orbital and the photon vacuum.
No spectral gap is assumed. -/
theorem unique_ground_state (D : StandardCylindricalDecomposition)
    (S : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    (BF : StandardSymmetricFockExponential)
    (Z : ℝ) (hZ : 0 < Z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    (c : ℝ) (hc : 0 ≤ c) (p : State 1)
    (hp : IsGroundState C 0 F χ (SpinfulCounterexamplePotentials.vector t)
      (SpinfulCounterexamplePotentials.scalar Z t) c hc p) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ p.vector = z • (state Z hZ).vector := by
  have hparts := minimizer_parts C F χ D Z hZ ht0 ht1 c hc p hp
  rcases hparts with ⟨he, hrDown⟩
  have hdown := minimizer_spin_down D S O Z hZ ht0 ht1 p he
  rcases hdown with ⟨hupref, hnDown, v, hv'⟩
  have hph := PhysicalReferenceVacuum.phase_of_electronic_factor BF (p.vector down)
    (inclusion Index (fun _ => 0) (CounterexampleVacuumState.reference Z hZ))
    (fun X => HydrogenOrbital.orbital Z (SymmetricLift.particle X 0))
    (fun X => (HydrogenOrbital.orbital_pos hZ _).ne')
    (CounterexampleVacuumState.reference_value_ae Z hZ) hnDown
    (CounterexampleVacuumState.reference_norm Z hZ) hrDown v hv'
  rcases hph with ⟨z, hz, hphase⟩
  have hdref : p.vector down = z • CounterexampleVacuumState.reference Z hZ := by
    apply inclusion_injective Index (fun _ => 0)
    exact hphase.trans (map_smul _ _ _).symm
  refine ⟨z, hz, ?_⟩
  calc
    p.vector = liftDown (p.vector down) := eq_liftDown_of_up_zero p.vector hupref
    _ = liftDown (z • CounterexampleVacuumState.reference Z hZ) := congrArg liftDown hdref
    _ = z • liftDown (CounterexampleVacuumState.reference Z hZ) := liftDown_smul z _
    _ = z • (state Z hZ).vector := rfl

/-- `prop-spinful-zero-coupling-counterexample` on the actual one-electron
Pauli model, for any fixed article cutoff. The ordinary circular and
spherical Fourier/Sobolev backgrounds `D` and `S`, the radial weak ODE
principle `O` and the inherited Fock background `BF` remain explicit.
No ground-state, angular-bound or energy-decomposition conclusion is
assumed. -/
theorem counterexample (D : StandardCylindricalDecomposition)
    (S : CounterexampleSpectral.StandardSphericalDecomposition)
    (O : CounterexampleSpectral.StandardRadialWeakODE (E := PhotonFock))
    (BF : StandardSymmetricFockExponential) (Z : ℝ) (hZ : 0 < Z) :
    ∃ p : State 1,
      (PauliReference.wave p.vector =ᵐ[volume] fun X =>
        (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) • vacuumDown) ∧
      (∀ t : ℝ, 0 < t → t < 1 / 2 →
        IsGroundState C 0 F χ (SpinfulCounterexamplePotentials.vector t)
          (SpinfulCounterexamplePotentials.scalar Z t) 1 zero_le_one p ∧
        energy C 0 F χ (SpinfulCounterexamplePotentials.vector t)
          (SpinfulCounterexamplePotentials.scalar Z t) 1 zero_le_one p.vector = -(Z ^ 2 / 2) ∧
        ∀ q : State 1,
          IsGroundState C 0 F χ (SpinfulCounterexamplePotentials.vector t)
            (SpinfulCounterexamplePotentials.scalar Z t) 1 zero_le_one q →
          ∃ z : ℂ, ‖z‖ = 1 ∧ q.vector = z • p.vector) ∧
      (PhysicalPairSpace.densityL1 (data C 0 F χ p.vector) =ᵐ[volume]
        HydrogenOrbital.density Z) ∧
      (∀ k : Fin 3, PauliMagnetizationMarginal.magnetization
        (PauliCurrentMagnetization.components p.vector) k =ᵐ[volume]
          fun x => if k = 2 then -HydrogenOrbital.density Z x else 0) ∧
      (PhysicalPairSpace.currentL1 (data C 0 F χ p.vector) =ᵐ[volume]
        SpinfulCounterexampleData.current Z) ∧
      (∀ α : ℝ, α < 2 * Z → Integrable (fun x => Real.exp (α * ‖x‖) *
        PhysicalPairSpace.densityL1 (data C 0 F χ p.vector) x) volume) ∧
      (∀ t r : ℝ, 2 < r → r < 3 → ∃ R : PauliPhysicalLocalRegularity.RegularityOn
        (SpinfulCounterexamplePotentials.vector t) (SpinfulCounterexamplePotentials.scalar Z t)
          Set.univ, R.exponent = r) ∧
      (∀ t : ℝ, ∀ x, SpinfulCounterexampleField.curl
        (SpinfulCounterexampleField.vectorPotential t) x =
          (2 * t * SpinfulCounterexampleField.weight x ^ 2) • EuclideanSpace.single 2 1) ∧
      (∀ s t : ℝ, s ≠ t →
        ¬ (((SpinfulCounterexamplePotentials.vector s).val : SpinfulCounterexampleField.Space →
            SpinfulCounterexampleField.Space) =ᵐ[volume]
          (SpinfulCounterexamplePotentials.vector t).val) ∧
        ¬ CounterexampleMagneticField.IsDistributionalGradient (fun x =>
          (SpinfulCounterexamplePotentials.vector t).val x -
            (SpinfulCounterexamplePotentials.vector s).val x) ∧
        ∀ x, SpinfulCounterexampleField.curl (SpinfulCounterexampleField.vectorPotential s) x ≠
          SpinfulCounterexampleField.curl (SpinfulCounterexampleField.vectorPotential t) x) := by
  refine ⟨state Z hZ, reference_wave_ae Z hZ, ?_,
    SpinfulCounterexampleData.density C F χ Z hZ,
    SpinfulCounterexampleData.magnetization Z hZ,
    SpinfulCounterexampleData.combined_current C F χ Z hZ,
    (fun α hα => SpinfulCounterexampleData.exponential_moment C F χ Z hZ hα),
    (fun t r hr hr3 =>
      ⟨SpinfulCounterexamplePotentials.pauliRegularityOfExponent Z t r hr hr3, rfl⟩),
    SpinfulCounterexampleField.magnetic_field, ?_⟩
  · intro t ht0 ht1
    exact ⟨ground_state C F χ D Z hZ ht0 ht1 1 zero_le_one,
      state_energy C F χ Z hZ t 1 zero_le_one,
      fun q hq => unique_ground_state C F χ D S O BF Z hZ ht0 ht1 1 zero_le_one q hq⟩
  · intro s t hst
    exact ⟨SpinfulCounterexamplePotentials.vector_not_ae_eq hst,
      SpinfulCounterexamplePotentials.not_distributional_gauge_equivalent hst,
      SpinfulCounterexampleField.distinct_curls_at hst⟩

end PfHk.SpinfulZeroCouplingCounterexample
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
