import PfHk.PhysicalOneParticleState
import PfHk.HydrogenOrbitalH1
import PfHk.CounterexampleSpectral

/-! The explicit normalized hydrogen orbital in the photon vacuum belongs
to the actual one-electron reference domain. Its electronic form energy is
the hydrogenic value for every member of the magnetic family. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.CounterexampleVacuumState

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalOneParticleState
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 250000

attribute [local irreducible] inclusion ordinary radiation
  PhysicalPFReference.referenceSubspace

private theorem zero_potential_graph (Z : ℝ) (hZ : 0 < Z) :
    ∀ᵐ X ∂volume, (0 : Lp ℂ 2 (volume : Measure (Position Index))) X =
      (Real.sqrt (0 : ℝ) : ℂ) •
        ElectronicH1Complex.value (HydrogenOrbital.oneParticleH1 Z hZ) X := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (Position Index))] with X hX
  simpa only [Real.sqrt_zero, Complex.ofReal_zero, zero_smul, Pi.zero_apply] using hX

private theorem value_electronic (u : Ref) :
    ElectronicH1Complex.value (electronic Index (fun _ => 0) u) =
      inclusion Index (fun _ => 0) u := by
  unfold inclusion
  rfl

private theorem derivative_electronic (u : Ref) (j : Index) :
    ElectronicH1Complex.derivative j (electronic Index (fun _ => 0) u) =
      ordinary Index (fun _ => 0) j u := by
  unfold ordinary
  rfl

def reference (Z : ℝ) (hZ : 0 < Z) : Ref :=
  PhysicalElectronicReference.reference Index (fun _ => 0)
    (HydrogenOrbital.oneParticleH1 Z hZ) 0 (zero_potential_graph Z hZ)

theorem reference_value (Z : ℝ) (hZ : 0 < Z) :
    inclusion Index (fun _ => 0) (reference Z hZ) =
      PhysicalFullVacuum.insertion volume
        (ElectronicH1Complex.value (HydrogenOrbital.oneParticleH1 Z hZ)) :=
  PhysicalElectronicReference.reference_value _ _ _ _ _

theorem reference_value_ae (Z : ℝ) (hZ : 0 < Z) :
    inclusion Index (fun _ => 0) (reference Z hZ) =ᵐ[volume]
      fun X => (HydrogenOrbital.orbital Z (SymmetricLift.particle X 0) : ℂ) •
        PhysicalFullVacuum.vacuum := by
  rw [reference_value]
  filter_upwards [PhysicalFullVacuum.insertion_ae volume
      (ElectronicH1Complex.value (HydrogenOrbital.oneParticleH1 Z hZ)),
    HydrogenOrbital.oneParticleH1_value Z hZ] with X hX hφ
  exact hX.trans (congrArg PhysicalFullVacuum.fiberInsertion hφ)

theorem reference_norm (Z : ℝ) (hZ : 0 < Z) :
    ‖inclusion Index (fun _ => 0) (reference Z hZ)‖ = 1 := by
  rw [reference_value, LinearIsometry.norm_map, HydrogenOrbital.oneParticleH1_value_norm]

theorem reference_ordinary (Z : ℝ) (hZ : 0 < Z) (j : Index) :
    ordinary Index (fun _ => 0) j (reference Z hZ) =
      PhysicalFullVacuum.insertion volume
        (ElectronicH1Complex.derivative j (HydrogenOrbital.oneParticleH1 Z hZ)) :=
  PhysicalElectronicReference.reference_ordinary _ _ _ _ _ _

theorem reference_ordinary_ae (Z : ℝ) (hZ : 0 < Z) (j : Index) :
    ordinary Index (fun _ => 0) j (reference Z hZ) =ᵐ[volume]
      fun X => (HydrogenOrbital.derivative Z j.2 (SymmetricLift.particle X 0) : ℂ) •
        PhysicalFullVacuum.vacuum := by
  rw [reference_ordinary]
  filter_upwards [PhysicalFullVacuum.insertion_ae volume
      (ElectronicH1Complex.derivative j (HydrogenOrbital.oneParticleH1 Z hZ)),
    HydrogenOrbital.oneParticleH1_derivative Z hZ j] with X hX hφ
  exact hX.trans (congrArg PhysicalFullVacuum.fiberInsertion hφ)

theorem reference_radiation (Z : ℝ) (hZ : 0 < Z) :
    radiation Index (fun _ => 0) (reference Z hZ) = 0 :=
  PhysicalElectronicReference.reference_radiation _ _ _ _ _

theorem reference_kinetic (Z : ℝ) (hZ : 0 < Z) :
    (∑ j : Index, ‖ordinary Index (fun _ => 0) j (reference Z hZ)‖ ^ 2) = Z ^ 2 := by
  simp only [reference_ordinary, LinearIsometry.norm_map]
  exact HydrogenOrbital.oneParticleH1_kinetic_norms Z hZ

private theorem real_current {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) (a b : ℝ) :
    (inner ℂ ((a : ℂ) • v) ((-Complex.I) • ((b : ℂ) • v))).re = 0 := by
  rw [inner_smul_right, inner_smul_right, inner_smul_left]
  have him : (inner ℂ v v).im = 0 := inner_self_im (𝕜 := ℂ) v
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    him, zero_mul, mul_zero, sub_zero, zero_sub, neg_zero]
  ring

private theorem real_current_ae {Q H : Type*} [MeasurableSpace Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure Q}
    (v : H) {f g : Q → H} {a b : Q → ℝ}
    (hf : f =ᵐ[μ] fun X => (a X : ℂ) • v)
    (hg : g =ᵐ[μ] fun X => (b X : ℂ) • v) :
    ∀ᵐ X ∂μ, (inner ℂ (f X) ((-Complex.I) • g X)).re = 0 := by
  filter_upwards [hf, hg] with X hX hd
  rw [hX, hd]
  exact real_current v _ _

private theorem norm_sq_real_ae {Q H : Type*} [MeasurableSpace Q]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {μ : Measure Q}
    (v : H) (hv : ‖v‖ = 1) {f : Q → H} {a : Q → ℝ}
    (hf : f =ᵐ[μ] fun X => (a X : ℂ) • v) :
    (fun X => ‖f X‖ ^ 2) =ᵐ[μ] fun X => a X ^ 2 := by
  filter_upwards [hf] with X hX
  rw [hX, norm_smul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem reference_current (Z : ℝ) (hZ : 0 < Z) (j : Fin 3) :
    ∀ᵐ X ∂volume,
      (⟪inclusion Index (fun _ => 0) (reference Z hZ) X,
        (-Complex.I) • ordinary Index (fun _ => 0) (0, j) (reference Z hZ) X⟫_ℂ).re = 0 :=
  real_current_ae PhysicalFullVacuum.vacuum (reference_value_ae Z hZ)
    (reference_ordinary_ae Z hZ (0, j))

theorem reference_coulomb (Z : ℝ) (hZ : 0 < Z) :
    CounterexampleSpectral.coulomb (electronic Index (fun _ => 0) (reference Z hZ)) = Z := by
  unfold CounterexampleSpectral.coulomb
  rw [value_electronic]
  have hn := norm_sq_real_ae PhysicalFullVacuum.vacuum PhysicalFullVacuum.vacuum_norm
    (reference_value_ae Z hZ)
  calc
    _ = ∫ X, HydrogenOrbital.density Z (SymmetricLift.particle X 0) /
        ‖SymmetricLift.particle X 0‖ := by
      apply integral_congr_ae
      filter_upwards [hn] with X hX
      exact congrArg (fun r : ℝ => r / ‖SymmetricLift.particle X 0‖)
        (hX.trans (HydrogenOrbital.orbital_sq hZ.le _))
    _ = Z := HydrogenOrbital.oneParticle_integral_density_div_norm hZ

theorem reference_rotation (Z : ℝ) (hZ : 0 < Z) :
    CounterexampleSpectral.rotationForm (electronic Index (fun _ => 0) (reference Z hZ)) = 0 := by
  unfold CounterexampleSpectral.rotationForm
  simp only [value_electronic, derivative_electronic]
  apply Finset.sum_eq_zero
  intro j _
  apply integral_eq_zero_of_ae
  filter_upwards [reference_current Z hZ j] with X hX
  exact (congrArg (fun r : ℝ => CounterexampleField.field
    (CounterexampleSpectral.position X) j * r) hX).trans (mul_zero _)

private theorem energy_value (Z t K V R : ℝ) (hK : K = Z ^ 2 / 2)
    (hV : V = Z) (hR : R = 0) : K - Z * V + t * R = -(Z ^ 2 / 2) := by
  rw [hK, hV, hR]
  ring

/-- Direct evaluation of the proposed state attains the lower spectral level. -/
theorem reference_electronic_energy (Z : ℝ) (hZ : 0 < Z) (t : ℝ) :
    CounterexampleSpectral.electronicEnergy Z t
      (electronic Index (fun _ => 0) (reference Z hZ)) = -(Z ^ 2 / 2) := by
  have hk : CounterexampleSpectral.kinetic
      (electronic Index (fun _ => 0) (reference Z hZ)) = Z ^ 2 / 2 := by
    unfold CounterexampleSpectral.kinetic
    simp only [derivative_electronic]
    rw [reference_kinetic]
    ring
  exact energy_value Z t _ _ _ hk (reference_coulomb Z hZ) (reference_rotation Z hZ)

variable (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground)

def state (Z : ℝ) (hZ : 0 < Z) : State F χ C B S 0 (N := 1) :=
  ofReference F χ C B S 0 (reference Z hZ) (reference_norm Z hZ)

theorem state_value (Z : ℝ) (hZ : 0 < Z) :
    (state F χ C B S Z hZ).val = inclusion Index (fun _ => 0) (reference Z hZ) := rfl

end PfHk.CounterexampleVacuumState

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
