import PfHk.CounterexampleSpectralAlgebra
import PfHk.CounterexampleField
import GptLean.ElectronicH1Complex
import GptLean.PhysicalFockSectors
import GptLean.SymmetricLift.MetricGeometry

/-! Hydrogenic lower bounds for the actual Hilbert-valued electronic H1
space. The standard spherical-harmonic transform and its Sobolev form
identities are explicit operator-theory inputs. The magnetic lower bound
and its equality case are conclusions. -/

noncomputable section
namespace PfHk.CounterexampleSpectral

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.ElectronicH1Complex
open scoped InnerProductSpace ENNReal Topology

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

local instance photonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

abbrev Index := Fin 1 × Fin 3
abbrev Space := EuclideanSpace ℝ Index
abbrev Electronic := ComplexH1 PhotonFock Index

attribute [local irreducible] ElectronicH1Complex.value ElectronicH1Complex.derivative

def position (X : Space) : CounterexampleField.Space := SymmetricLift.particle X 0

def kinetic (q : Electronic) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Index, ‖derivative i q‖ ^ 2

def coulomb (q : Electronic) : ℝ :=
  ∫ X, ‖value q X‖ ^ 2 / ‖position X‖

def rotationForm (q : Electronic) : ℝ :=
  ∑ j : Fin 3, ∫ X, CounterexampleField.field (position X) j *
    (inner ℂ (value q X) ((-Complex.I) • derivative (0, j) q X)).re

/-- The electronic quadratic form of the displayed counterexample after
the diamagnetic scalar cancellation. -/
def electronicEnergy (Z t : ℝ) (q : Electronic) : ℝ :=
  kinetic q - Z * coulomb q + t * rotationForm q

attribute [local irreducible] kinetic coulomb rotationForm electronicEnergy

/-- Standard Hilbert-valued spherical-harmonic expansion on the actual
three-dimensional H1 space. The radial profiles include the ordinary core
IBP identities. These inputs are independent of both physical parameters.
No lower bound, spectral simplicity, or counterexample conclusion is a
field of this structure. -/
structure StandardSphericalDecomposition where
  profile : AngularIndex → Electronic → RadialProfile PhotonFock
  summable_derivative : ∀ q, Summable (fun c => ‖(profile c q).derivative‖ ^ 2)
  summable_centrifugal : ∀ q,
    Summable (fun c => centrifugal c * ‖(profile c q).inverseRadius‖ ^ 2)
  summable_coulomb : ∀ q,
    Summable (fun c => inner ℝ (profile c q).inverseRadius (profile c q).value)
  summable_norm : ∀ q, Summable (fun c => ‖(profile c q).value‖ ^ 2)
  summable_rotation : ∀ q,
    Summable (fun c => (order c : ℝ) * ‖(profile c q).rotationWeight‖ ^ 2)
  kinetic_decomposition : ∀ q, kinetic q =
    ∑' c, ((1 / 2 : ℝ) * ‖(profile c q).derivative‖ ^ 2 +
      centrifugal c * ‖(profile c q).inverseRadius‖ ^ 2)
  coulomb_decomposition : ∀ q, coulomb q =
    ∑' c, inner ℝ (profile c q).inverseRadius (profile c q).value
  norm_decomposition : ∀ q, ‖value q‖ ^ 2 = ∑' c, ‖(profile c q).value‖ ^ 2
  rotation_decomposition : ∀ q, rotationForm q =
    ∑' c, (order c : ℝ) * ‖(profile c q).rotationWeight‖ ^ 2
  reconstruct_sWave : ∀ (q : Electronic) (f : ℝ → PhotonFock),
    (∀ c, c ≠ zeroChannel → (profile c q).value = 0) →
    ((profile zeroChannel q).value =ᵐ[radialMeasure] f) →
    (value q =ᵐ[volume] fun X =>
      (Real.sqrt (4 * Real.pi) * ‖position X‖)⁻¹ • f ‖position X‖)

def channelExcess (D : StandardSphericalDecomposition) (Z t : ℝ)
    (q : Electronic) (c : AngularIndex) : ℝ :=
  radialExcess Z (D.profile c q) + angularEnergy t c (D.profile c q)

theorem channelExcess_summable (D : StandardSphericalDecomposition)
    (Z t : ℝ) (q : Electronic) : Summable (channelExcess D Z t q) := by
  have hr := ((D.summable_derivative q).mul_left (1 / 2 : ℝ)).sub
    ((D.summable_coulomb q).mul_left Z)
  have hs := hr.add ((D.summable_norm q).mul_left (Z ^ 2 / 2))
  have ha := (D.summable_centrifugal q).add ((D.summable_rotation q).mul_left t)
  convert hs.add ha using 1 <;> try rfl
  funext c
  simp only [channelExcess, radialExcess, angularEnergy]
  ring

/-- The exact channel expansion of the energy above the hydrogenic level. -/
theorem energy_excess_decomposition (D : StandardSphericalDecomposition)
    (Z t : ℝ) (q : Electronic) :
    electronicEnergy Z t q + (Z ^ 2 / 2) * ‖value q‖ ^ 2 =
      ∑' c, channelExcess D Z t q c := by
  have h := sum_energy_reorder
    (fun c => (1 / 2 : ℝ) * ‖(D.profile c q).derivative‖ ^ 2)
    (fun c => centrifugal c * ‖(D.profile c q).inverseRadius‖ ^ 2)
    (fun c => inner ℝ (D.profile c q).inverseRadius (D.profile c q).value)
    (fun c => (order c : ℝ) * ‖(D.profile c q).rotationWeight‖ ^ 2)
    (fun c => ‖(D.profile c q).value‖ ^ 2)
    ((D.summable_derivative q).mul_left (1 / 2 : ℝ))
    (D.summable_centrifugal q) (D.summable_coulomb q)
    (D.summable_rotation q) (D.summable_norm q) Z t
  rw [← D.kinetic_decomposition q, ← D.coulomb_decomposition q,
    ← D.rotation_decomposition q, ← D.norm_decomposition q] at h
  simpa only [electronicEnergy, channelExcess, radialExcess, angularEnergy, mul_assoc] using h

theorem channelExcess_nonneg (D : StandardSphericalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : |t| ≤ 1) (q : Electronic) (c : AngularIndex) :
    0 ≤ channelExcess D Z t q c :=
  add_nonneg (radialExcess_nonneg Z _) (angularEnergy_nonneg ht _ _)

/-- Every actual electronic H1 vector satisfies the hydrogenic lower bound
for the whole magnetic family, with no gap assumption. -/
theorem energy_lower_bound (D : StandardSphericalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : |t| ≤ 1) (q : Electronic) :
    -(Z ^ 2 / 2) * ‖value q‖ ^ 2 ≤ electronicEnergy Z t q := by
  have h : 0 ≤ ∑' c, channelExcess D Z t q c :=
    tsum_nonneg (channelExcess_nonneg D Z ht q)
  rw [← energy_excess_decomposition D Z t q] at h
  linarith

theorem channelExcess_eq_zero (D : StandardSphericalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : |t| ≤ 1) (q : Electronic)
    (he : electronicEnergy Z t q = -(Z ^ 2 / 2) * ‖value q‖ ^ 2)
    (c : AngularIndex) : channelExcess D Z t q c = 0 :=
  nonnegative_series_term_zero (channelExcess D Z t q)
    (channelExcess_summable D Z t q) (channelExcess_nonneg D Z ht q)
    (electronicEnergy Z t q) (Z ^ 2 / 2) (‖value q‖ ^ 2)
    (energy_excess_decomposition D Z t q) he c

theorem higher_channels_zero (D : StandardSphericalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : |t| < 1) (q : Electronic)
    (he : electronicEnergy Z t q = -(Z ^ 2 / 2) * ‖value q‖ ^ 2)
    (c : AngularIndex) (hc : c ≠ zeroChannel) : (D.profile c q).value = 0 := by
  have hz := channelExcess_eq_zero D Z ht.le q he c
  have hr := radialExcess_nonneg Z (D.profile c q)
  have ha := angularEnergy_nonneg ht.le c (D.profile c q)
  have hangular : angularEnergy t c (D.profile c q) = 0 := by
    unfold channelExcess at hz
    linarith
  exact radial_value_eq_zero_of_angular_zero ht hc _ hangular

theorem zero_channel_radial_zero (D : StandardSphericalDecomposition)
    (Z : ℝ) {t : ℝ} (ht : |t| ≤ 1) (q : Electronic)
    (he : electronicEnergy Z t q = -(Z ^ 2 / 2) * ‖value q‖ ^ 2) :
    radialExcess Z (D.profile zeroChannel q) = 0 := by
  have hz := channelExcess_eq_zero D Z ht q he zeroChannel
  simpa [channelExcess, angularEnergy, centrifugal, zeroChannel, degree, order] using hz

private theorem position_ne_zero_ae : ∀ᵐ X : Space ∂volume, position X ≠ 0 := by
  filter_upwards [(volume : Measure Space).ae_ne 0] with X hX hpos
  apply hX
  ext i
  rcases i with ⟨n, j⟩
  have hn : n = 0 := Subsingleton.elim _ _
  subst n
  exact congrArg (fun x : CounterexampleField.Space => x j) hpos

/-- Equality forces a common radial orbital times a constant photon vector.
The subsequent radiation argument identifies that vector with the vacuum. -/
theorem energy_equality_radial (D : StandardSphericalDecomposition)
    (O : StandardRadialWeakODE (E := PhotonFock))
    {Z t : ℝ} (hZ : 0 < Z) (ht : |t| < 1) (q : Electronic)
    (he : electronicEnergy Z t q = -(Z ^ 2 / 2) * ‖value q‖ ^ 2) :
    ∃ c : PhotonFock, value q =ᵐ[volume] fun X =>
      (Real.sqrt (Z ^ 3 / Real.pi) * Real.exp (-Z * ‖position X‖)) • c := by
  have hrad := radial_kernel O Z (D.profile zeroChannel q)
    (zero_channel_radial_zero D Z ht.le q he)
  obtain ⟨C, hC⟩ := hrad
  have hreconstruct := D.reconstruct_sWave q
    (fun r => (r * Real.exp (-Z * r)) • C)
    (higher_channels_zero D Z ht q he) hC
  let a : ℝ := Real.sqrt (Z ^ 3 / Real.pi)
  let b : ℝ := Real.sqrt (4 * Real.pi)
  have ha : a ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hb : b ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  refine ⟨(b * a)⁻¹ • C, ?_⟩
  filter_upwards [hreconstruct, position_ne_zero_ae] with X hX hn
  rw [hX, smul_smul, smul_smul]
  congr 1
  change (b * ‖position X‖)⁻¹ * (‖position X‖ * Real.exp (-Z * ‖position X‖)) =
    (a * Real.exp (-Z * ‖position X‖)) * (b * a)⁻¹
  field_simp [ha, hb, norm_ne_zero_iff.mpr hn]

/-- A normalized scalar orbital transfers the L2 norm to its constant
photon coefficient. This derives the coefficient norm used in the vacuum
and phase-uniqueness step. -/
theorem norm_value_eq_norm_coefficient (q : Electronic) (f : Space → ℝ)
    (c : PhotonFock) (hf : value q =ᵐ[volume] fun X => f X • c)
    (hnormal : (∫ X, f X ^ 2) = 1) : ‖value q‖ = ‖c‖ :=
  lp_norm_eq_norm_coefficient (value q) f c hf hnormal

end PfHk.CounterexampleSpectral
