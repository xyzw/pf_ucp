import PfHk.PauliWeylEnergyCoordinates
import PfHk.PauliWeylEnergyLp

/-! The full physical Pauli energy along actual photon displacement lines.
Both magnetic contributions are retained through the Pauli contraction. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeylEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.SymmetricLift GptLean.Representability PfHk.PauliSpin PfHk.PauliGroundState
  PfHk.PauliCurrentAlgebra PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.CenteredPhysicalReference PfHk.PauliWeylEnergyLp

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 90000

variable {N : ℕ}
local instance energyReferenceAddCommGroup :
    AddCommGroup (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceAddCommGroup (N := N)
local instance energyReferenceModule : Module ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceModule (N := N)
local instance energyReferenceSMul : SMul ℂ (Reference (Fin N × Fin 3) (fun _ => 0)) :=
  PauliGroundState.referenceSMul (N := N)
attribute [local irreducible] referenceSubspace inclusion roughMultiply covariant
  PauliWeyl.displaced derivatives rawCovariant

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (e : ℝ) (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "κ" => profile (N := N) F χ 0
set_option hygiene false in
local notation "hκ" => profile_measurable (N := N) F χ 0
set_option hygiene false in
local notation "M" => profileBound F χ
set_option hygiene false in
local notation "hb" => profile_bound (N := N) F χ 0
set_option hygiene false in
local notation "D" => physicalDomain (N := N) A v c hc

def currentShift (f : Lp ℂ 2 photonMeasure) (u : PauliGroundState.Ref N) : ℝ :=
  ∑ n, ∑ a, ∫ X, classicalField κ f (n, a) X *
    current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
      (fun b s => derivatives F χ C e A v c hc u (n, b) s X) a

def densityShift (f : Lp ℂ 2 photonMeasure) (u : PauliGroundState.Ref N) : ℝ :=
  ∑ n : Fin N, ∑ a : Fin 3, ∫ X, classicalField κ f (n, a) X ^ 2 *
    density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)

def amplitude (K : WeightedPhotonKernel) (u : PauliGroundState.Ref N) : ℝ :=
  ∑ s, (inner ℂ (annihilationRef (fun _ => 0) K (u s))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).re

theorem energy_coordinates (u : PauliGroundState.Ref N) :
    PauliGroundState.energy C e F χ A v c hc u =
      (∑ n, kinetic n (fun a => derivatives F χ C e A v c hc u (n, a))) +
      (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
      (∑ s, ‖roughMultiply (positive v c)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).positive‖ ^ 2) -
      ∑ s, ‖roughMultiply (negative v c)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).negative‖ ^ 2 := by
  exact (rawEnergy_eq C κ hκ M hb e (vector A) (positive v c) (negative v c) u (D u)).trans
    (by simp only [kinetic, derivatives, rawContraction, Finset.mul_sum])

attribute [local irreducible] PauliGroundState.energy PauliReference.wave radiation

variable (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

theorem kinetic_displaced (u : PauliGroundState.Ref N) (n : Fin N) :
    kinetic n (fun a => derivatives F χ C e A v c hc (PauliWeyl.displaced W K hK u) (n, a)) =
      kinetic n (fun a => derivatives F χ C e A v c hc u (n, a)) -
      e * (∑ a, ∫ X, classicalField κ f (n, a) X *
        current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => derivatives F χ C e A v c hc u (n, b) s X) a) +
      (e ^ 2 / 2) * ∑ a, ∫ X, classicalField κ f (n, a) X ^ 2 *
        density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  have hmult (a : Fin 3) (s : SpinIndex N) :
      MemLp (fun X => (-(e * classicalField κ f (n, a) X)) •
        inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) 2 volume := by
    have hh := (bounded_multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      (classicalField κ f (n, a)) (classicalField_aestronglyMeasurable κ hκ f (n, a))
      (classicalField_bound κ M hb f (n, a))).const_smul (-e)
    change MemLp (fun X => (-e) • (classicalField κ f (n, a) X •
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)) 2 volume at hh
    simpa only [smul_smul, neg_mul] using hh
  have hh := integrated_kinetic_isometry_shift n (W.weyl f).toLinearIsometry
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun a => derivatives F χ C e A v c hc u (n, a))
    (fun a => derivatives F χ C e A v c hc (PauliWeyl.displaced W K hK u) (n, a))
    (fun a X => -(e * classicalField κ f (n, a) X)) hmult
    (fun a s => derivatives_displaced_ae W K hK F χ C e A v c hc u (n, a) s)
  refine hh.trans ?_
  simp only [neg_mul, mul_assoc, integral_neg, integral_const_mul,
    Finset.sum_neg_distrib, ← Finset.mul_sum, neg_sq, mul_pow]
  ring

private theorem energy_assembly
    {E E' T T' R R' P P' Q Q' amp rad coupling j q : ℝ}
    (hE : E = T + R + P - Q) (hE' : E' = T' + R' + P' - Q')
    (hT : T' = T - coupling * j + (coupling ^ 2 / 2) * q)
    (hR : R' = R + 2 * amp + rad) (hP : P' = P) (hQ : Q' = Q) :
    E' = E + 2 * amp + rad - coupling * j + (coupling ^ 2 / 2) * q := by
  rw [hE', hT, hR, hP, hQ, hE]
  ring

theorem energy_displaced (u : PauliGroundState.Ref N) :
    PauliGroundState.energy C e F χ A v c hc (PauliWeyl.displaced W K hK u) =
      PauliGroundState.energy C e F χ A v c hc u +
      2 * amplitude K u + ‖K.val.2‖ ^ 2 * ‖PauliReference.wave u‖ ^ 2 -
      e * currentShift F χ C e A v c hc f u + (e ^ 2 / 2) * densityShift F χ f u := by
  have hkin : (∑ n, kinetic n (fun a =>
      derivatives F χ C e A v c hc (PauliWeyl.displaced W K hK u) (n, a))) =
      (∑ n, kinetic n (fun a => derivatives F χ C e A v c hc u (n, a))) -
      e * currentShift F χ C e A v c hc f u + (e ^ 2 / 2) * densityShift F χ f u := by
    simp only [kinetic_displaced F χ C e A v c hc W K hK, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, currentShift, densityShift]
  have hpos : (∑ s, ‖roughMultiply (positive v c)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliWeyl.displaced W K hK u s))
      ((D (PauliWeyl.displaced W K hK u)) s).positive‖ ^ 2) =
      ∑ s, ‖roughMultiply (positive v c)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).positive‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => congrArg (fun r : ℝ => r ^ 2)
      (rough_norm_displaced W K hK (positive v c) u s _ _)
  have hneg : (∑ s, ‖roughMultiply (negative v c)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (PauliWeyl.displaced W K hK u s))
      ((D (PauliWeyl.displaced W K hK u)) s).negative‖ ^ 2) =
      ∑ s, ‖roughMultiply (negative v c)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((D u) s).negative‖ ^ 2 :=
    Finset.sum_congr rfl fun s _ => congrArg (fun r : ℝ => r ^ 2)
      (rough_norm_displaced W K hK (negative v c) u s _ _)
  have hrad : (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0)
      (PauliWeyl.displaced W K hK u s)‖ ^ 2) =
      (∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) +
      2 * amplitude K u + ‖K.val.2‖ ^ 2 * ‖PauliReference.wave u‖ ^ 2 :=
    PauliWeyl.radiation_norm_sq_displaced W K hK u
  exact energy_assembly (energy_coordinates F χ C e A v c hc u)
    (energy_coordinates F χ C e A v c hc (PauliWeyl.displaced W K hK u))
    hkin hrad hpos hneg

theorem currentShift_scaled (t : ℝ) (u : PauliGroundState.Ref N) :
    currentShift F χ C e A v c hc ((t : ℂ) • f) u =
      t * currentShift F χ C e A v c hc f u := by
  simp only [currentShift, classicalField_smul, mul_assoc, integral_const_mul,
    ← Finset.mul_sum]

theorem densityShift_scaled (t : ℝ) (u : PauliGroundState.Ref N) :
    densityShift F χ ((t : ℂ) • f) u = t ^ 2 * densityShift F χ f u := by
  simp only [densityShift, classicalField_smul, mul_pow, mul_assoc,
    integral_const_mul, ← Finset.mul_sum]

theorem amplitude_scaled (t : ℝ) (u : PauliGroundState.Ref N) :
    amplitude ((t : ℂ) • K) u = t * amplitude K u := by
  simp only [amplitude, PhysicalWeyl.amplitude_scaled, ← Finset.mul_sum]

attribute [local irreducible] currentShift densityShift amplitude

private theorem scaled_energy_assembly
    {E E' amp amp' rad rad' j j' q q' mass0 coupling t0 : ℝ}
    (hE : E' = E + 2 * amp' + rad' * mass0 - coupling * j' +
      (coupling ^ 2 / 2) * q')
    (ha : amp' = t0 * amp) (hr : rad' = t0 ^ 2 * rad)
    (hj : j' = t0 * j) (hq : q' = t0 ^ 2 * q) :
    E' = E + t0 * (2 * amp - coupling * j) +
      t0 ^ 2 * (rad * mass0 + (coupling ^ 2 / 2) * q) := by
  rw [hE, ha, hr, hj, hq]
  ring

theorem energy_scaled (t : ℝ) (u : PauliGroundState.Ref N) :
    PauliGroundState.energy C e F χ A v c hc
      (PauliWeyl.displaced W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u) =
      PauliGroundState.energy C e F χ A v c hc u +
        t * (2 * amplitude K u - e * currentShift F χ C e A v c hc f u) +
        t ^ 2 * (‖K.val.2‖ ^ 2 * ‖PauliReference.wave u‖ ^ 2 +
          (e ^ 2 / 2) * densityShift F χ f u) := by
  exact scaled_energy_assembly
    (energy_displaced F χ C e A v c hc W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)
    (amplitude_scaled K t u) (kernel_scaled_norm_sq t K)
    (currentShift_scaled F χ C e A v c hc t u) (densityShift_scaled F χ t u)

end PfHk.PauliWeylEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
