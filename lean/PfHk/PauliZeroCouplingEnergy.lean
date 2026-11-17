import PfHk.PauliExternalEnergy
import PfHk.PauliFreeGradient
import PfHk.CounterexamplePhysicalEnergy

/-! At zero photon coupling the actual one-electron Pauli energy has the
ordinary kinetic and radiation terms, with its physical scalar and current
pairings. The electron interaction vanishes for one electron. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliZeroCouplingEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliExternalEnergy
  PfHk.PauliCurrentAlgebra PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
attribute [local irreducible] referenceSubspace inclusion ordinary radiation covariant
  ElectronicH1Complex.complexWeakGraph

abbrev Index := Fin 1 × Fin 3

variable (C : CanonicalSectorCCR photonMeasure) (F : Frame) (χ : ArticleCutoff)

/-- The photon kernel disappears from every covariant derivative at e=0. -/
theorem covariants_zero {N : ℕ} (u : Ref N) (q : Fin N × Fin 3) (s : SpinIndex N) :
    covariants C 0 F χ u q s = (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) q (u s) := by
  exact (covariant_apply (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) 0 q (u s)).trans
    (by simp only [Complex.ofReal_zero, zero_smul, sub_zero])

theorem coulombTerm_one (c : ℝ) (u : Ref 1) : coulombTerm c u = 0 := by
  simp [coulombTerm, PhysicalCoulombH1.potential]

private theorem sum_index (f : Index → ℝ) : (∑ q, f q) = ∑ a : Fin 3, f (0, a) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]

private theorem half_sum_comm {S : Type*} [Fintype S] (g : S → Fin 3 → ℝ) :
    (∑ s, (1 / 2 : ℝ) * ∑ a, g s a) = (1 / 2 : ℝ) * ∑ a, ∑ s, g s a := by
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- The ordinary electronic kinetic energy of one photon-valued reference vector. -/
theorem kinetic_electronic (w : Reference Index (fun _ => 0)) :
    CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) w) =
      (1 / 2 : ℝ) * ∑ a : Fin 3, ‖ordinary Index (fun _ => 0) (0, a) w‖ ^ 2 := by
  have hk : CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) w) =
      (1 / 2 : ℝ) * ∑ q : Index, ‖ordinary Index (fun _ => 0) q w‖ ^ 2 :=
    congrArg (fun d : Index → WaveSpace Index => (1 / 2 : ℝ) * ∑ q, ‖d q‖ ^ 2)
      (funext (fun q : Index => CounterexamplePhysicalEnergy.derivative_electronic w q))
  exact hk.trans (congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (sum_index (fun q => ‖ordinary Index (fun _ => 0) q w‖ ^ 2)))

/-- The free Pauli square is the ordinary electronic kinetic energy on H1. -/
theorem kinetic_one (u : Ref 1) :
    kinetic (0 : Fin 1) (fun a => covariants C 0 F χ u (0, a)) =
      ∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s)) := by
  have hd : (fun a s => covariants C 0 F χ u (0, a) s) =
      (fun a s => (-Complex.I) • ordinary Index (fun _ => 0) (0, a) (u s)) :=
    funext fun a => funext fun s => covariants_zero C F χ u (0, a) s
  have hk : kinetic (0 : Fin 1) (fun a => covariants C 0 F χ u (0, a)) =
      (1 / 2 : ℝ) * ∑ a : Fin 3, ∑ s, ‖ordinary Index (fun _ => 0) (0, a) (u s)‖ ^ 2 :=
    (congrArg (kinetic (0 : Fin 1)) hd).trans
      (congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) (PauliFreeGradient.reference_norm_sq u 0))
  have hs : (∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s))) =
      (1 / 2 : ℝ) * ∑ a : Fin 3, ∑ s, ‖ordinary Index (fun _ => 0) (0, a) (u s)‖ ^ 2 :=
    (Finset.sum_congr rfl fun s _ => kinetic_electronic (u s)).trans
      (half_sum_comm (fun s a => ‖ordinary Index (fun _ => 0) (0, a) (u s)‖ ^ 2))
  exact hk.trans hs.symm

theorem intrinsicEnergy_one (c : ℝ) (u : Ref 1) :
    intrinsicEnergy C 0 F χ c u =
      (∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s))) +
      ∑ s, ‖radiation Index (fun _ => 0) (u s)‖ ^ 2 := by
  have hk : (∑ n : Fin 1, kinetic n (fun a => covariants C 0 F χ u (n, a))) =
      ∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s)) :=
    (Fin.sum_univ_one (fun n : Fin 1 => kinetic n (fun a => covariants C 0 F χ u (n, a)))).trans
      (kinetic_one C F χ u)
  have hc := coulombTerm_one c u
  have he : intrinsicEnergy C 0 F χ c u =
      (∑ n : Fin 1, kinetic n (fun a => covariants C 0 F χ u (n, a))) +
        (∑ s, ‖radiation Index (fun _ => 0) (u s)‖ ^ 2) + coulombTerm c u := rfl
  linarith

/-- An exact identity on every reference spinor, before using any spectral
inequality or choosing the hydrogenic state. -/
theorem energy_one (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Ref 1) :
    energy C 0 F χ A v c hc u =
      (∑ s, CounterexampleSpectral.kinetic (electronic Index (fun _ => 0) (u s))) +
      (∑ s, ‖radiation Index (fun _ => 0) (u s)‖ ^ 2) +
      scalarTerm (PhysicalDiamagneticPotential.shifted v A).1 u + vectorTerm C 0 F χ A u := by
  have h := energy_expansion C 0 F χ A v c hc u
  have hi := intrinsicEnergy_one C F χ c u
  have hs := scalarTerm_shift A v u
  linarith

end PfHk.PauliZeroCouplingEnergy
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
