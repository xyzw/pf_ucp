import PfHk.PhysicalGroundStateWeak
import PfHk.PhysicalDiamagneticPotential
import PfHk.PhysicalFermionicUCP

/-! Physical unique continuation and density positivity for the existing
variational ground states. The diamagnetic shift, common form representative,
fermionic first variation and extension to all tests are constructed. -/

noncomputable section
namespace PfHk.PhysicalGroundStateUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PhysicalFermionicCoefficients PfHk.PhysicalDiamagneticPotential

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 150000

attribute [local irreducible] inclusion covariant PhysicalPFReference.referenceSubspace
  IsExternalWeakEigenstate PhysicalFermionicWeakEquation.IsFermionicWeakEigenstate

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure) (B : StandardNormalTraceBackground)
  (S : StandardClosedFormBackground) (e : ℝ)
  (i : Fin N) (A : VectorPotential) (v : ScalarPotential)
  (p : State F χ C B S e (N := N))
  (hground : IsGroundState i F χ C B S e (shifted v A) p)

include hground

/-- The paper's variational ground state satisfies the full-space weak
Hamiltonian equation with its actual scalar and vector potentials. -/
theorem exists_full_weak_eigenstate :
    ∃ u : Reference (Fin N × Fin 3) (fun _ => 0),
      inclusion (Fin N × Fin 3) (fun _ => 0) u = p.val ∧
      IsExternalWeakEigenstate (fun _ => 0) C (CenteredPhysicalReference.profile F χ 0)
        (CenteredPhysicalReference.profile_measurable F χ 0)
        (CenteredPhysicalReference.profileBound F χ)
        (CenteredPhysicalReference.profile_bound F χ 0) e
        (vector A) (positive v 1) (negative v 1)
        (shiftedEnergy i F χ C B S e (shifted v A) p) u
        (externalDomain A v 1 zero_le_one u) := by
  have hex := PhysicalGroundStateWeak.exists_shifted_weak_eigenstate
    (N := N) F χ C B S e i A v p hground
  rcases hex with ⟨u, hvalue, heigen⟩
  exact ⟨u, hvalue, PhysicalFermionicReduction.full_weak_of_fermionic_weak
    F χ C e A v 1 zero_le_one heigen⟩

variable (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e) (hreg : Regularity A v)

include U hreg

/-- The existing normalized fermionic ground state is nonzero almost
everywhere in configuration space. -/
theorem ae_nonzero : ∀ᵐ X ∂volume, p.val X ≠ 0 := by
  have hex := PhysicalGroundStateWeak.exists_shifted_weak_eigenstate
    (N := N) F χ C B S e i A v p hground
  rcases hex with ⟨u, hvalue, heigen⟩
  have hu : u ≠ 0 := by
    intro hz
    have hn : ‖p.val‖ = 0 := by rw [← hvalue, hz, map_zero, norm_zero]
    have hone : ‖p.val‖ = 1 := p.property.1
    linarith
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) => ∀ᵐ X ∂volume, ψ X ≠ 0) hvalue).mp
    (PhysicalFermionicUCP.ae_nonzero U hN hreg zero_le_one heigen hu)

theorem ae_norm_pos : ∀ᵐ X ∂volume, 0 < ‖p.val X‖ :=
  (ae_nonzero F χ C B S e i A v p hground U hreg).mono fun _ hx => norm_pos_iff.mpr hx

/-- Positivity of the actual full electronic marginal. -/
theorem electronic_density_pos :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density p.val x :=
  NonvanishingDensity.density_pos_ae i p.val
    (ae_nonzero F χ C B S e i A v p hground U hreg)

/-- Positivity of the density component of the existing article model's
actual density-current pair. -/
theorem model_density_pos :
    ∀ᵐ x ∂volume, 0 < PhysicalPairSpace.densityL1
      ((PhysicalGroundState.model i F χ C B S e).density p) x := by
  let u := PhysicalGroundStateWeak.stateReference F χ C B S e p
  have hv := PhysicalGroundStateWeak.stateReference_value F χ C B S e p
  have hpair := PhysicalGroundStateWeak.pure_density_eq_pair F χ C B S e i p u hv
  have hvalue : ElectronicH1Space.value
      (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
        (electronic (Fin N × Fin 3) (fun _ => 0) u)) = p.val := by
    have hval : ElectronicH1Space.value
        (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
          (electronic (Fin N × Fin 3) (fun _ => 0) u)) =
        inclusion (Fin N × Fin 3) (fun _ => 0) u := by
      unfold inclusion
      rfl
    exact hval.trans hv
  have hn : ∀ᵐ X ∂volume, ElectronicH1Space.value
      (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
        (electronic (Fin N × Fin 3) (fun _ => 0) u)) X ≠ 0 :=
    (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) => ∀ᵐ X ∂volume, ψ X ≠ 0) hvalue).mpr
      (ae_nonzero F χ C B S e i A v p hground U hreg)
  rw [hpair]
  exact NonvanishingDensity.pair_density_pos_ae i
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) u)) _ hn

end PfHk.PhysicalGroundStateUCP
