import PfHk.PhysicalGroundStateWeak
import PfHk.PhysicalDiamagneticPotential
import PfHk.PhysicalOpenFermionicUCP

/-! Physical unique continuation and density positivity for the existing
variational ground states with coefficient regularity only on a connected
open full-measure set. The global physical form and the actual state are
unchanged. No global distributional divergence is required. -/

noncomputable section
namespace PfHk.PhysicalOpenGroundStateUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalGroundState GptLean.PhysicalPairDuality GptLean.PhysicalPolarization
  GptLean.PhysicalNormalTrace GptLean.PhysicalClosedForms
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PhysicalOpenUCPCoefficients PfHk.PhysicalDiamagneticPotential

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

variable (U : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e) 
  {Ω : Set GptLean.PhysicalSourceCoordinates.Position}
  (hΩ : IsOpen Ω) (hconnected : IsConnected Ω)
  (hfull : ∀ᵐ x ∂volume, x ∈ Ω) (hreg : RegularityOn A v Ω)

include U hΩ hconnected hfull hreg

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
    (PhysicalOpenFermionicUCP.ae_nonzero U hN hΩ hconnected hfull hreg zero_le_one heigen hu)

theorem ae_norm_pos : ∀ᵐ X ∂volume, 0 < ‖p.val X‖ :=
  (ae_nonzero F χ C B S e i A v p hground U hΩ hconnected hfull hreg).mono fun _ hx => norm_pos_iff.mpr hx

/-- Positivity of the actual full electronic marginal. -/
theorem electronic_density_pos :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density p.val x :=
  NonvanishingDensity.density_pos_ae i p.val
    (ae_nonzero F χ C B S e i A v p hground U hΩ hconnected hfull hreg)

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
      (ae_nonzero F χ C B S e i A v p hground U hΩ hconnected hfull hreg)
  rw [hpair]
  exact NonvanishingDensity.pair_density_pos_ae i
    (ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
      (electronic (Fin N × Fin 3) (fun _ => 0) u)) _ hn

end PfHk.PhysicalOpenGroundStateUCP
