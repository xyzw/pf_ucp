import PfHk.PhysicalFermionicReduction
import PfHk.PhysicalFermionicCoefficients
import PfHk.PhysicalUCPConsequences

/-! Unique continuation for the actual fermionic external form. The weak
equation is only required on fermionic tests. The extension, collision-free
geometry, scalar Sobolev bound and physical Carleman estimate are derived. -/

noncomputable section
namespace PfHk.PhysicalFermionicUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.PhysicalPairDuality
  PfHk.PhysicalFermionicWeakEquation PfHk.PhysicalFermionicCoefficients
  PfHk.PhysicalFermionicAverage PfHk.UniqueContinuationDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalLocalEnergy.IsExternalWeakEigenstate

variable {N : ℕ} {F : Frame} {χ : ArticleCutoff} {C : CanonicalSectorCCR photonMeasure} {e : ℝ}
  (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e) (hN : 0 < N)
  {A : VectorPotential} {v : ScalarPotential} (hreg : Regularity A v)
  {c : ℝ} (hc : 0 ≤ c) {E : ℝ} {u : Ref N}
  (heigen : IsFermionicWeakEigenstate F χ C e A v c hc E u)

include B hN hreg heigen

/-- An infinite-order zero away from collisions forces the physical
fermionic weak eigenstate to vanish globally almost everywhere. -/
theorem zero_of_infinite_order {X₀ : GptLean.SymmetricLift.Configuration N}
    (hX₀ : X₀ ∈ GptLean.SymmetricLift.distinctConfigurations N)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (inclusion (Fin N × Fin 3) (fun _ => 0) u) X₀)) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 :=
  PhysicalUCPConsequences.zero_of_infinite_order B (hreg.data c hc) hN
    (ConfigurationGeometry.regular_isOpen N)
    (ConfigurationGeometry.regular_isConnected N).isPreconnected
    (ConfigurationGeometry.regular_ae N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen)
    hX₀ hflat

theorem zero_of_positive_zero_measure
    (hpositive : 0 < volume {X | inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0}) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 :=
  PhysicalUCPConsequences.zero_of_positive_zero_measure B (hreg.data c hc) hN
    (ConfigurationGeometry.regular_isOpen N)
    (ConfigurationGeometry.regular_isConnected N).isPreconnected
    (ConfigurationGeometry.regular_ae N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hpositive

theorem ae_nonzero (hu : u ≠ 0) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X ≠ 0 :=
  PhysicalUCPConsequences.ae_nonzero B (hreg.data c hc) hN
    (ConfigurationGeometry.regular_isOpen N)
    (ConfigurationGeometry.regular_isConnected N).isPreconnected
    (ConfigurationGeometry.regular_ae N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hu

theorem ae_norm_pos (hu : u ≠ 0) :
    ∀ᵐ X ∂volume, 0 < ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ :=
  (ae_nonzero B hN hreg hc heigen hu).mono fun _ hx => norm_pos_iff.mpr hx

theorem electronic_density_pos (hu : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) x :=
  PhysicalUCPConsequences.electronic_density_pos B (hreg.data c hc) hN
    (ConfigurationGeometry.regular_isOpen N)
    (ConfigurationGeometry.regular_isConnected N).isPreconnected
    (ConfigurationGeometry.regular_ae N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hu

end PfHk.PhysicalFermionicUCP
