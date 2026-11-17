import PfHk.PhysicalFermionicReduction
import PfHk.PhysicalOpenRegularity
import PfHk.ExceptionalConfigurationGeometry
import PfHk.PhysicalOpenUCPConsequences

/-! Unique continuation for the actual fermionic external form. The weak
equation is only required on fermionic tests. Local regularity and
distributional divergence are required only on the connected open
full-measure one-body set. The collision-free geometry,
scalar Sobolev bound and physical Carleman estimate are derived. -/

noncomputable section
namespace PfHk.PhysicalOpenFermionicUCP

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.PhysicalPairDuality
  PfHk.PhysicalFermionicWeakEquation PfHk.PhysicalOpenUCPCoefficients
  PfHk.PhysicalFermionicAverage PfHk.UniqueContinuationDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] inclusion PhysicalPFReference.referenceSubspace
  PhysicalLocalEnergy.IsExternalWeakEigenstate

/-- The actual one-body coefficients and Coulomb interaction on the regular
configuration region. No coefficient outside the open set is modified. -/
def coefficientData {N : ℕ} {A : VectorPotential} {v : ScalarPotential}
    {Ω : Set GptLean.PhysicalSourceCoordinates.Position} (hΩ : IsOpen Ω)
    (hreg : RegularityOn A v Ω) (c : ℝ) (hc : 0 ≤ c) :
    PhysicalOpenUCPCoefficients.Data N
      (ExceptionalConfigurationGeometry.configurationDomain Ω N) :=
  hreg.data hΩ (fun _ hX => hX.2) (fun _ hX => hX.1) c hc

variable {N : ℕ} {F : Frame} {χ : ArticleCutoff} {C : CanonicalSectorCCR photonMeasure} {e : ℝ}
  (B : PhysicalUCPConsequences.Backgrounds (N := N) F χ C e) (hN : 0 < N)
  {Ω : Set GptLean.PhysicalSourceCoordinates.Position}
  (hΩ : IsOpen Ω) (hconnected : IsConnected Ω)
  (hfull : ∀ᵐ x ∂volume, x ∈ Ω)
  {A : VectorPotential} {v : ScalarPotential} (hreg : RegularityOn A v Ω)
  {c : ℝ} (hc : 0 ≤ c) {E : ℝ} {u : Ref N}
  (heigen : IsFermionicWeakEigenstate F χ C e A v c hc E u)

include B hN hΩ hconnected hfull hreg heigen

/-- An infinite-order zero away from collisions and the exceptional set
forces the physical fermionic weak eigenstate to vanish globally almost
everywhere. -/
theorem zero_of_infinite_order {X₀ : GptLean.SymmetricLift.Configuration N}
    (hX₀ : X₀ ∈ ExceptionalConfigurationGeometry.configurationDomain Ω N)
    (hflat : InfiniteOrder.FlatAtZero
      (localMass (μ := volume) (inclusion (Fin N × Fin 3) (fun _ => 0) u) X₀)) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 :=
  PhysicalOpenUCPConsequences.zero_of_infinite_order B (coefficientData hΩ hreg c hc) hN
    (ExceptionalConfigurationGeometry.configurationDomain_isOpen hΩ N)
    (ExceptionalConfigurationGeometry.configurationDomain_isPreconnected hΩ hconnected.isPreconnected N)
    (ExceptionalConfigurationGeometry.configurationDomain_ae hfull N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen)
    hX₀ hflat

theorem zero_of_positive_zero_measure
    (hpositive : 0 < volume {X | inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0}) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X = 0 :=
  PhysicalOpenUCPConsequences.zero_of_positive_zero_measure B (coefficientData hΩ hreg c hc) hN
    (ExceptionalConfigurationGeometry.configurationDomain_isOpen hΩ N)
    (ExceptionalConfigurationGeometry.configurationDomain_isPreconnected hΩ hconnected.isPreconnected N)
    (ExceptionalConfigurationGeometry.configurationDomain_ae hfull N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hpositive

theorem ae_nonzero (hu : u ≠ 0) :
    ∀ᵐ X ∂volume, inclusion (Fin N × Fin 3) (fun _ => 0) u X ≠ 0 :=
  PhysicalOpenUCPConsequences.ae_nonzero B (coefficientData hΩ hreg c hc) hN
    (ExceptionalConfigurationGeometry.configurationDomain_isOpen hΩ N)
    (ExceptionalConfigurationGeometry.configurationDomain_isPreconnected hΩ hconnected.isPreconnected N)
    (ExceptionalConfigurationGeometry.configurationDomain_ae hfull N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hu

theorem ae_norm_pos (hu : u ≠ 0) :
    ∀ᵐ X ∂volume, 0 < ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ :=
  (ae_nonzero B hN hΩ hconnected hfull hreg hc heigen hu).mono fun _ hx => norm_pos_iff.mpr hx

theorem electronic_density_pos (hu : u ≠ 0) :
    ∀ᵐ x ∂volume, 0 < PhysicalElectronicDensity.density
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) x :=
  PhysicalOpenUCPConsequences.electronic_density_pos B (coefficientData hΩ hreg c hc) hN
    (ExceptionalConfigurationGeometry.configurationDomain_isOpen hΩ N)
    (ExceptionalConfigurationGeometry.configurationDomain_isPreconnected hΩ hconnected.isPreconnected N)
    (ExceptionalConfigurationGeometry.configurationDomain_ae hfull N)
    (PhysicalFermionicReduction.full_weak_of_fermionic_weak F χ C e A v c hc heigen) hu

end PfHk.PhysicalOpenFermionicUCP
