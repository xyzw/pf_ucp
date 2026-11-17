import PfHk.CenteredPhysicalCoreSupport
import PfHk.PhysicalPolarDensity
import PfHk.CarlemanAnnularWeights

/-! Integrability of the actual original PF core densities, including the
Carleman weights on a fixed spatial annulus. -/

noncomputable section
namespace PfHk.PhysicalPolarDensity

open MeasureTheory Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.SymmetricLift GptLean.Representability
  PfHk.PhysicalFieldRegularity PfHk.PhysicalOperatorDomain
  PfHk.CenteredRadialGauge PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

local instance coreSpatialPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

private theorem norm_sq_zero {H : Type*} [NormedAddCommGroup H] {q : H} (hq : q = 0) :
    ‖q‖ ^ 2 = 0 := by rw [hq, norm_zero, zero_pow (by decide : 2 ≠ 0)]

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.inclusion
  PhysicalPFReference.radiation PhysicalPFReference.referenceSubspace
  radiationGraphInclusion radiationGraphDerivative kernelField SmoothCore.reference

variable {N : ℕ} {s : Set (Configuration N)} (a : SmoothCore s)
  (F : Frame) (χ : ArticleCutoff) (e : ℝ) (O : Configuration N)
  (C : CanonicalSectorCCR photonMeasure)

theorem core_mass_integrable : Integrable (mass a.rootWave) :=
  (radiationGraphInclusion.comp_memLp' a.rootWave_memLp).norm.integrable_sq

theorem core_reference_covariant_ae (j : Fin N × Fin 3) :
    covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j a.reference
      =ᵐ[volume] coreCovariant F χ e O C a.rootWave j := by
  unfold SmoothCore.reference
  exact (C1ReferenceCore.reference_covariant C (profile F χ O)
    (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e
    a.rootWave a.rootWave_memLp a.value_smooth a.value_compact j).trans
      (Filter.EventuallyEq.of_eq (funext fun X => covariantFunction_eq F χ O C e a.rootWave j X))

theorem core_reference_radiation_ae :
    PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) a.reference
      =ᵐ[volume] fun X => radiationGraphDerivative (a.rootWave X) := by
  unfold SmoothCore.reference
  exact C1ReferenceCore.reference_radiation_ae a.rootWave a.rootWave_memLp
    a.value_smooth a.value_compact

theorem core_covariant_memLp (j : Fin N × Fin 3) :
    MemLp (coreCovariant F χ e O C a.rootWave j) 2 volume := by
  exact (memLp_congr_ae (core_reference_covariant_ae a F χ e O C j)).mp (Lp.memLp _)

theorem core_covariant_supported (j : Fin N × Fin 3) :
    ∀ᵐ X ∂volume, X ∉ s → covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j a.reference X = 0 := by
  filter_upwards [core_reference_covariant_ae a F χ e O C j] with X hX hs
  exact hX.trans (coreCovariant_eq_zero_of_notMem a F χ e O C hs j)

theorem core_radiation_supported :
    ∀ᵐ X ∂volume, X ∉ s → PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0)
      a.reference X = 0 := by
  filter_upwards [core_reference_radiation_ae a] with X hX hs
  exact hX.trans ((congrArg radiationGraphDerivative (rootWave_eq_zero_of_notMem a hs)).trans
    (map_zero radiationGraphDerivative))

theorem core_kinetic_integrable : Integrable (kinetic F χ e O C a.rootWave) :=
  integrable_finsetSum _ fun j _ => (core_covariant_memLp a F χ e O C j).norm.integrable_sq

theorem core_radiation_integrable : Integrable (radiation a.rootWave) :=
  (radiationGraphDerivative.comp_memLp' a.rootWave_memLp).norm.integrable_sq

theorem core_densities_zero {X : Configuration N} (hX : X ∉ s) :
    mass a.rootWave X = 0 ∧ kinetic F χ e O C a.rootWave X = 0 ∧
      radiation a.rootWave X = 0 := by
  have hq := rootWave_eq_zero_of_notMem a hX
  have hD := coreCovariant_eq_zero_of_notMem a F χ e O C hX
  constructor
  · exact norm_sq_zero ((congrArg radiationGraphInclusion hq).trans (map_zero radiationGraphInclusion))
  constructor
  · unfold kinetic
    exact Finset.sum_eq_zero fun j _ => norm_sq_zero (hD j)
  · exact norm_sq_zero ((congrArg radiationGraphDerivative hq).trans (map_zero radiationGraphDerivative))

theorem core_weighted_density_integrable (τ α : ℝ) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : R < 1) (hs : s ⊆ CarlemanSpatialDensity.annulus ρ R) :
    Integrable (CarlemanSpatialDensity.density τ α (mass a.rootWave)
      (kinetic F χ e O C a.rootWave) (radiation a.rootWave)) :=
  CarlemanSpatialDensity.density_integrable τ α hρ hR
    (mass a.rootWave) (kinetic F χ e O C a.rootWave) (radiation a.rootWave)
    (core_mass_integrable a) (core_kinetic_integrable a F χ e O C)
    (core_radiation_integrable a)
    (ae_of_all _ fun X hX => core_densities_zero a F χ e O C (fun h => hX (hs h)))

theorem core_weighted_density_integrableOn (τ α : ℝ) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : R < 1) (hs : s ⊆ CarlemanSpatialDensity.annulus ρ R)
    (t : Set (Configuration N)) :
    IntegrableOn (CarlemanSpatialDensity.density τ α (mass a.rootWave)
      (kinetic F χ e O C a.rootWave) (radiation a.rootWave)) t :=
  (core_weighted_density_integrable a F χ e O C τ α hρ hR hs).integrableOn

end PfHk.PhysicalPolarDensity
