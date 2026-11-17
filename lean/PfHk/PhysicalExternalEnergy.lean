import PfHk.PhysicalDyadicPartition
import PfHk.WeightedCovariantEnergy

/-! The actual external covariant derivative in the Carleman density.
The extra kinetic contribution is the multiplication field A u. -/

noncomputable section
namespace PfHk.PhysicalExternalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  PfHk.CenteredPhysicalReference PfHk.PhysicalFieldRegularity
  PfHk.PhysicalLocalEnergy PfHk.PhysicalDyadicEnergy PfHk.PhysicalFreeCarleman
  PfHk.PhysicalCarlemanInput PfHk.PhysicalOperatorDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

local instance externalEnergyPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PfHk.PhysicalDyadicEnergy.dyadicEnergyPhotonRealInner

attribute [local irreducible] inclusion covariant radiation roughMultiply externalCovariant
  PhysicalPFReference.referenceSubspace

private theorem integral_three {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {m k r : X → ℝ} (hm : Integrable m μ) (hk : Integrable k μ) (hr : Integrable r μ) :
    (∫ x, m x + k x + r x ∂μ) = (∫ x, m x ∂μ) + (∫ x, k x ∂μ) + ∫ x, r x ∂μ := by
  simpa only [Pi.add_apply] using
    (integral_add (hm.add hk) hr).trans
      (congrArg (fun z => z + ∫ x, r x ∂μ) (integral_add hm hk))

private theorem energy_arithmetic (m r k p a : ℝ) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hp : p ≤ 2 * k + 2 * a) : m + p + r ≤ 2 * (m + k + r) + 2 * a := by
  linarith only [hm, hr, hp]

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ) (positive negative : Configuration N → ℝ)

def positiveKinetic (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u) (X : Configuration N) : ℝ :=
  positiveKineticWeight O τ α X * ∑ i,
    ‖externalCovariant (fun _ => 0) C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu i X‖ ^ 2

def density (O : Configuration N) (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u) (X : Configuration N) : ℝ :=
  massEnergy O τ α u X + positiveKinetic F χ C e A positive negative O τ α u hu X +
    radiationEnergy O τ α u X

theorem positiveKineticWeight_measurable (O : Configuration N) (τ α : ℝ) :
    Measurable (positiveKineticWeight O τ α) := by
  unfold positiveKineticWeight centeredKineticWeight CarlemanSpatialDensity.kineticWeight
    CarlemanWeights.weight CarlemanWeights.beta
  fun_prop

theorem density_bound
    {O : Configuration N} {R τ α : ℝ}
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ExternalDomain (fun _ => 0) A positive negative u)
    (f : WaveSpace (Fin N × Fin 3))
    (hd : EnergyData F χ C e O R τ α u f)
    (ha : ∀ i, Integrable (fun X => positiveKineticWeight O τ α X *
      ‖roughMultiply (A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hu.vector i) X‖ ^ 2)) :
    Integrable (density F χ C e A positive negative O τ α u hu) ∧
      (∫ X, density F χ C e A positive negative O τ α u hu X) ≤
        2 * (∫ X, centeredOperatorDensity F χ C e O τ α u X) +
          2 * ∑ i, ∫ X, positiveKineticWeight O τ α X *
            ‖roughMultiply (A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hu.vector i) X‖ ^ 2 := by
  classical
  let d := fun i => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e i u
  let a := fun i => roughMultiply (A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hu.vector i)
  let p := fun i => externalCovariant (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e A positive negative u hu i
  have heq (i : Fin N × Fin 3) : (fun X => p i X) =ᵐ[volume] fun X => d i X + a i X := by
    have hp : p i = d i + a i := by
      unfold p externalCovariant
      rfl
    exact (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ⇑z) hp)).trans
      (Lp.coeFn_add (d i) (a i))
  have hm : AEStronglyMeasurable (fun X => positiveKineticWeight O τ α X * ∑ i, ‖p i X‖ ^ 2)
      volume := (positiveKineticWeight_measurable O τ α).aestronglyMeasurable.mul
    (Finset.univ.aestronglyMeasurable_fun_sum fun i _ => (Lp.aestronglyMeasurable (p i)).norm.pow 2)
  have hD : Integrable (fun X => positiveKineticWeight O τ α X * ∑ i, ‖d i X‖ ^ 2) :=
    hd.kinetic_integrable.congr hd.positive_kinetic_eq.symm
  have hp := WeightedCovariantEnergy.sum_add_integrable_bound (positiveKineticWeight O τ α)
    (fun i X => d i X) (fun i X => a i X) (fun i X => p i X)
    (ae_of_all _ fun X => le_max_left _ _) heq hm hD ha
  have hfull : Integrable (density F χ C e A positive negative O τ α u hu) :=
    (hd.mass_integrable.add hp.1).add hd.radiation_integrable
  have hfreeIntegral : (∫ X, centeredOperatorDensity F χ C e O τ α u X) =
      (∫ X, massEnergy O τ α u X) + (∫ X, kineticEnergy F χ C e O τ α u X) +
        ∫ X, radiationEnergy O τ α u X := by
    simp_rw [density_eq_energies]
    exact integral_three hd.mass_integrable hd.kinetic_integrable hd.radiation_integrable
  have hfullIntegral : (∫ X, density F χ C e A positive negative O τ α u hu X) =
      (∫ X, massEnergy O τ α u X) + (∫ X, positiveKinetic F χ C e A positive negative O τ α u hu X) +
        ∫ X, radiationEnergy O τ α u X := by
    unfold density
    exact integral_three hd.mass_integrable hp.1 hd.radiation_integrable
  have hposIntegral : (∫ X, positiveKineticEnergy F χ C e O τ α u X) =
      ∫ X, kineticEnergy F χ C e O τ α u X := integral_congr_ae hd.positive_kinetic_eq
  have hm0 := integral_nonneg_of_ae hd.mass_nonneg
  have hr0 := integral_nonneg_of_ae hd.radiation_nonneg
  let extra : ℝ := ∑ i, ∫ X, positiveKineticWeight O τ α X * ‖a i X‖ ^ 2
  have hbound : (∫ X, positiveKinetic F χ C e A positive negative O τ α u hu X) ≤
      2 * (∫ X, kineticEnergy F χ C e O τ α u X) + 2 * extra :=
    hp.2.trans_eq (congrArg (fun z : ℝ => 2 * z + 2 * extra) hposIntegral)
  exact ⟨hfull, hfullIntegral.le.trans
    ((energy_arithmetic _ _ _ _ extra hm0 hr0 hbound).trans_eq
      (congrArg (fun z : ℝ => 2 * z + 2 * extra) hfreeIntegral.symm))⟩

end PfHk.PhysicalExternalEnergy
