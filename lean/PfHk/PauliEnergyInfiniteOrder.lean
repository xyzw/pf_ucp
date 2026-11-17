import PfHk.PauliCaccioppoli
import PfHk.InfiniteOrderMonotone
import PfHk.UniqueContinuationDensity

/-! Infinite-order mass decay implies decay of the actual covariant
energies of every spin component of the coupled Pauli state. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliInfiniteOrder

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliSpin
  PfHk.UniqueContinuationDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion ordinary radiation rawCovariant
  externalCovariant PhysicalPFScalarMultiplier.multiply

theorem component_mass_flat_of_mass_flat {u : Ref N} {O : Configuration N}
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O))
    (s : SpinIndex N) :
    InfiniteOrder.FlatAtZero (fun r => PhysicalLocalEnergy.massOn (Metric.ball O r)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) := by
  apply InfiniteOrder.FlatAtZero.mono hflat
  intro r _
  exact PauliCaccioppoli.component_mass_le (Metric.ball O r) u s

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

theorem energy_flat_of_mass_flat {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N}
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O)) :
    InfiniteOrder.FlatAtZero (fun r =>
      PauliCaccioppoli.ordinaryEnergyOn (Metric.ball O r) u +
      PauliCaccioppoli.covariantEnergyOn C κ hκ M hκbound e A v c hc (Metric.ball O r) u +
      PauliCaccioppoli.radiationEnergyOn (Metric.ball O r) u) := by
  have hex := PauliCaccioppoli.exists_caccioppoli_constant C κ hκ M hκbound e A v c hc heigen
  let K := Classical.choose hex
  have hK := Classical.choose_spec hex
  apply InfiniteOrder.energy_flat_of_mass_flat (K := K + 1) (R₀ := 1)
    (by linarith only [hK.1]) zero_lt_one hflat
  intro r hr hr1
  exact (hK.2 O r hr hr1).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) (sq_nonneg r))
      (PauliCaccioppoli.massOn_nonneg _ u))

theorem covariant_energy_flat_of_mass_flat {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N}
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O)) :
    InfiniteOrder.FlatAtZero (fun r =>
      PauliCaccioppoli.covariantEnergyOn C κ hκ M hκbound e A v c hc (Metric.ball O r) u) := by
  apply InfiniteOrder.FlatAtZero.mono
    (energy_flat_of_mass_flat C κ hκ M hκbound e A v c hc heigen hflat)
  intro r _
  have ho : 0 ≤ PauliCaccioppoli.ordinaryEnergyOn (Metric.ball O r) u :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => massOn_nonneg _ _
  have hr : 0 ≤ PauliCaccioppoli.radiationEnergyOn (Metric.ball O r) u :=
    Finset.sum_nonneg fun _ _ => massOn_nonneg _ _
  exact (le_add_of_nonneg_left ho).trans (le_add_of_nonneg_right hr)

theorem component_covariant_energy_flat_of_mass_flat {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N}
    (hflat : InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O))
    (s : SpinIndex N) :
    InfiniteOrder.FlatAtZero (fun r => ∑ q, PhysicalLocalEnergy.massOn (Metric.ball O r)
      (externalCovariant (fun _ => 0) C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
        (u s) (physicalDomain A v c hc u s) q)) := by
  apply InfiniteOrder.FlatAtZero.mono
    (covariant_energy_flat_of_mass_flat C κ hκ M hκbound e A v c hc heigen hflat)
  intro r _
  unfold PauliCaccioppoli.covariantEnergyOn rawCovariant
  exact Finset.single_le_sum
    (f := fun t : SpinIndex N => ∑ q : Fin N × Fin 3,
      PhysicalLocalEnergy.massOn (Metric.ball O r)
        (externalCovariant (fun _ => 0) C κ hκ M hκbound e
          (vector A) (positive v c) (negative v c) (u t) (physicalDomain A v c hc u t) q))
    (fun t _ => Finset.sum_nonneg fun q _ => massOn_nonneg _ _) (Finset.mem_univ s)

end PfHk.PauliInfiniteOrder

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
