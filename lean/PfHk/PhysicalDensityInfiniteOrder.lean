import PfHk.PhysicalEnergyInfiniteOrder

noncomputable section
namespace PfHk.PhysicalInfiniteOrder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
open PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 10000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant

variable {I : Type} [Fintype I] [DecidableEq I]
variable (V : Position I → ℝ)
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- Infinite-order vanishing of the actual PF eigenstate at a density point
of its zero set. Caccioppoli is supplied by the proved physical theorem. -/
theorem physical_flat_at_zero_density {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hnegative : ScalarMultiplierBound negative (1 / 4) C₀)
    {p q S L : ℝ} (hpq : p.HolderConjugate q) (hS : 0 ≤ S)
    (hSob : ScalarSobolevBound (I := I) p S)
    (x₀ : Position I)
    (a : ∀ r : Ioc (0 : ℝ) 1, BallCutoff x₀ r L)
    (hdensity : Tendsto (fun r =>
      (volume (nonzeroRegion (inclusion I V u) x₀ r)).toReal / r ^ (2 * q))
      (𝓝[>] 0) (𝓝 0)) :
    InfiniteOrder.FlatAtZero (localMass (μ := volume) (inclusion I V u) x₀) := by
  classical
  let η : ℝ → Position I → ℝ := fun r =>
    if h : r ∈ Ioc (0 : ℝ) 1 then (a ⟨r, h⟩).multiplier.weight else fun _ => 0
  let G : ℝ → ℝ := fun r => if h : r ∈ Ioc (0 : ℝ) 1 then
    normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V (a ⟨r, h⟩).multiplier u) else 0
  have hψ := (Lp.memLp (inclusion I V u)).norm.integrable_sq
  have hZ : MeasurableSet {x | inclusion I V u x ≠ 0} := by
    simpa only [norm_pos_iff] using measurableSet_lt (measurable_const : Measurable (fun _ : Position I => (0 : ℝ)))
      (Lp.stronglyMeasurable (inclusion I V u)).norm.measurable
  refine flat_at_zero_density_point (η := η) (G := G)
    (S := S) (K := 8 * (|E| + |C₀|) + 4 * Fintype.card I * L ^ 2) (R₀ := 1)
    hpq hS zero_lt_one hψ hdensity (fun r => Metric.isOpen_ball.measurableSet.inter hZ)
    (fun r => (measure_mono inter_subset_left).trans_lt measure_ball_lt_top) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr hr1 x hx
    simpa only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)] using
      (a ⟨r, hr, hr1⟩).eq_one x hx
  · intro r hr hr1 x hx
    simpa only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)] using
      (a ⟨r, hr, hr1⟩).eq_zero x hx
  · intro r hr hr1
    simp only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)]
    exact ((Lp.memLp (inclusion I V
      (PhysicalPFScalarMultiplier.multiply V (a ⟨r, hr, hr1⟩).multiplier u))).norm.integrable_sq).congr
        (localized_norm_sq_ae V _ (a ⟨r, hr, hr1⟩).nonneg u)
  · intro r hr hr1
    simp only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)]
    exact (localized_scalar_sobolev V hSob _ (a ⟨r, hr, hr1⟩).nonneg u).1
  · intro r hr hr1
    simp only [η, G, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)]
    exact (localized_scalar_sobolev V hSob _ (a ⟨r, hr, hr1⟩).nonneg u).2
  · intro r hr hr1
    simp only [G, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1⟩)]
    exact caccioppoli_normGradient V C κ hκ M hbound e A positive negative
      heigen C₀ hnegative hr hr1 (a ⟨r, hr, hr1⟩)


end PfHk.PhysicalInfiniteOrder
