import PfHk.PauliCaccioppoli
import PfHk.PauliScalarSobolev
import PfHk.DensityFlatPoint
import PfHk.ScalarSobolevFromWeak

/-! Density points of the zero set of a physical weak Pauli eigenstate
are infinite-order zeros. The scalar Sobolev input and ball cutoffs are
constructed, and all energy bounds use the coupled weak equation. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliInfiniteOrder

open MeasureTheory Filter Set GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliSpin
  PfHk.UniqueContinuationDensity
open scoped ENNReal Topology

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace GptLean.PhysicalPFReference.inclusion ordinary radiation rawCovariant
  externalCovariant PhysicalPFScalarMultiplier.multiply PauliReference.wave

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

theorem caccioppoli_normGradient {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff O r L) :
    normGradientEnergy (PauliLocalEnergy.localize a.multiplier u) ≤
      PauliCaccioppoli.ordinaryConstant (N := N) M e A v c hc E L / r ^ 2 *
        localMass (μ := volume) (PauliReference.wave u) O (2*r) :=
  (normGradientEnergy_le_ordinaryEnergy _).trans
    ((le_add_of_nonneg_right (radiationEnergy_nonneg _)).trans
      (PauliCaccioppoli.localized_ordinary_radiation C κ hκ M hκbound e A v c hc heigen hr hr1 a))

theorem flat_at_zero_density {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {p q S L : ℝ} (hpq : p.HolderConjugate q) (hS : 0 ≤ S)
    (hSob : PhysicalInfiniteOrder.ScalarSobolevBound (I := Fin N × Fin 3) p S)
    (O : Configuration N) (a : ∀ r : Ioc (0 : ℝ) 1, BallCutoff O r L)
    (hdensity : Tendsto (fun r =>
      (volume (nonzeroRegion (PauliReference.wave u) O r)).toReal / r ^ (2*q))
      (𝓝[>] 0) (𝓝 0)) :
    InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O) := by
  classical
  let η : ℝ → Configuration N → ℝ := fun r =>
    if h : r ∈ Ioc (0 : ℝ) 1 then (a ⟨r,h⟩).multiplier.weight else fun _ => 0
  let G : ℝ → ℝ := fun r => if h : r ∈ Ioc (0 : ℝ) 1 then
    normGradientEnergy (PauliLocalEnergy.localize (a ⟨r,h⟩).multiplier u) else 0
  have hψ := (Lp.memLp (PauliReference.wave u)).norm.integrable_sq
  have hZ : MeasurableSet {X | PauliReference.wave u X ≠ 0} := by
    simpa only [norm_pos_iff] using measurableSet_lt
      (measurable_const : Measurable (fun _ : Configuration N => (0 : ℝ)))
      (Lp.stronglyMeasurable (PauliReference.wave u)).norm.measurable
  refine flat_at_zero_density_point (η := η) (G := G)
    (S := S) (K := PauliCaccioppoli.ordinaryConstant (N := N) M e A v c hc E L) (R₀ := 1)
    hpq hS zero_lt_one hψ hdensity (fun r => Metric.isOpen_ball.measurableSet.inter hZ)
    (fun r => (measure_mono inter_subset_left).trans_lt measure_ball_lt_top) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr hr1 X hX
    simpa only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)] using
      (a ⟨r,hr,hr1⟩).eq_one X hX
  · intro r hr hr1 X hX
    simpa only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)] using
      (a ⟨r,hr,hr1⟩).eq_zero X hX
  · intro r hr hr1
    simp only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)]
    exact ((Lp.memLp (PauliReference.wave
      (PauliLocalEnergy.localize (a ⟨r,hr,hr1⟩).multiplier u))).norm.integrable_sq).congr
        (localized_norm_sq_ae _ (a ⟨r,hr,hr1⟩).nonneg u)
  · intro r hr hr1
    simp only [η, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)]
    exact (localized_scalar_sobolev hSob _ (a ⟨r,hr,hr1⟩).nonneg u).1
  · intro r hr hr1
    simp only [η, G, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)]
    exact (localized_scalar_sobolev hSob _ (a ⟨r,hr,hr1⟩).nonneg u).2
  · intro r hr hr1
    simp only [G, dite_eq_left (show r ∈ Ioc (0 : ℝ) 1 from ⟨hr,hr1⟩)]
    exact caccioppoli_normGradient C κ hκ M hκbound e A v c hc heigen hr hr1 (a ⟨r,hr,hr1⟩)

theorem exists_flat_point_of_sobolev {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {p q S : ℝ} (hpq : p.HolderConjugate q) (hd : (Fintype.card (Fin N × Fin 3) : ℝ) = 2*q)
    (hS : 0 ≤ S) (hSob : PhysicalInfiniteOrder.ScalarSobolevBound (I := Fin N × Fin 3) p S)
    {U : Set (Configuration N)} (hfull : ∀ᵐ X ∂volume, X ∈ U)
    (hpositive : 0 < volume {X | PauliReference.wave u X = 0}) :
    ∃ O ∈ U, PauliReference.wave u O = 0 ∧
      InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O) :=
  exists_flat_point_of_density (ψ := PauliReference.wave u) hd
    (Lp.stronglyMeasurable (PauliReference.wave u)).norm.measurable hfull hpositive
    (fun O hdensity => flat_at_zero_density C κ hκ M hκbound e A v c hc
      heigen hpq hS hSob O (fun r => ballCutoff O r r.property.1) hdensity)

theorem exists_flat_point {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u)) (hN : 0 < N)
    {U : Set (Configuration N)} (hfull : ∀ᵐ X ∂volume, X ∈ U)
    (hpositive : 0 < volume {X | PauliReference.wave u X = 0}) :
    ∃ O ∈ U, PauliReference.wave u O = 0 ∧
      InfiniteOrder.FlatAtZero (localMass (μ := volume) (PauliReference.wave u) O) := by
  have hd : 2 < Fintype.card (Fin N × Fin 3) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hex := ScalarSobolevFromWeak.exists_scalarSobolevBound hd
  let p := Classical.choose hex
  have h₁ := Classical.choose_spec hex
  let q := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let S := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  exact exists_flat_point_of_sobolev C κ hκ M hκbound e A v c hc heigen
    h₃.1 h₃.2.1 h₃.2.2.1 h₃.2.2.2 hfull hpositive

end PfHk.PauliInfiniteOrder

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
