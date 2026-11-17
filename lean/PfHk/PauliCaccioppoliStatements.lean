import PfHk.PauliCaccioppoli

/-! Statement-level form of `ucp-caccioppoli-spin` (ii). The ordinary
gradient of the localized spinor is bounded by the spinor mass on the
doubled ball, for every admissible cutoff. One constant serves every
center, every radius at most one and every cutoff with the given gradient
constant. Part (i) is `PauliCaccioppoli.exists_caccioppoli_constant`. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCaccioppoli

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant externalCovariant roughMultiply rawEnergy
  PhysicalPFScalarMultiplier.multiply

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

/-- The ordinary gradient energy of the localized spinor, for one cutoff. -/
theorem localized_gradient {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff O r L) :
    ordinaryEnergy (PauliLocalEnergy.localize a.multiplier u) ≤
      ordinaryConstant (N := N) M e A v c hc E L / r ^ 2 * massOn (Metric.ball O (2*r)) u :=
  (le_add_of_nonneg_right (radiationEnergy_nonneg _)).trans
    (localized_ordinary_radiation C κ hκ M hκbound e A v c hc heigen hr hr1 a)

/-- `ucp-caccioppoli-spin` (ii). The constant depends on the cutoff only
through its gradient constant `L`. -/
theorem exists_localized_gradient_constant {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u)) (L : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (O : Configuration N) (r : ℝ), 0 < r → r ≤ 1 →
      ∀ a : BallCutoff O r L,
      ordinaryEnergy (PauliLocalEnergy.localize a.multiplier u) ≤
        K / r ^ 2 * massOn (Metric.ball O (2*r)) u :=
  ⟨ordinaryConstant (N := N) M e A v c hc E L, ordinaryConstant_nonneg M e A v c hc E L,
    fun _ _ hr hr1 a => localized_gradient C κ hκ M hκbound e A v c hc heigen hr hr1 a⟩

end PfHk.PauliCaccioppoli

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
