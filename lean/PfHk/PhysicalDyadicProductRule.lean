import PfHk.PhysicalDyadicPartition
import PfHk.PhysicalEnlargedFractionalCarleman
import PfHk.PhysicalLocalEnergySobolev
import PfHk.DyadicProductRuleAlgebra

/-! The exact covariant product rule gives the magnetic localization
estimate for the actual standard and enlarged weighted cutoffs. -/

noncomputable section
namespace PfHk.PhysicalDyadicProductRule

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator PfHk.PhysicalDyadicPartition
  PfHk.SmoothCutoffBounds PfHk.SmoothDyadicCutoffs

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000


variable {N : ℕ}

attribute [local irreducible] inclusion covariant PhysicalPFScalarMultiplier.multiply roughMultiply HasMultiplier
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.derivativeMultiplier
  PhysicalEnlargedFractionalCarleman.localized
  PfHk.PhysicalDyadicPartition.localizedField GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier
  PfHk.SmoothDyadicCutoffs.weightedCutoff PfHk.SmoothDyadicCutoffs.Enlarged.weightedCutoff

theorem covariant_product_ae
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
    (a : GptLean.ElectronicH1Multiplier.DifferentiableMultiplier (Fin N × Fin 3))
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (i : Fin N × Fin 3) :
    (fun X : Configuration N => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u) X) =ᵐ[volume]
    fun X : Configuration N => a.weight X • covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u X +
      (-Complex.I) • (a.gradient i X • inclusion (Fin N × Fin 3) (fun _ => 0) u X) := by
  exact multiplier_derivative_ae a i (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u)
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u))
    (PhysicalPFScalarMultiplier.covariant_multiply (I := Fin N × Fin 3)
      (fun _ => 0) a C κ hκ M hbound e u i)

theorem localized_covariant_multiplier_bound
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)
    {O : Configuration N} (family : BufferedFamily O) {R τ α : ℝ}
    (hR : 0 < R) (hsmall : 4 * R ≤ Real.exp (-2))
    (hτ : 1 ≤ τ) (hα : 0 < α)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (i : Fin N × Fin 3)
    (b : Configuration N → ℝ) (j : ℕ)
    (hb : HasMultiplier b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u))
    (hbhigh : HasMultiplier b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i
      (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u j)))
    (hblow : HasMultiplier b (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u j))) :
    ‖localizedField family R hR τ α j
      (roughMultiply b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) hb)‖ ^ 2 ≤
      2 * ‖roughMultiply b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i
        (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u j)) hbhigh‖ ^ 2 +
      (2 * (Enlarged.firstWeightConstant family * τ / radius R j) ^ 2) *
      ‖roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0)
        (PhysicalEnlargedFractionalCarleman.localized family R hR τ α u j)) hblow‖ ^ 2 := by
  unfold PhysicalEnlargedFractionalCarleman.localized at hbhigh hblow ⊢
  let a := (Enlarged.weightedCutoff family R hR τ α j).scalar
  let z := PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u
  let k := Enlarged.firstWeightConstant family * τ / radius R j
  have hk : 0 ≤ k := div_nonneg (mul_nonneg (Enlarged.firstWeightConstant_nonneg family)
    (by linarith only [hτ])) (radius_pos hR j).le
  have hax (X : Configuration N) (hηzero : (cutoff family R j).scalar.weight X ≠ 0) :
      a.weight X = Real.exp (τ * PfHk.CarlemanWeights.weight α (-Real.log (dist X O))) := by
    exact (Enlarged.weightedCutoff_actual_weight family hR hsmall τ α j X).trans
      (by rw [enlarged_eq_one family hR j X hηzero, one_mul])
  have ha (X : Configuration N) (hηzero : (cutoff family R j).scalar.weight X ≠ 0) :
      0 < a.weight X := (hax X hηzero).symm ▸ Real.exp_pos _
  have hd (X : Configuration N) (hηzero : (cutoff family R j).scalar.weight X ≠ 0) :
      |a.gradient i X| ≤ k * a.weight X := by
    have hs := weight_supported family hR j X hηzero
    have hmem : X ∈ Enlarged.dyadicAnnulus O R j :=
      ⟨by linarith only [hs.1, radius_pos hR j], by linarith only [hs.2, radius_pos hR j]⟩
    exact (Enlarged.weightedCutoff_first_bound family hR hsmall hτ hα j X hmem i).trans_eq
      (congrArg (fun v : ℝ => k * v) (hax X hηzero).symm)
  simpa only [localizedField] using product_localization_bound (H := PhotonFock) a (cutoff family R j).scalar
    (weightedCutoff family R hR τ α j).scalar i
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u)
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i z)
    (roughMultiply b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) hb)
    (roughMultiply b (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i z) hbhigh)
    (roughMultiply b (inclusion (Fin N × Fin 3) (fun _ => 0) z) hblow) b hk
    (PhysicalPFScalarMultiplier.value_multiply (I := Fin N × Fin 3) (fun _ => 0) a u)
    (PhysicalPFScalarMultiplier.covariant_multiply (I := Fin N × Fin 3) (fun _ => 0) a C κ hκ M hbound e u i)
    (fun X => (Enlarged.weightedCutoff_product_identity family hR τ α j X).symm)
    (weight_abs_le_one family hR j) ha hd
    (roughMultiply_ae b _ hb) (roughMultiply_ae b _ hbhigh) (roughMultiply_ae b _ hblow)

end PfHk.PhysicalDyadicProductRule
