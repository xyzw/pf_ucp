import GptLean.PhysicalFockChannel

/-!
The one-photon coassociativity identities for separated physical cutoffs.
They identify two successive retained splittings with a single retained
splitting followed by an isometry acting only on its environment.
-/

noncomputable section
namespace GptLean.PhysicalFock.CutoffComposition

open MeasureTheory PhotonLocalizationKernelCutoffs PhotonLocalizationFockChannel
open scoped ENNReal

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]

omit [MeasurableSpace P] [BorelSpace P] in
theorem discarded_absorption {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : 2 * r ≤ s) (y : P) : discarded s y * discarded r y = discarded s y := by
  have hA := retained_absorption hr hs hrs y
  have hR := square_partition r y
  have hS := square_partition s y
  have hDr := discarded_nonneg r y
  have hDs := discarded_nonneg s y
  by_cases hz : retained r y = 0
  · have h : discarded r y = 1 := by rw [hz] at hR; nlinarith
    rw [h, mul_one]
  · have hp : 0 < retained r y := lt_of_le_of_ne (retained_nonneg r y) (Ne.symm hz)
    have h : retained s y = 1 := by nlinarith
    have hd : discarded s y = 0 := by rw [h] at hS; nlinarith
    rw [hd, zero_mul]

def discardMap (r : ℝ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (WithLp.sndL 2 ℂ _ _).comp (complexOnePhotonIsometry r).toContinuousLinearMap

omit [IsScalarTower ℝ ℂ E] in
@[simp] theorem discardMap_apply (r : ℝ) (u : Lp E 2 μ) :
    discardMap r u = discardedOperator r u := rfl

omit [IsScalarTower ℝ ℂ E] in
theorem discarded_retained_commute (r s : ℝ) (u : Lp E 2 μ) :
    discardMap r (cutoffMap s u) = cutoffMap s (discardMap r u) := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded r) (discarded_measurable r) (ae_of_all _ (discarded_abs_le_one r))
      (retainedOperator s u),
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained s) (retained_measurable s) (ae_of_all _ (retained_abs_le_one s)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (retained s) (retained_measurable s) (ae_of_all _ (retained_abs_le_one s))
      (discardedOperator r u),
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded r) (discarded_measurable r) (ae_of_all _ (discarded_abs_le_one r)) u]
    with y h₁ h₂ h₃ h₄
  change discardedOperator r (retainedOperator s u) y = retainedOperator s (discardedOperator r u) y
  rw [show discardedOperator r (retainedOperator s u) y =
      discarded r y • retainedOperator s u y from h₁,
    show retainedOperator s u y = retained s y • u y from h₂,
    show retainedOperator s (discardedOperator r u) y =
      retained s y • discardedOperator r u y from h₃,
    show discardedOperator r u y = discarded r y • u y from h₄,
    smul_smul, smul_smul, mul_comm]

omit [IsScalarTower ℝ ℂ E] in
theorem discardMap_absorption {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : 2 * r ≤ s) (u : Lp E 2 μ) :
    discardMap s (discardMap r u) = discardMap s u := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded s) (discarded_measurable s) (ae_of_all _ (discarded_abs_le_one s))
      (discardedOperator r u),
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded r) (discarded_measurable r) (ae_of_all _ (discarded_abs_le_one r)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae
      (discarded s) (discarded_measurable s) (ae_of_all _ (discarded_abs_le_one s)) u]
    with y h₁ h₂ h₃
  change discardedOperator s (discardedOperator r u) y = discardedOperator s u y
  rw [show discardedOperator s (discardedOperator r u) y =
      discarded s y • discardedOperator r u y from h₁,
    show discardedOperator r u y = discarded r y • u y from h₂,
    show discardedOperator s u y = discarded s y • u y from h₃,
    smul_smul, discarded_absorption hr hs hrs]

omit [IsScalarTower ℝ ℂ E] in
/-- All three components of the two one-photon dilation orders coincide. -/
theorem three_components {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : 2 * r ≤ s) (u : Lp E 2 μ) :
    cutoffMap r (cutoffMap s u) = cutoffMap r u ∧
      discardMap r (cutoffMap s u) = cutoffMap s (discardMap r u) ∧
      discardMap s u = discardMap s (discardMap r u) :=
  ⟨retainedOperator_absorption hr hs hrs u,
    discarded_retained_commute r s u, (discardMap_absorption hr hs hrs u).symm⟩

end GptLean.PhysicalFock.CutoffComposition
