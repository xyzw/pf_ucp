import GptLean.PhysicalFockSoftRadiationBound
import GptLean.PhysicalFockHardRadiation

/-!
Complementary momentum projections partition the actual radiation form.
The retained hard channel therefore has exactly the hard-root norm, with
no infrared-number or replacement-form hypothesis.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFormBounds PhotonLocalizationFockChannel PhotonLocalizationChannel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

theorem radiationFamily_projection_partition (s : Set PhotonMode) (hs : MeasurableSet s)
    (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue radiationFamily (MomentumSplit.projection photonMeasure s hs u) +
      onePhotonFamilyValue radiationFamily (MomentumSplit.projection photonMeasure sᶜ hs.compl u) =
        onePhotonFamilyValue radiationFamily u := by
  classical
  have hm : AEMeasurable (fun p : PhotonMode => ENNReal.ofReal ‖p.1‖ *
      ENNReal.ofReal (‖MomentumSplit.projection photonMeasure s hs u p‖ ^ 2)) photonMeasure :=
    measurable_fst.norm.ennreal_ofReal.aemeasurable.mul
      (((Lp.aestronglyMeasurable (MomentumSplit.projection photonMeasure s hs u)).norm.pow 2).aemeasurable.ennreal_ofReal)
  rw [radiationFamily_value, radiationFamily_value, radiationFamily_value,
    ← lintegral_add_left' hm]
  apply lintegral_congr_ae
  filter_upwards [MomentumSplit.projection_ae photonMeasure s hs u,
    MomentumSplit.projection_ae photonMeasure sᶜ hs.compl u] with p hp hc
  rw [hp, hc]
  by_cases h : p ∈ s <;> simp [h]

private theorem fockForm_add {V : Type*} (q r : V → ℝ≥0∞)
    (v : (n : ℕ) → Fin n → ℕ → V) :
    fockForm (fun x => q x + r x) v = fockForm q v + fockForm r v := by
  simp only [fockForm, sectorForm, ENNReal.tsum_add, Finset.sum_add_distrib]

private theorem split_remainder_eq {s h t a b : ℝ≥0∞}
    (hsplit : s + h = t) (hsoft : s = a) (htotal : t = a + b) (ha : a ≠ ⊤) : h = b :=
  (ENNReal.add_right_inj ha).mp
    ((congrArg (fun x => x + h) hsoft.symm).trans (hsplit.trans htotal))

section Normal

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)
  (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

include normal F C in
theorem split_radiation_partition (s : Set PhotonMode) (hs : MeasurableSet s) (u : PhotonFock) :
    (∑' a, radiationForm ((photonFactorization BF).factor
      (MomentumSplit.split photonMeasure s hs) u a)) +
    (∑' a, radiationForm ((photonFactorization BF).factor
      (MomentumSplit.split photonMeasure sᶜ hs.compl) u a)) = radiationForm u := by
  have hsoft := familyObservable_pullback normal F BF C
    (MomentumSplit.split photonMeasure s hs) radiationFamily u
  have hhard := familyObservable_pullback normal F BF C
    (MomentumSplit.split photonMeasure sᶜ hs.compl) radiationFamily u
  simp only [radiationObservable_rankOne, MomentumSplit.retained_split] at hsoft hhard
  rw [hsoft, hhard, ← fockForm_add]
  exact (congrArg (fun q => fockForm q (fockSlices u))
    (funext (radiationFamily_projection_partition s hs))).trans (fockSlices_radiationForm u)

include normal F C in
/-- Exact hard retained energy on the original full-radiation graph. -/
theorem hardSplit_radiation_sum (κ : ℝ) (q : RadiationGraphSpace) :
    (∑' a, radiationForm ((photonFactorization BF).factor
      (MomentumSplit.split photonMeasure (softMomentumSet κ)ᶜ
        (softMomentumSet_measurable κ).compl) (radiationGraphInclusion q) a)) =
          ENNReal.ofReal (‖hardRadiationRoot κ q‖ ^ 2) := by
  have hsplit := split_radiation_partition normal F BF C (softMomentumSet κ)
    (softMomentumSet_measurable κ) (radiationGraphInclusion q)
  have hsoft := (softSplit_radiation_sum normal F BF C κ
    (radiationGraphInclusion q)).trans (softRadiationRoot_energy κ q)
  have htotal := (radiationGraph_energy q).trans
    ((congrArg ENNReal.ofReal (radiationRoot_norm_partition κ q)).trans
      (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)))
  exact split_remainder_eq hsplit hsoft htotal ENNReal.ofReal_ne_top

end Normal
end GptLean.PhysicalFock
