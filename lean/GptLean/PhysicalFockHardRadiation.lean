import GptLean.PhysicalFockSoftRadiation

/-!
The hard radiation square root on the full radiation graph. Its multiplier
is the square root of the sum of the hard photon frequencies. The soft and
hard root norms partition the total radiation norm on the same vector.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

def sectorHardDispersion (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  sectorDispersion n k - sectorSoftDispersion κ n k

theorem sectorHardDispersion_nonneg (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    0 ≤ sectorHardDispersion κ n k := sub_nonneg.mpr (sectorSoftDispersion_le κ n k)

theorem sectorHardDispersion_le (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    sectorHardDispersion κ n k ≤ sectorDispersion n k :=
  sub_le_self _ (sectorSoftDispersion_nonneg κ n k)

theorem sectorHardDispersion_eq (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    sectorHardDispersion κ n k =
      ∑ i, ((softMomentumSet κ)ᶜ).indicator NormalPhoton.frequency (k i) := by
  classical
  unfold sectorHardDispersion sectorDispersion sectorSoftDispersion
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : k i ∈ softMomentumSet κ <;>
    simp [softFrequency, NormalPhoton.frequency, hi]

theorem sectorHardDispersion_measurable (κ : ℝ) (n : ℕ) :
    Measurable (sectorHardDispersion κ n) :=
  (sectorDispersion_measurable n).sub (sectorSoftDispersion_measurable κ n)

theorem sectorHardDispersion_permutation (κ : ℝ) (n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    sectorHardDispersion κ n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      sectorHardDispersion κ n k := by
  simp only [sectorHardDispersion, sectorDispersion_permutation, sectorSoftDispersion_permutation]

def hardRootRatio (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  Real.sqrt (sectorHardDispersion κ n k) / Real.sqrt (sectorDispersion n k)

theorem hardRootRatio_bound (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    |hardRootRatio κ n k| ≤ 1 := by
  unfold hardRootRatio
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  by_cases hz : Real.sqrt (sectorDispersion n k) = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz))).mpr
      (Real.sqrt_le_sqrt (sectorHardDispersion_le κ n k))

theorem hardRootRatio_mul_root (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    hardRootRatio κ n k * Real.sqrt (sectorDispersion n k) =
      Real.sqrt (sectorHardDispersion κ n k) := by
  by_cases hz : Real.sqrt (sectorDispersion n k) = 0
  · have hs : Real.sqrt (sectorHardDispersion κ n k) = 0 :=
      le_antisymm ((Real.sqrt_le_sqrt (sectorHardDispersion_le κ n k)).trans hz.le)
        (Real.sqrt_nonneg _)
    simp [hardRootRatio, hz, hs]
  · exact div_mul_cancel₀ _ hz

def hardRootRatioWeight (κ : ℝ) : BoundedSymmetricWeight photonMeasure 1 where
  value := hardRootRatio κ
  measurable n := ((sectorHardDispersion_measurable κ n).sqrt.div
    (sectorDispersion_measurable n).sqrt).aestronglyMeasurable
  bound := hardRootRatio_bound κ
  symmetric n π k := by
    simp only [hardRootRatio, sectorHardDispersion_permutation, sectorDispersion_permutation]

/-- Actual ambient hard root, distinct from the root restricted to the generated hard space. -/
def hardRadiationRoot (κ : ℝ) : RadiationGraphSpace →L[ℂ] PhotonFock :=
  ((hardRootRatioWeight κ).operator zero_le_one).comp radiationGraphDerivative

theorem hardRadiationRoot_ae (κ : ℝ) (q : RadiationGraphSpace) (n : ℕ) :
    (hardRadiationRoot κ q n).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => (Real.sqrt (sectorHardDispersion κ n k) : ℂ) *
        (radiationGraphInclusion q n).val k := by
  filter_upwards [(hardRootRatioWeight κ).sector_ae n (radiationGraphDerivative q n),
    (radiationRoot_graph_iff (radiationGraphInclusion q) (radiationGraphDerivative q)).mp
      (radiationGraph_pair q) n] with k hs hr
  have hs' : (hardRadiationRoot κ q n).val k =
      hardRootRatio κ n k • (radiationGraphDerivative q n).val k := hs
  have hr' : (radiationGraphDerivative q n).val k =
      (Real.sqrt (sectorDispersion n k) : ℂ) * (radiationGraphInclusion q n).val k := hr
  have hscalar (z : ℂ) : hardRootRatio κ n k •
      ((Real.sqrt (sectorDispersion n k) : ℂ) * z) =
        (Real.sqrt (sectorHardDispersion κ n k) : ℂ) * z := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hardRootRatio_mul_root]
  exact hs'.trans ((congrArg (fun z : ℂ => hardRootRatio κ n k • z) hr').trans
    (hscalar _))

private theorem root_norm_sq {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    ‖(Real.sqrt a : ℂ) * z‖ ^ 2 = a * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ha]

private theorem root_partition (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) (z : ℂ) :
    ENNReal.ofReal (‖(Real.sqrt (sectorDispersion n k) : ℂ) * z‖ ^ 2) =
      ENNReal.ofReal (‖(Real.sqrt (sectorSoftDispersion κ n k) : ℂ) * z‖ ^ 2) +
        ENNReal.ofReal (‖(Real.sqrt (sectorHardDispersion κ n k) : ℂ) * z‖ ^ 2) := by
  rw [root_norm_sq (sectorDispersion_nonneg n k),
    root_norm_sq (sectorSoftDispersion_nonneg κ n k),
    root_norm_sq (sectorHardDispersion_nonneg κ n k),
    ← ENNReal.ofReal_add
      (mul_nonneg (sectorSoftDispersion_nonneg κ n k) (sq_nonneg _))
      (mul_nonneg (sectorHardDispersion_nonneg κ n k) (sq_nonneg _))]
  congr 1
  unfold sectorHardDispersion
  ring

private theorem sector_norm_partition (n : ℕ) (u v w : Sector photonMeasure n)
    (h : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      ENNReal.ofReal (‖u.val k‖ ^ 2) =
        ENNReal.ofReal (‖v.val k‖ ^ 2) + ENNReal.ofReal (‖w.val k‖ ^ 2)) :
    ENNReal.ofReal (‖u‖ ^ 2) =
      ENNReal.ofReal (‖v‖ ^ 2) + ENNReal.ofReal (‖w‖ ^ 2) := by
  have hm : AEMeasurable (fun k => ENNReal.ofReal (‖v.val k‖ ^ 2))
      (SectorMeasure photonMeasure n) :=
    ((Lp.aestronglyMeasurable v.val).norm.pow 2).aemeasurable.ennreal_ofReal
  exact (sector_mass_lintegral n u).symm.trans
    ((lintegral_congr_ae h).trans ((lintegral_add_left' hm _).trans
      (congrArg₂ (· + ·) (sector_mass_lintegral n v) (sector_mass_lintegral n w))))

private theorem hilbert_sum_norm_partition (K : ℕ → Type*)
    [∀ n, NormedAddCommGroup (K n)] (u v w : Space K)
    (h : ∀ n, ENNReal.ofReal (‖u n‖ ^ 2) =
      ENNReal.ofReal (‖v n‖ ^ 2) + ENNReal.ofReal (‖w n‖ ^ 2)) :
    ‖u‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have he : ENNReal.ofReal (‖u‖ ^ 2) =
      ENNReal.ofReal (‖v‖ ^ 2) + ENNReal.ofReal (‖w‖ ^ 2) := by
    rw [← massForm_eq K u, ← massForm_eq K v, ← massForm_eq K w]
    simp only [weightedForm, one_mul]
    rw [← ENNReal.tsum_add]
    exact tsum_congr h
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))).mp he

theorem radiationRoot_sector_norm_partition (κ : ℝ) (q : RadiationGraphSpace) (n : ℕ) :
    ENNReal.ofReal (‖radiationGraphDerivative q n‖ ^ 2) =
      ENNReal.ofReal (‖softRadiationRoot κ q n‖ ^ 2) +
        ENNReal.ofReal (‖hardRadiationRoot κ q n‖ ^ 2) := by
  refine sector_norm_partition n (radiationGraphDerivative q n)
    (softRadiationRoot κ q n) (hardRadiationRoot κ q n) ?_
  filter_upwards [(radiationRoot_graph_iff (radiationGraphInclusion q)
    (radiationGraphDerivative q)).mp (radiationGraph_pair q) n,
    softRadiationRoot_ae κ q n, hardRadiationRoot_ae κ q n] with k hr hs hh
  have hr' : (radiationGraphDerivative q n).val k =
      (Real.sqrt (sectorDispersion n k) : ℂ) * (radiationGraphInclusion q n).val k := hr
  exact (congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hr').trans
    ((root_partition κ n k _).trans (congrArg₂ (· + ·)
      (congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hs).symm
      (congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) hh).symm))

/-- Exact total energy split for the actual soft and hard square-root operators. -/
theorem radiationRoot_norm_partition (κ : ℝ) (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative q‖ ^ 2 =
      ‖softRadiationRoot κ q‖ ^ 2 + ‖hardRadiationRoot κ q‖ ^ 2 :=
  hilbert_sum_norm_partition (Sector photonMeasure) (radiationGraphDerivative q)
    (softRadiationRoot κ q) (hardRadiationRoot κ q) (radiationRoot_sector_norm_partition κ q)

end GptLean.PhysicalFock
