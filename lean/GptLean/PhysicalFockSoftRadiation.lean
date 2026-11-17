import GptLean.PhysicalFockRadiationField
import GptLean.PhysicalPhotonHardSoft

/-!
The actual soft radiation square root on the full radiation domain.
A bounded symmetric ratio of soft and total dispersion multiplies the
already constructed total square root. Its pointwise formula and exact
moment identity are proved on the same Fock vectors.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationChannel
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

def softFrequency (κ : ℝ) : PhotonMode → ℝ :=
  (softMomentumSet κ).indicator NormalPhoton.frequency

theorem softFrequency_measurable (κ : ℝ) : Measurable (softFrequency κ) :=
  measurable_fst.norm.indicator (softMomentumSet_measurable κ)

theorem softFrequency_nonneg (κ : ℝ) (p : PhotonMode) : 0 ≤ softFrequency κ p := by
  classical
  by_cases hp : p ∈ softMomentumSet κ <;> simp [softFrequency, hp, NormalPhoton.frequency]

theorem softFrequency_le (κ : ℝ) (p : PhotonMode) : softFrequency κ p ≤ ‖p.1‖ := by
  classical
  by_cases hp : p ∈ softMomentumSet κ <;> simp [softFrequency, hp, NormalPhoton.frequency]

theorem ofReal_softFrequency (κ : ℝ) (p : PhotonMode) :
    ENNReal.ofReal (softFrequency κ p) = NormalPhoton.softWeight κ p := by
  classical
  by_cases hp : NormalPhoton.frequency p < κ <;>
    simp [softFrequency, NormalPhoton.softWeight, softMomentumSet, hp]

def sectorSoftDispersion (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  ∑ i, softFrequency κ (k i)

theorem sectorSoftDispersion_nonneg (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    0 ≤ sectorSoftDispersion κ n k :=
  Finset.sum_nonneg fun i _ => softFrequency_nonneg κ (k i)

theorem sectorSoftDispersion_le (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    sectorSoftDispersion κ n k ≤ sectorDispersion n k :=
  Finset.sum_le_sum fun i _ => softFrequency_le κ (k i)

theorem sectorSoftDispersion_measurable (κ : ℝ) (n : ℕ) :
    Measurable (sectorSoftDispersion κ n) :=
  Finset.measurable_sum _ fun i _ => (softFrequency_measurable κ).comp (measurable_pi_apply i)

theorem sectorSoftDispersion_permutation (κ : ℝ) (n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    sectorSoftDispersion κ n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      sectorSoftDispersion κ n k := by
  unfold sectorSoftDispersion
  rw [← Equiv.sum_comp π (fun i => softFrequency κ
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) i))]
  simp only [MeasurableEquiv.piCongrLeft_apply_apply]

theorem ofReal_sectorSoftDispersion (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    ENNReal.ofReal (sectorSoftDispersion κ n k) =
      ∑ i, NormalPhoton.softWeight κ (k i) := by
  rw [sectorSoftDispersion, ENNReal.ofReal_sum_of_nonneg (fun i _ => softFrequency_nonneg κ (k i))]
  exact Finset.sum_congr rfl fun i _ => ofReal_softFrequency κ (k i)

def softRootRatio (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  Real.sqrt (sectorSoftDispersion κ n k) / Real.sqrt (sectorDispersion n k)

theorem softRootRatio_bound (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    |softRootRatio κ n k| ≤ 1 := by
  unfold softRootRatio
  rw [abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  by_cases hz : Real.sqrt (sectorDispersion n k) = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz))).mpr
      (Real.sqrt_le_sqrt (sectorSoftDispersion_le κ n k))

theorem softRootRatio_mul_root (κ : ℝ) (n : ℕ) (k : Fin n → PhotonMode) :
    softRootRatio κ n k * Real.sqrt (sectorDispersion n k) =
      Real.sqrt (sectorSoftDispersion κ n k) := by
  by_cases hz : Real.sqrt (sectorDispersion n k) = 0
  · have hs : Real.sqrt (sectorSoftDispersion κ n k) = 0 :=
      le_antisymm ((Real.sqrt_le_sqrt (sectorSoftDispersion_le κ n k)).trans hz.le)
        (Real.sqrt_nonneg _)
    simp [softRootRatio, hz, hs]
  · exact div_mul_cancel₀ _ hz

def softRootRatioWeight (κ : ℝ) : BoundedSymmetricWeight photonMeasure 1 where
  value := softRootRatio κ
  measurable n := ((sectorSoftDispersion_measurable κ n).sqrt.div
    (sectorDispersion_measurable n).sqrt).aestronglyMeasurable
  bound := softRootRatio_bound κ
  symmetric n π k := by
    simp only [softRootRatio, sectorSoftDispersion_permutation, sectorDispersion_permutation]

/-- The soft root is an actual bounded ratio applied to the total root. -/
def softRadiationRoot (κ : ℝ) : RadiationGraphSpace →L[ℂ] PhotonFock :=
  ((softRootRatioWeight κ).operator zero_le_one).comp radiationGraphDerivative

theorem softRadiationRoot_ae (κ : ℝ) (q : RadiationGraphSpace) (n : ℕ) :
    (softRadiationRoot κ q n).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => (Real.sqrt (sectorSoftDispersion κ n k) : ℂ) *
        (radiationGraphInclusion q n).val k := by
  filter_upwards [(softRootRatioWeight κ).sector_ae n (radiationGraphDerivative q n),
    (radiationRoot_graph_iff (radiationGraphInclusion q) (radiationGraphDerivative q)).mp
      (radiationGraph_pair q) n] with k hs hr
  have hs' : (softRadiationRoot κ q n).val k =
      softRootRatio κ n k • (radiationGraphDerivative q n).val k := hs
  have hr' : (radiationGraphDerivative q n).val k =
      (Real.sqrt (sectorDispersion n k) : ℂ) * (radiationGraphInclusion q n).val k := hr
  have hscalar (z : ℂ) : softRootRatio κ n k •
      ((Real.sqrt (sectorDispersion n k) : ℂ) * z) =
        (Real.sqrt (sectorSoftDispersion κ n k) : ℂ) * z := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, softRootRatio_mul_root]
  exact hs'.trans ((congrArg (fun z : ℂ => softRootRatio κ n k • z) hr').trans
    (hscalar _))

theorem sectorSoftMoment_eq_root_norm (κ : ℝ) (n : ℕ)
    (u v : Sector photonMeasure n)
    (h : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      v.val k = (Real.sqrt (sectorSoftDispersion κ n k) : ℂ) * u.val k) :
    sectorPhotonMoment (NormalPhoton.softWeight κ) n u = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← sector_mass_lintegral n v]
  unfold sectorPhotonMoment
  apply lintegral_congr_ae
  filter_upwards [h] with k hk
  rw [hk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sectorSoftDispersion_nonneg κ n k),
    ENNReal.ofReal_mul (sectorSoftDispersion_nonneg κ n k), ofReal_sectorSoftDispersion]

/-- Exact actual soft energy, with no replacement by total radiation. -/
theorem softRadiationRoot_energy (κ : ℝ) (q : RadiationGraphSpace) :
    photonMoment (NormalPhoton.softWeight κ) (radiationGraphInclusion q) =
      ENNReal.ofReal (‖softRadiationRoot κ q‖ ^ 2) := by
  unfold photonMoment
  simp_rw [sectorSoftMoment_eq_root_norm κ _ _ _ (softRadiationRoot_ae κ q _)]
  simpa only [weightedForm, one_mul] using
    massForm_eq (Sector photonMeasure) (softRadiationRoot κ q)

theorem softRadiationRoot_norm_sq (κ : ℝ) (q : RadiationGraphSpace) :
    ‖softRadiationRoot κ q‖ ^ 2 =
      (photonMoment (NormalPhoton.softWeight κ) (radiationGraphInclusion q)).toReal := by
  rw [softRadiationRoot_energy, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem softRadiation_finite (κ : ℝ) (q : RadiationGraphSpace) :
    photonMoment (NormalPhoton.softWeight κ) (radiationGraphInclusion q) < ⊤ := by
  rw [softRadiationRoot_energy]
  exact ENNReal.ofReal_lt_top

/-- The ordinary operator is extended by zero off its specified full-radiation domain. -/
def softRadiation (κ : ℝ) (u : PhotonFock) : PhotonFock := by
  classical
  exact if h : u ∈ radiationRoot.domain then
    softRadiationRoot κ ⟨(u, radiationRoot ⟨u, h⟩), radiationRoot.mem_graph ⟨u, h⟩⟩ else 0

theorem softRadiation_of_graph (κ : ℝ) (q : RadiationGraphSpace) :
    softRadiation κ (radiationGraphInclusion q) = softRadiationRoot κ q := by
  obtain ⟨u, hu, hv⟩ := radiationRoot.mem_graph_iff.mp q.property
  have hd : radiationGraphInclusion q ∈ radiationRoot.domain := by
    change q.val.1 ∈ radiationRoot.domain
    exact hu ▸ u.property
  rw [softRadiation, dite_eq_left hd]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change radiationRoot ⟨radiationGraphInclusion q, hd⟩ = radiationGraphDerivative q
    have harg : (⟨radiationGraphInclusion q, hd⟩ : radiationRoot.domain) = u :=
      Subtype.ext hu.symm
    have hv' : radiationRoot u = radiationGraphDerivative q := hv
    exact (congrArg radiationRoot harg).trans hv'

section Normal
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : NormalTraceData R) (F : NormalFunctionalData R)

theorem softRadiationRoot_normal_energy (κ : ℝ) (q : RadiationGraphSpace) :
    (NormalPhoton.softEnergyForm normal F κ).expectation
      (R.rankOne (radiationGraphInclusion q)) = ENNReal.ofReal (‖softRadiationRoot κ q‖ ^ 2) := by
  rw [NormalPhoton.softEnergyForm, secondQuantizedPositiveForm_rankOne]
  exact softRadiationRoot_energy κ q

end Normal
end GptLean.PhysicalFock
