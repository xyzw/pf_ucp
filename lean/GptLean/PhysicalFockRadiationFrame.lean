import GptLean.PhysicalFockRadiationFamily
import GptLean.PhysicalFockFormTruncation
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
The inverse-frequency representatives of the shell radiation kernels
form an actual Parseval frame. Its finite prefixes satisfy the Bessel
bound needed by the sharp localization estimate. Pairing with an actual
radiation square-root vector gives the exact radiation-kernel duality.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

namespace RadiationShells
variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (d : X → ℝ) (hd : Measurable d)

def indicator (n : ℕ) (x : X) : ℝ := if ⌊d x⌋₊ = n then 1 else 0

include hd in
theorem indicator_measurable (n : ℕ) : Measurable (indicator d n) :=
  Measurable.ite (measurableSet_eq_fun hd.nat_floor measurable_const) measurable_const measurable_const

omit [MeasurableSpace X] in
theorem indicator_bound (n : ℕ) (x : X) : |indicator d n x| ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

def projection (n : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  PhotonLocalization.realL2Multiplier (indicator d n) (indicator_measurable d hd n).aestronglyMeasurable
    1 (ae_of_all μ (indicator_bound d n))

theorem projection_ae (n : ℕ) (u : Lp H 2 μ) :
    projection μ d hd n u =ᵐ[μ] fun x => indicator d n x • u x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

omit [MeasurableSpace X] in
theorem indicator_square_sum (x : X) :
    (∑' n, ENNReal.ofReal (indicator d n x ^ 2)) = 1 := by
  have he : (∑' n, ENNReal.ofReal (indicator d n x ^ 2)) =
      ENNReal.ofReal (indicator d ⌊d x⌋₊ x ^ 2) := by
    apply tsum_eq_single ⌊d x⌋₊
    intro n hn
    simp only [indicator, ite_eq_right (Ne.symm hn), zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  exact he.trans (by simp [indicator])

theorem projection_norm_integral (n : ℕ) (u : Lp H 2 μ) :
    ENNReal.ofReal (‖projection μ d hd n u‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal (indicator d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
  have hn := Repair.toL2_norm_sq (Lp.memLp (projection μ d hd n u))
  simp only [Lp.toLp_coeFn] at hn
  rw [hn, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    (ae_of_all μ (fun x => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [projection_ae μ d hd n u] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]

theorem projection_norm_sum (u : Lp H 2 μ) :
    (∑' n, ENNReal.ofReal (‖projection μ d hd n u‖ ^ 2)) = ENNReal.ofReal (‖u‖ ^ 2) := by
  calc
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (indicator d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      tsum_congr (fun n => projection_norm_integral μ d hd n u)
    _ = ∫⁻ x, ∑' n, ENNReal.ofReal (indicator d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      (lintegral_tsum (fun n => ((indicator_measurable d hd n).pow_const 2).ennreal_ofReal.aemeasurable.mul
        ((Lp.aestronglyMeasurable u).norm.pow 2).aemeasurable.ennreal_ofReal)).symm
    _ = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      lintegral_congr (fun x => by rw [ENNReal.tsum_mul_right, indicator_square_sum d x, one_mul])
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
      (ae_of_all μ (fun x => sq_nonneg _))).symm.trans
      (congrArg ENNReal.ofReal (by
        simpa only [Lp.toLp_coeFn] using (Repair.toL2_norm_sq (Lp.memLp u)).symm))

end RadiationShells

def photonShellProjection (n : ℕ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  RadiationShells.projection photonMeasure photonDispersion photonDispersion_measurable n

def radiationFrame : OnePhotonFormFamily := fun n =>
  boundedSquareFamily (photonShellProjection n.unpair.1) n.unpair.2

theorem radiationFrame_value (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue radiationFrame u = ENNReal.ofReal (‖u‖ ^ 2) := by
  have he : onePhotonFamilyValue radiationFrame u =
      ∑' n, onePhotonFamilyValue (boundedSquareFamily (photonShellProjection n)) u :=
    (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ =>
      ENNReal.ofReal (‖⟪boundedSquareFamily (photonShellProjection p.1) p.2, u⟫_ℂ‖ ^ 2))).trans
      ENNReal.tsum_prod'
  exact he.trans ((tsum_congr (fun n => boundedSquareFamily_value (photonShellProjection n) u)).trans
    (RadiationShells.projection_norm_sum photonMeasure photonDispersion photonDispersion_measurable u))

theorem radiationFrame_bessel (k : ℕ) (u : Lp ℂ 2 photonMeasure) :
    ∑ i : Fin k, ‖⟪radiationFrame i, u⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖u‖)).mp
  rw [← finiteFamily_value_fin, ← radiationFrame_value]
  rw [finiteFamily_value]
  exact ENNReal.sum_le_tsum (Finset.range k)

theorem radiationShell_root (n : ℕ) (u z : Lp ℂ 2 photonMeasure)
    (hz : ∀ᵐ p ∂photonMeasure, z p = (Real.sqrt ‖p.1‖ : ℂ) * u p) :
    photonRadiationShell n u = photonShellProjection n z := by
  apply Lp.ext
  filter_upwards [RadiationShells.multiplier_ae photonMeasure photonDispersion
    photonDispersion_measurable n u,
    RadiationShells.projection_ae photonMeasure photonDispersion photonDispersion_measurable n z,
    hz] with p hu hp hz
  change (RadiationShells.multiplier photonMeasure photonDispersion photonDispersion_measurable n u) p =
    (RadiationShells.projection photonMeasure photonDispersion photonDispersion_measurable n z) p
  rw [hu, hp]
  by_cases h : ⌊photonDispersion p⌋₊ = n
  · simp only [RadiationShells.weight, RadiationShells.indicator, h, ite_true, one_smul]
    simpa only [photonDispersion, Complex.real_smul] using hz.symm
  · simp only [RadiationShells.weight, RadiationShells.indicator, ite_eq_right h, zero_smul]

theorem radiationFamily_root_pairing (u z : Lp ℂ 2 photonMeasure)
    (hz : ∀ᵐ p ∂photonMeasure, z p = (Real.sqrt ‖p.1‖ : ℂ) * u p) (i : ℕ) :
    ⟪radiationFamily i, u⟫_ℂ = ⟪radiationFrame i, z⟫_ℂ := by
  change ⟪(photonRadiationShell i.unpair.1).adjoint (numberFamily i.unpair.2), u⟫_ℂ =
    ⟪(photonShellProjection i.unpair.1).adjoint (numberFamily i.unpair.2), z⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    radiationShell_root i.unpair.1 u z hz]


theorem photonRadiationShell_selfadjoint (n : ℕ) : IsSelfAdjoint (photonRadiationShell n) := by
  unfold photonRadiationShell RadiationShells.multiplier
  exact PhotonLocalization.realL2Multiplier_selfadjoint _ _ _ _

theorem photonShellProjection_selfadjoint (n : ℕ) : IsSelfAdjoint (photonShellProjection n) := by
  unfold photonShellProjection RadiationShells.projection
  exact PhotonLocalization.realL2Multiplier_selfadjoint _ _ _ _

/-- The actual normalized frame represents the inverse-frequency kernel. -/
theorem radiationFamily_weighted (i : ℕ) :
    radiationFamily i =ᵐ[photonMeasure] fun p =>
      (Real.sqrt ‖p.1‖ : ℂ) * radiationFrame i p := by
  change ((photonRadiationShell i.unpair.1).adjoint (numberFamily i.unpair.2)) =ᵐ[photonMeasure]
    fun p => (Real.sqrt ‖p.1‖ : ℂ) *
      ((photonShellProjection i.unpair.1).adjoint (numberFamily i.unpair.2)) p
  rw [(photonRadiationShell_selfadjoint i.unpair.1).adjoint_eq,
    (photonShellProjection_selfadjoint i.unpair.1).adjoint_eq]
  filter_upwards [RadiationShells.multiplier_ae photonMeasure photonDispersion
    photonDispersion_measurable i.unpair.1 (numberFamily i.unpair.2),
    RadiationShells.projection_ae photonMeasure photonDispersion photonDispersion_measurable
      i.unpair.1 (numberFamily i.unpair.2)] with p hw hp
  change (RadiationShells.multiplier photonMeasure photonDispersion photonDispersion_measurable
      i.unpair.1 (numberFamily i.unpair.2)) p = _
  rw [hw]
  change _ = (Real.sqrt ‖p.1‖ : ℂ) *
    (RadiationShells.projection photonMeasure photonDispersion photonDispersion_measurable
      i.unpair.1 (numberFamily i.unpair.2)) p
  rw [hp]
  by_cases h : ⌊photonDispersion p⌋₊ = i.unpair.1
  · simp only [RadiationShells.weight, RadiationShells.indicator, h, ite_true, one_smul]
    rfl
  · simp only [RadiationShells.weight, RadiationShells.indicator, ite_eq_right h, zero_smul, mul_zero]

/-- Finite one-photon radiation constructs its actual square-root vector. -/
theorem exists_photonRadiationRoot (u : Lp ℂ 2 photonMeasure)
    (hfinite : onePhotonFamilyValue radiationFamily u < ⊤) :
    ∃ z : Lp ℂ 2 photonMeasure,
      onePhotonFamilyValue radiationFamily u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      (∀ᵐ p ∂photonMeasure, z p = (Real.sqrt ‖p.1‖ : ℂ) * u p) := by
  let f : PhotonMode → ℂ := fun p => (Real.sqrt ‖p.1‖ : ℂ) * u p
  have hc : Measurable (fun p : PhotonMode => (Real.sqrt ‖p.1‖ : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable f photonMeasure := hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)
  have he (p : PhotonMode) : ‖f p‖ ^ 2 = ‖p.1‖ * ‖u p‖ ^ 2 := by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hf : MemLp f 2 photonMeasure := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    refine ⟨hm.norm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sq_nonneg (‖f p‖))).mpr
    simpa only [he, ENNReal.ofReal_mul (norm_nonneg _), radiationFamily_value] using hfinite
  let z := hf.toLp f
  have hz : ∀ᵐ p ∂photonMeasure, z p = (Real.sqrt ‖p.1‖ : ℂ) * u p := hf.coeFn_toLp
  have hp : onePhotonFamilyValue radiationFamily u = onePhotonFamilyValue radiationFrame z :=
    tsum_congr (fun i => congrArg (fun c : ℂ => ENNReal.ofReal (‖c‖ ^ 2))
      (radiationFamily_root_pairing u z hz i))
  exact ⟨z, hp.trans (radiationFrame_value z), hz⟩

theorem radiationFamily_root_duality (u : Lp ℂ 2 photonMeasure)
    (hfinite : onePhotonFamilyValue radiationFamily u < ⊤) :
    ∃ z : Lp ℂ 2 photonMeasure,
      onePhotonFamilyValue radiationFamily u = ENNReal.ofReal (‖z‖ ^ 2) ∧
      ∀ i, ⟪radiationFamily i, u⟫_ℂ = ⟪radiationFrame i, z⟫_ℂ := by
  obtain ⟨z, he, hz⟩ := exists_photonRadiationRoot u hfinite
  exact ⟨z, he, radiationFamily_root_pairing u z hz⟩

end GptLean.PhysicalFock
