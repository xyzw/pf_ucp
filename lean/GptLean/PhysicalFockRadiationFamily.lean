import GptLean.PhysicalFockFormFamilies
import GptLean.PhotonLocalizationLocalForms
import Mathlib.MeasureTheory.Function.Floor

/-!
The one-photon radiation form as an actual countable kernel family.
Disjoint bounded momentum shells resolve the square-root dispersion.
Each shell uses the actual L2 multiplier and the proved one-photon frame.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

namespace RadiationShells
variable {X H : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (d : X → ℝ) (hd : Measurable d) (hpos : ∀ x, 0 ≤ d x)

def weight (n : ℕ) (x : X) : ℝ := if ⌊d x⌋₊ = n then Real.sqrt (d x) else 0

include hd in
theorem weight_measurable (n : ℕ) : Measurable (weight d n) :=
  Measurable.ite (measurableSet_eq_fun hd.nat_floor measurable_const) hd.sqrt measurable_const

omit [MeasurableSpace X] in
theorem weight_bound (n : ℕ) (x : X) : |weight d n x| ≤ Real.sqrt (n + 1 : ℝ) := by
  unfold weight
  split_ifs with h
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have ht := Nat.lt_floor_add_one (d x)
    rw [h] at ht
    exact ht.le
  · simp only [abs_zero]
    exact Real.sqrt_nonneg _

def multiplier (n : ℕ) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  PhotonLocalization.realL2Multiplier (weight d n) (weight_measurable d hd n).aestronglyMeasurable
    (Real.sqrt (n + 1 : ℝ)) (ae_of_all μ (weight_bound d n))

theorem multiplier_ae (n : ℕ) (u : Lp H 2 μ) :
    multiplier μ d hd n u =ᵐ[μ] fun x => weight d n x • u x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ u

include hpos in
omit [MeasurableSpace X] in
theorem weight_square_sum (x : X) :
    (∑' n, ENNReal.ofReal (weight d n x ^ 2)) = ENNReal.ofReal (d x) := by
  have he : (∑' n, ENNReal.ofReal (weight d n x ^ 2)) =
      ENNReal.ofReal (weight d ⌊d x⌋₊ x ^ 2) := by
    apply tsum_eq_single ⌊d x⌋₊
    intro n hn
    simp only [weight, ite_eq_right (Ne.symm hn), zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  exact he.trans (by rw [weight, ite_eq_left rfl, Real.sq_sqrt (hpos x)])

theorem multiplier_norm_integral (n : ℕ) (u : Lp H 2 μ) :
    ENNReal.ofReal (‖multiplier μ d hd n u‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal (weight d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
  have hn := Repair.toL2_norm_sq (Lp.memLp (multiplier μ d hd n u))
  simp only [Lp.toLp_coeFn] at hn
  rw [hn, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    (ae_of_all μ (fun x => sq_nonneg _))]
  apply lintegral_congr_ae
  filter_upwards [multiplier_ae μ d hd n u] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]

include hpos in
theorem multiplier_norm_sum (u : Lp H 2 μ) :
    (∑' n, ENNReal.ofReal (‖multiplier μ d hd n u‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (d x) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ := by
  calc
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (weight d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      tsum_congr (fun n => multiplier_norm_integral μ d hd n u)
    _ = ∫⁻ x, ∑' n, ENNReal.ofReal (weight d n x ^ 2) * ENNReal.ofReal (‖u x‖ ^ 2) ∂μ :=
      (lintegral_tsum (fun n => ((weight_measurable d hd n).pow_const 2).ennreal_ofReal.aemeasurable.mul
        ((Lp.aestronglyMeasurable u).norm.pow 2).aemeasurable.ennreal_ofReal)).symm
    _ = _ := lintegral_congr (fun x => by rw [ENNReal.tsum_mul_right, weight_square_sum d hpos x])

end RadiationShells

def photonDispersion (p : PhotonMode) : ℝ := ‖p.1‖

theorem photonDispersion_measurable : Measurable photonDispersion := by
  unfold photonDispersion
  fun_prop

def photonRadiationShell (n : ℕ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  RadiationShells.multiplier photonMeasure photonDispersion photonDispersion_measurable n

def radiationFamily : OnePhotonFormFamily := fun n =>
  boundedSquareFamily (photonRadiationShell n.unpair.1) n.unpair.2

theorem radiationFamily_value (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue radiationFamily u =
      ∫⁻ p, ENNReal.ofReal (‖p.1‖) * ENNReal.ofReal (‖u p‖ ^ 2) ∂photonMeasure := by
  have he : onePhotonFamilyValue radiationFamily u =
      ∑' n, onePhotonFamilyValue (boundedSquareFamily (photonRadiationShell n)) u :=
    (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ =>
      ENNReal.ofReal (‖⟪boundedSquareFamily (photonRadiationShell p.1) p.2, u⟫_ℂ‖ ^ 2))).trans
      ENNReal.tsum_prod'
  exact he.trans ((tsum_congr (fun n => boundedSquareFamily_value (photonRadiationShell n) u)).trans
    (RadiationShells.multiplier_norm_sum photonMeasure photonDispersion photonDispersion_measurable
      (fun p => norm_nonneg p.1) u))

end GptLean.PhysicalFock
