import GptLean.RemovalSourceTests
import GptLean.Repair.ParameterSections

/-!
The conditional source marginal is the Bochner integral of the actual
rank-one L² sections. Its trace-norm bound and tested evaluation follow
from universal rank-one trace facts, so source marginal sums require no
extra facts about already constructed localized marginals.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure Filter Repair

variable {Q X K T F : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def productSourceSection (φ : Q × X → K) (q : Q) : Lp K 2 ν :=
  toL2Section (fun q x => φ (q, x)) q

def productSourceMarginal (R : Gaussian.RankOneData (Lp K 2 ν) T) (M : T →L[ℝ] F)
    (φ : Q × X → K) : F := ∫ q, M (R.rankOne (productSourceSection (ν := ν) φ q)) ∂μ

theorem productSourceSection_norm
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν)) :
    ∀ᵐ q ∂μ, ‖productSourceSection (ν := ν) φ q‖ ^ 2 = ∫ x, ‖φ (q, x)‖ ^ 2 ∂ν := by
  have hi := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  filter_upwards [hi.prod_right_ae] with q hq
  have hm : MemLp (fun x => φ (q, x)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm
      ((hφ.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr hq
  rw [productSourceSection, toL2Section_eq hm]
  exact toL2_norm_sq hm

theorem productSourceSection_mass_integrable
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν)) :
    Integrable (fun q => ‖productSourceSection (ν := ν) φ q‖ ^ 2) μ := by
  have hi := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have he : (fun q => ‖productSourceSection (ν := ν) φ q‖ ^ 2) =ᵐ[μ]
      (fun q => ∫ x, ‖φ (q, x)‖ ^ 2 ∂ν) := productSourceSection_norm hφ hmem
  exact hi.integral_prod_left.congr he.symm

theorem productSource_rankOne_integrable
    (R : Gaussian.RankOneData (Lp K 2 ν) T)
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν)) :
    Integrable (fun q => R.rankOne (productSourceSection (ν := ν) φ q)) μ := by
  have hm : StronglyMeasurable (productSourceSection (ν := ν) φ) :=
    stronglyMeasurable_toL2Section hφ
  apply (productSourceSection_mass_integrable hφ hmem).mono'
    (R.continuous_rankOne.comp_aestronglyMeasurable hm.aestronglyMeasurable)
  exact Eventually.of_forall fun q => (R.norm_rankOne _).le

theorem productSourceMarginal_norm_le
    (R : Gaussian.RankOneData (Lp K 2 ν) T) (M : T →L[ℝ] F)
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν)) :
    ‖productSourceMarginal (μ := μ) R M φ‖ ≤ ‖M‖ * ∫ qx, ‖φ qx‖ ^ 2 ∂μ.prod ν := by
  have hi := productSource_rankOne_integrable R hφ hmem
  have hM := M.integrable_comp hi
  have hm := productSourceSection_mass_integrable hφ hmem
  have hquad := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  calc
    _ ≤ ∫ q, ‖M (R.rankOne (productSourceSection (ν := ν) φ q))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, ‖M‖ * ‖productSourceSection (ν := ν) φ q‖ ^ 2 ∂μ := by
      apply integral_mono_ae hM.norm (hm.const_mul ‖M‖)
      exact Eventually.of_forall fun q => by simpa only [R.norm_rankOne] using M.le_opNorm (R.rankOne _)
    _ = ‖M‖ * ∫ qx, ‖φ qx‖ ^ 2 ∂μ.prod ν := by
      rw [integral_const_mul, integral_prod _ hquad]
      congr 1
      exact integral_congr_ae (productSourceSection_norm hφ hmem)

theorem productSourceMarginal_comp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (R : Gaussian.RankOneData (Lp K 2 ν) T) (M : T →L[ℝ] F) (P : F →L[ℝ] G)
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν)) :
    productSourceMarginal (μ := μ) R (P.comp M) φ =
      P (productSourceMarginal (μ := μ) R M φ) := by
  exact P.integral_comp_comm (M.integrable_comp (productSource_rankOne_integrable R hφ hmem))

/-- Every source test follows from a formula for all reference vectors.
The exceptional zero sections disappear on the finite-mass set. -/
theorem productSourceMarginal_test
    (R : Gaussian.RankOneData (Lp K 2 ν) T) (M : T →L[ℝ] F) (test : F →L[ℝ] ℝ)
    (W : Q × X → K →L[ℂ] K)
    (hrank : ∀ q (v : Lp K 2 ν), test (M (R.rankOne v)) =
      (∫ x, inner ℂ (v x) (W (q, x) (v x)) ∂ν).re)
    {φ : Q × X → K} (hφ : StronglyMeasurable φ) (hmem : MemLp φ 2 (μ.prod ν))
    (htest : Integrable (fun qx => inner ℂ (φ qx) (W qx (φ qx))) (μ.prod ν)) :
    test (productSourceMarginal (μ := μ) R M φ) =
      (∫ q, ∫ x, inner ℂ (φ (q, x)) (W (q, x) (φ (q, x))) ∂ν ∂μ).re := by
  have hi := M.integrable_comp (productSource_rankOne_integrable R hφ hmem)
  change test (∫ q, M (R.rankOne (productSourceSection (ν := ν) φ q)) ∂μ) = _
  have hre : (∫ q, ∫ x, inner ℂ (φ (q, x)) (W (q, x) (φ (q, x))) ∂ν ∂μ).re =
      ∫ q, (∫ x, inner ℂ (φ (q, x)) (W (q, x) (φ (q, x))) ∂ν).re ∂μ :=
    (integral_re htest.integral_prod_left).symm
  rw [← test.integral_comp_comm hi, hre]
  have hquad := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  apply integral_congr_ae
  filter_upwards [hquad.prod_right_ae] with q hq
  have hm : MemLp (fun x => φ (q, x)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm
      ((hφ.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr hq
  rw [hrank]
  congr 1
  apply integral_congr_ae
  have hrep : (fun x => productSourceSection (ν := ν) φ q x) =ᵐ[ν] (fun x => φ (q, x)) := by
    rw [productSourceSection, toL2Section_eq hm]
    exact hm.coeFn_toLp
  filter_upwards [hrep] with x hx
  rw [hx]

end GptLean.RemovalSource
