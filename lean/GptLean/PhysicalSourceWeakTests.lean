import GptLean.PhysicalSourceH1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Product test functions prove the weak H1 property of actual Fubini sources. -/

noncomputable section

namespace GptLean.PhysicalSourceH1

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter GptLean.SymmetricLift GptLean.PhysicalSourceFubini
open scoped ENNReal Topology ContDiff

variable {I J H : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

def testProduct (φ : Position I → ℝ) (ψ : Position J → ℝ) (p : Position I × Position J) : ℝ :=
  φ p.1 * ψ p.2

omit [DecidableEq I] [DecidableEq J] in
theorem testProduct_compact {φ : Position I → ℝ} {ψ : Position J → ℝ}
    (hφ : HasCompactSupport φ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (testProduct φ ψ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hφ.prod hψ)
  intro p hp
  have hne : φ p.1 ≠ 0 ∧ ψ p.2 ≠ 0 := mul_ne_zero_iff.mp hp
  exact ⟨subset_tsupport φ hne.1, subset_tsupport ψ hne.2⟩

omit [DecidableEq I] [DecidableEq J] in
theorem testProduct_continuous {φ : Position I → ℝ} {ψ : Position J → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) : Continuous (testProduct φ ψ) :=
  (hφ.comp continuous_fst).mul (hψ.comp continuous_snd)

omit [DecidableEq I] [DecidableEq J] in
/-- Actual nested L2 test pairings are the joint product integral. -/
theorem curry_test_pairing
    (u : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (φ : Position I → ℝ) (ψ : Position J → ℝ)
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume)
    (hprod : MemLp (testProduct φ ψ) 2 (volume.prod volume)) :
    (∫ y, ψ y • (∫ x, φ x • curry u x : Lp H 2 volume) y) =
      ∫ p, testProduct φ ψ p • u p := by
  let T : Lp H 2 (volume : Measure (Position J)) →L[ℝ] H := l2TestIntegralCLM hψ
  have htest := integrable_l2_test hφ (curry u)
  have hint : Integrable (fun p => testProduct φ ψ p • u p) (volume.prod volume) :=
    integrable_l2_test hprod u
  have hrep : ∀ᵐ x ∂volume, (curry u x : Position J → H) =ᵐ[volume]
      (fun y => u (x, y)) := by
    filter_upwards [curry_ae u, section_represents_ae u] with x hx hrep
    rw [hx]
    exact hrep
  calc
    _ = T (∫ x, φ x • curry u x) := rfl
    _ = ∫ x, T (φ x • curry u x) := (T.integral_comp_comm htest).symm
    _ = ∫ x, ∫ y, testProduct φ ψ (x, y) • u (x, y) := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [map_smul]
      change φ x • (∫ y, ψ y • curry u x y) = _
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      simp only [testProduct, smul_smul, hy]
    _ = _ := (integral_prod _ hint).symm

omit [DecidableEq J] [TopologicalSpace.SeparableSpace H] in
/-- Compact smooth scalar tests distinguish Hilbert-valued L2 vectors. -/
theorem L2_eq_of_smooth_tests
    (u v : Lp H 2 (volume : Measure (Position J)))
    (h : ∀ (ψ : Position J → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y, ψ y • u y) = ∫ y, ψ y • v y) : u = v := by
  apply Lp.ext
  exact ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num))
    ((Lp.memLp v).locallyIntegrable (by norm_num)) h

omit [DecidableEq J] in
/-- Product distributional identities suffice for the full Hilbert-valued
weak derivative identity of the actual source. -/
theorem weakH1_curry_of_product_tests
    (u : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (du : I → Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (hweak : ∀ i (φ : Position I → ℝ) (ψ : Position J → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ p, testProduct φ ψ p • du i p) =
        -(∫ p, testProduct (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) ψ p • u p)) :
    HasWeakH1Local (curry u) (fun i => curry (du i)) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun i K _ => (Lp.memLp _).restrict K, ?_⟩
  intro i φ hφ hφs
  apply L2_eq_of_smooth_tests
  intro ψ hψ hψs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  let hψ₂ : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψs
  change l2TestIntegralCLM hψ₂ (∫ x, φ x • curry (du i) x) =
    l2TestIntegralCLM hψ₂ (-(∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) • curry u x))
  rw [map_neg]
  simp only [l2TestIntegralCLM_apply]
  rw [curry_test_pairing (du i) φ ψ
    (hφ.continuous.memLp_of_hasCompactSupport hφs) hψ₂
    ((testProduct_continuous hφ.continuous hψ.continuous).memLp_of_hasCompactSupport
      (testProduct_compact hφs hψs))]
  rw [curry_test_pairing u _ ψ
    (hdφ.memLp_of_hasCompactSupport (hφs.fderiv_apply ℝ _)) hψ₂
    ((testProduct_continuous hdφ hψ.continuous).memLp_of_hasCompactSupport
      (testProduct_compact (hφs.fderiv_apply ℝ _) hψs))]
  exact hweak i φ ψ hφ hφs hψ hψs

end GptLean.PhysicalSourceH1
