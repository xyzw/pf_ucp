import GptLean.PhysicalEnsembleTests
import GptLean.PhysicalWeightedDensity

/-!
Unbounded current tests obtained from weighted square integrability.
The proof uses Fubini and a dominated ensemble series. No truncation of
the current or bound on the testing function is assumed.
-/

noncomputable section
namespace GptLean.PhysicalWeightedCurrentCore

open MeasureTheory Filter PhysicalEnsembleSource PhysicalSourceCoordinates
  PhysicalSourceFubini PhysicalSourceH1 PhysicalSourceMarginal
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weighted Cauchy--Schwarz in the form used for the dominating series. -/
theorem weighted_re_inner_bound (a : ℝ) (u v : H) :
    ‖a * (inner ℂ u v).re‖ ≤ a ^ 2 * ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hinner := (Complex.abs_re_le_norm (inner ℂ u v)).trans (norm_inner_le_norm u v)
  have hmul := mul_le_mul_of_nonneg_left hinner (abs_nonneg a)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a| * ‖u‖ - ‖v‖), sq_abs a]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- A square-integrable density weight makes the associated current test
absolutely integrable. -/
theorem weighted_re_inner_integrable (u v : Lp H 2 μ)
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hi : Integrable (fun x => a x ^ 2 * ‖u x‖ ^ 2) μ) :
    Integrable (fun x => a x * (inner ℂ (u x) (v x)).re) μ := by
  have hiv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  apply (hi.add hiv).mono' (ha.mul (((Lp.aestronglyMeasurable u).inner (𝕜 := ℂ)
    (Lp.aestronglyMeasurable v)).re))
  exact ae_of_all _ fun x => weighted_re_inner_bound (a x) (u x) (v x)

variable [TopologicalSpace.SeparableSpace H]

/-- The unbounded weighted ensemble current has the exact integrated
source series whenever the density-weighted square is integrable. -/
theorem ensemble_tested_re_inner_hasSum (v w : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) (hw : Summable (fun n => ‖w n‖ ^ 2))
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    (hi : Integrable (fun x => a x ^ 2 * ‖ensemble v hv x‖ ^ 2) μ) :
    HasSum (fun n => ∫ x, a x * (inner ℂ (v n x) (w n x)).re ∂μ)
      (∫ x, a x * (inner ℂ (ensemble v hv x) (ensemble w hw x)).re ∂μ) := by
  have hiw := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble w hw))).mp (Lp.memLp (ensemble w hw))
  have hsv := ensemble_squares_summable_ae v hv
  have hsw := ensemble_squares_summable_ae w hw
  apply hasSum_integral_of_dominated_convergence
    (fun n x => a x ^ 2 * ‖v n x‖ ^ 2 + ‖w n x‖ ^ 2)
  · intro n
    exact ha.mul (((Lp.aestronglyMeasurable (v n)).inner (𝕜 := ℂ)
      (Lp.aestronglyMeasurable (w n))).re)
  · intro n
    exact ae_of_all _ fun x => weighted_re_inner_bound (a x) (v n x) (w n x)
  · filter_upwards [hsv, hsw] with x hx hy
    exact (hx.mul_left (a x ^ 2)).add hy
  · have he : (fun x => a x ^ 2 * ‖ensemble v hv x‖ ^ 2 + ‖ensemble w hw x‖ ^ 2) =ᵐ[μ]
        (fun x => ∑' n, (a x ^ 2 * ‖v n x‖ ^ 2 + ‖w n x‖ ^ 2)) := by
      filter_upwards [ensemble_norm_sq_ae v hv, ensemble_norm_sq_ae w hw, hsv, hsw]
        with x hx hy hsx hsy
      rw [hx, hy, (hsx.mul_left (a x ^ 2)).tsum_add hsy, tsum_mul_left]
    exact (hi.add hiw).congr he
  · filter_upwards [ensemble_represents_ae v hv, ensemble_represents_ae w hw,
      ensemble_inner_ae v w hv hw] with x hx hy hinner
    have hs : Summable (fun n => inner ℂ (v n x) (w n x)) := by
      have hh := (integrable_count_iff.mp
        (L2.integrable_inner (𝕜 := ℂ) (ensemble v hv x) (ensemble w hw x))).of_norm
      simpa only [hx, hy] using hh
    have hsum : HasSum (fun n => inner ℂ (v n x) (w n x))
        (inner ℂ (ensemble v hv x) (ensemble w hw x)) := by
      rw [hinner]
      exact hs.hasSum
    exact (Complex.reCLM.hasSum hsum).mul_left (a x)

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Fubini for an integrable unbounded real current weight. -/
theorem curry_tested_re_inner
    (u v : Lp H 2 ((volume : Measure (Position I)).prod (volume : Measure (Position J))))
    (a : Position I → ℝ)
    (hi : Integrable (fun p => a p.1 * (inner ℂ (u p) (v p)).re) (volume.prod volume)) :
    Integrable (fun x => a x * (inner ℂ (curry u x) (curry v x)).re) ∧
      (∫ x, a x * (inner ℂ (curry u x) (curry v x)).re) =
        ∫ p, a p.1 * (inner ℂ (u p) (v p)).re := by
  have he : (fun x => a x * (inner ℂ (curry u x) (curry v x)).re) =ᵐ[volume]
      fun x => ∫ y, a x * (inner ℂ (u (x, y)) (v (x, y))).re := by
    filter_upwards [curry_inner_ae u v, (L2.integrable_inner (𝕜 := ℂ) u v).prod_right_ae]
      with x hx hix
    have hr := Complex.reCLM.integral_comp_comm hix
    simp only [Complex.reCLM_apply] at hr
    rw [hx, ← hr, integral_const_mul]
  exact ⟨hi.integral_prod_left.congr he.symm,
    (integral_congr_ae he).trans (integral_prod _ hi).symm⟩

variable {N : ℕ}

/-- The selected-particle marginal current is the weighted configuration
current whenever that configuration integrand is integrable. -/
theorem particleMap_tested_re_inner (i : Fin N)
    (u v : ElectronicH1Space.L2 H (Fin N × Fin 3))
    (a : PhysicalPairSpace.Position → ℝ)
    (hi : Integrable (fun z => a (SymmetricLift.particle z i) * (inner ℂ (u z) (v z)).re)) :
    Integrable (fun x => a x * (inner ℂ (particleMap i u x) (particleMap i v x)).re) ∧
      (∫ x, a x * (inner ℂ (particleMap i u x) (particleMap i v x)).re) =
        ∫ z, a (SymmetricLift.particle z i) * (inner ℂ (u z) (v z)).re := by
  let L := split i
  let hL := split_symm_measurePreserving i
  have hrep : (fun p : PhysicalPairSpace.Position × Spectator i => a p.1 *
      (inner ℂ (productMap L hL u p) (productMap L hL v p)).re) =ᵐ[volume.prod volume]
      fun p => a (SymmetricLift.particle (L.symm p) i) *
        (inner ℂ (u (L.symm p)) (v (L.symm p))).re := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u hL,
      Lp.coeFn_compMeasurePreserving v hL] with p hu hv
    change a p.1 * (inner ℂ (Lp.compMeasurePreserving L.symm hL u p)
      (Lp.compMeasurePreserving L.symm hL v p)).re = _
    rw [hu, hv, ← PhysicalSourcePair.split_fst_eq_particle i,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hip := (hL.integrable_comp_emb
    (g := fun z => a (SymmetricLift.particle z i) * (inner ℂ (u z) (v z)).re)
    L.symm.toHomeomorph.measurableEmbedding).mpr hi
  have hc := curry_tested_re_inner (productMap L hL u) (productMap L hL v) a
    (hip.congr hrep.symm)
  refine ⟨hc.1, hc.2.trans ?_⟩
  have hmap := hL.integral_comp L.symm.toHomeomorph.measurableEmbedding
    (fun z : Configuration N => a (SymmetricLift.particle z i) * (inner ℂ (u z) (v z)).re)
  exact (integral_congr_ae hrep).trans hmap

end GptLean.PhysicalWeightedCurrentCore
