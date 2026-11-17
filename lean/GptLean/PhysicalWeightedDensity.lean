import GptLean.PhysicalElectronicDensity
import GptLean.PhysicalEnsembleObservables
import GptLean.Repair.PairHardy
import GptLean.Repair.IntegratedChannel

/-!
The density-weighted hypothesis in Appendix C implies the corresponding
configuration integrability for every source vector, and summability of
their weighted integrals. All weights may be unbounded and nonnegative.
-/

noncomputable section

namespace GptLean.PhysicalWeightedDensity

open MeasureTheory Filter PhysicalElectronicDensity PhysicalSourceCoordinates
  PhysicalSourceMarginal PhysicalSourcePair PhysicalSourceH1 PhysicalSourceFubini
  PhysicalEnsembleSource SymmetricLift Repair
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H] [CompleteSpace H]

theorem particle_weighted (u : Wave (N := N) (H := H)) (i : Fin N)
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume)
    (hw0 : ∀ y, 0 ≤ w y)
    (hi : Integrable (fun y => w y * ‖particleMap i u y‖ ^ 2)) :
    Integrable (fun x => w (particle x i) * ‖u x‖ ^ 2) ∧
      (∫ x, w (particle x i) * ‖u x‖ ^ 2) = ∫ y, w y * ‖particleMap i u y‖ ^ 2 := by
  let L := split i
  let hL := split_symm_measurePreserving i
  have hp := product_weighted_norm_sq (productMap L hL u) w hw hw0 hi
  have hrep : (fun p : PhysicalPairSpace.Position × Spectator i =>
      w p.1 * ‖productMap L hL u p‖ ^ 2) =ᵐ[volume.prod volume]
      fun p => w (particle (L.symm p) i) * ‖u (L.symm p)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u hL] with p hp
    change w p.1 * ‖Lp.compMeasurePreserving L.symm hL u p‖ ^ 2 = _
    rw [hp, ← split_fst_eq_particle i, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hir := (hL.integrable_comp_emb
    (g := fun x => w (particle x i) * ‖u x‖ ^ 2)
    L.symm.toHomeomorph.measurableEmbedding).mp (hp.1.congr hrep)
  refine ⟨hir, ?_⟩
  exact (hL.integral_comp L.symm.toHomeomorph.measurableEmbedding _).symm.trans
    ((integral_congr_ae hrep.symm).trans hp.2)

/-- A nonnegative one-particle density weight is exactly the sum of the
configuration pullbacks, including their integrability. -/
theorem density_weighted (u : Wave (N := N) (H := H))
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume)
    (hw0 : ∀ y, 0 ≤ w y) (hi : Integrable (fun y => w y * density u y)) :
    Integrable (fun x => (∑ i, w (particle x i)) * ‖u x‖ ^ 2) ∧
      (∫ x, (∑ i, w (particle x i)) * ‖u x‖ ^ 2) = ∫ y, w y * density u y := by
  have hip (i : Fin N) : Integrable (fun y => w y * ‖particleMap i u y‖ ^ 2) := by
    apply hi.mono' (hw.mul ((Lp.aestronglyMeasurable (particleMap i u)).norm.pow 2))
    filter_upwards [density_ae u] with y hy
    change ‖w y * ‖particleMap i u y‖ ^ 2‖ ≤ w y * density u y
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 y) (sq_nonneg _)), hy]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖particleMap j u y‖)
        (Finset.mem_univ i)) (hw0 y)
  have hp (i : Fin N) := particle_weighted u i w hw hw0 (hip i)
  have hs : Integrable (fun x => (∑ i, w (particle x i)) * ‖u x‖ ^ 2) := by
    simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => (hp i).1)
  refine ⟨hs, ?_⟩
  calc
    _ = ∑ i, ∫ x, w (particle x i) * ‖u x‖ ^ 2 := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => (hp i).1)
    _ = ∑ i, ∫ y, w y * ‖particleMap i u y‖ ^ 2 :=
      Finset.sum_congr rfl (fun i _ => (hp i).2)
    _ = ∫ y, ∑ i, w y * ‖particleMap i u y‖ ^ 2 :=
      (integral_finsetSum _ (fun i _ => hip i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [density_ae u] with y hy
      rw [hy, densityFunction, Finset.mul_sum]

section Ensemble

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- The weighted source series can be integrated from its actual Hilbert
ensemble density. This proves each term finite before summing it. -/
theorem ensemble_weighted (v : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2))
    (w : X → ℝ) (hw : AEStronglyMeasurable w μ) (hw0 : ∀ x, 0 ≤ w x)
    (hi : Integrable (fun x => w x * ‖ensemble v hv x‖ ^ 2) μ) :
    (∀ n, Integrable (fun x => w x * ‖v n x‖ ^ 2) μ) ∧
      HasSum (fun n => ∫ x, w x * ‖v n x‖ ^ 2 ∂μ)
        (∫ x, w x * ‖ensemble v hv x‖ ^ 2 ∂μ) := by
  have hm (n) := hw.mul ((Lp.aestronglyMeasurable (v n)).norm.pow 2)
  have hpos (n) : ∀ᵐ x ∂μ, 0 ≤ w x * ‖v n x‖ ^ 2 :=
    ae_of_all _ fun x => mul_nonneg (hw0 x) (sq_nonneg _)
  have hs : ∀ᵐ x ∂μ, HasSum (fun n => w x * ‖v n x‖ ^ 2)
      (w x * ‖ensemble v hv x‖ ^ 2) := by
    filter_upwards [ensemble_squares_summable_ae v hv, ensemble_norm_sq_ae v hv]
      with x hx he
    rw [he]
    exact hx.hasSum.mul_left (w x)
  exact ⟨integrable_term_of_nonnegative_hasSum hm hpos hs hi,
    hasSum_integral_nonnegative hm hpos hs hi⟩

end Ensemble

private instance fiberSeparable : TopologicalSpace.SeparableSpace (Fiber H) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- The article's one density-weighted condition supplies every source
pullback integral and the exact total sum. -/
theorem ensemble_density_weighted (v : ℕ → Wave (N := N) (H := H))
    (hv : Summable (fun n => ‖v n‖ ^ 2))
    (w : PhysicalPairSpace.Position → ℝ) (hw : AEStronglyMeasurable w volume)
    (hw0 : ∀ y, 0 ≤ w y)
    (hi : Integrable (fun y => w y * density (ensemble v hv) y)) :
    (∀ n, Integrable (fun x => (∑ i, w (particle x i)) * ‖v n x‖ ^ 2)) ∧
      HasSum (fun n => ∫ x, (∑ i, w (particle x i)) * ‖v n x‖ ^ 2)
        (∫ y, w y * density (ensemble v hv) y) := by
  have hd := density_weighted (ensemble v hv) w hw hw0 hi
  have hm : AEStronglyMeasurable (fun x : SymmetricLift.Configuration N => ∑ i, w (particle x i)) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => particle_test_measurable i w hw
  have hs := ensemble_weighted v hv (fun x => ∑ i, w (particle x i)) hm
    (fun x => Finset.sum_nonneg fun i _ => hw0 _) hd.1
  exact ⟨hs.1, hd.2 ▸ hs.2⟩

end GptLean.PhysicalWeightedDensity
