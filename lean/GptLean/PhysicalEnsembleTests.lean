import GptLean.PhysicalSourceTests
import GptLean.PhysicalEnsemblePair
import GptLean.PhysicalEnsembleObservables

/-!
Bounded physical tests of the constructed ensemble density and current
equal the sums of the actual configuration-space source integrals.
Square summability supplies the domination needed for the current sum.
-/

noncomputable section

namespace GptLean.PhysicalEnsembleSource

open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

theorem ensemble_tested_re_inner_hasSum (v w : ℕ → Lp H 2 μ)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) (hw : Summable (fun n => ‖w n‖ ^ 2))
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    HasSum (fun n => ∫ x, a x * (inner ℂ (v n x) (w n x)).re ∂μ)
      (∫ x, a x * (inner ℂ (ensemble v hv x) (ensemble w hw x)).re ∂μ) := by
  have hiv := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble v hv))).mp (Lp.memLp (ensemble v hv))
  have hiw := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (ensemble w hw))).mp (Lp.memLp (ensemble w hw))
  have hsv := ensemble_squares_summable_ae v hv
  have hsw := ensemble_squares_summable_ae w hw
  apply hasSum_integral_of_dominated_convergence
    (fun n x => |C| * (‖v n x‖ ^ 2 + ‖w n x‖ ^ 2))
  · intro n
    exact ha.mul (((Lp.aestronglyMeasurable (v n)).inner (𝕜 := ℂ)
      (Lp.aestronglyMeasurable (w n))).re)
  · intro n
    filter_upwards [hb] with x hx
    have hinner : |(inner ℂ (v n x) (w n x)).re| ≤ ‖v n x‖ * ‖w n x‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hsquare : ‖v n x‖ * ‖w n x‖ ≤ ‖v n x‖ ^ 2 + ‖w n x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v n x‖ - ‖w n x‖)]
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul (hx.trans (le_abs_self C)) (hinner.trans hsquare)
        (abs_nonneg _) (abs_nonneg C)
  · filter_upwards [hsv, hsw] with x hx hy
    exact (hx.add hy).mul_left |C|
  · have he : (fun x => |C| * (‖ensemble v hv x‖ ^ 2 + ‖ensemble w hw x‖ ^ 2)) =ᵐ[μ]
        (fun x => ∑' n, |C| * (‖v n x‖ ^ 2 + ‖w n x‖ ^ 2)) := by
      filter_upwards [ensemble_norm_sq_ae v hv, ensemble_norm_sq_ae w hw, hsv, hsw]
        with x hx hy hsx hsy
      rw [hx, hy, tsum_mul_left, hsx.tsum_add hsy]
    exact ((hiv.add hiw).const_mul |C|).congr he
  · filter_upwards [ensemble_represents_ae v hv, ensemble_represents_ae w hw,
      ensemble_inner_ae v w hv hw] with x hx hy hinner
    have hs : Summable (fun n => inner ℂ (v n x) (w n x)) := by
      have hi := (integrable_count_iff.mp
        (L2.integrable_inner (𝕜 := ℂ) (ensemble v hv x) (ensemble w hw x))).of_norm
      simpa only [hx, hy] using hi
    have hsum : HasSum (fun n => inner ℂ (v n x) (w n x))
        (inner ℂ (ensemble v hv x) (ensemble w hw x)) := by
      rw [hinner]
      exact hs.hasSum
    exact (Complex.reCLM.hasSum hsum).mul_left (a x)

end GptLean.PhysicalEnsembleSource

namespace GptLean.PhysicalSourcePair

open MeasureTheory ElectronicH1Space PhysicalPairSpace PhysicalEnsembleSource PhysicalEnsembleH1
open PhysicalSourceCoordinates
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem tested_density_ofEnsemble (i : Fin N) (v : ℕ → H1 H (Fin N × Fin 3))
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ b, Summable (fun n => ‖derivative b (v n)‖ ^ 2))
    (d : Fin 3 → ℕ → L2 H (Fin N × Fin 3))
    (hcov : ∀ b, Summable (fun n => ‖d b n‖ ^ 2))
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * densityL1 (ofEnsemble i v hv hd d hcov) x) =
      (N : ℝ) * ∑' n, ∫ z, a ((split i) z).1 * ‖value (v n) z‖ ^ 2 := by
  have ha' := ha.comp_fst.comp_measurePreserving (split_measurePreserving i)
  have hb' := (split_measurePreserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae hb)
  have hs := ensemble_tested_mass_hasSum (fun n => value (v n)) hv
    (fun z => a ((split i) z).1) ha' hb'
  exact (tested_density_ofWaveFunction i (ensembleH1 v hv hd)
    (fun b => ensemble (d b) (hcov b)) a ha hb).trans
      (congrArg (fun t : ℝ => (N : ℝ) * t) hs.tsum_eq.symm)

theorem tested_current_ofEnsemble (i : Fin N) (v : ℕ → H1 H (Fin N × Fin 3))
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ b, Summable (fun n => ‖derivative b (v n)‖ ^ 2))
    (d : Fin 3 → ℕ → L2 H (Fin N × Fin 3))
    (hcov : ∀ b, Summable (fun n => ‖d b n‖ ^ 2)) (b : Fin 3)
    (a : PhysicalPairSpace.Position → ℝ) (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖a x‖ ≤ C) :
    (∫ x, a x * currentL1 (ofEnsemble i v hv hd d hcov) x b) =
      (N : ℝ) * ∑' n, ∫ z, a ((split i) z).1 * (inner ℂ (value (v n) z) (d b n z)).re := by
  have ha' := ha.comp_fst.comp_measurePreserving (split_measurePreserving i)
  have hb' := (split_measurePreserving i).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae hb)
  have hs := ensemble_tested_re_inner_hasSum (fun n => value (v n)) (d b) hv (hcov b)
    (fun z => a ((split i) z).1) ha' hb'
  exact (tested_current_ofWaveFunction i (ensembleH1 v hv hd)
    (fun a => ensemble (d a) (hcov a)) b a ha hb).trans
      (congrArg (fun t : ℝ => (N : ℝ) * t) hs.tsum_eq.symm)

end GptLean.PhysicalSourcePair
