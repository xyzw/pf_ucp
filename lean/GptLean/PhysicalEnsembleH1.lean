import GptLean.PhysicalEnsembleSource
import GptLean.ElectronicH1Space
import GptLean.SymmetricLift.L2Mollification

/-!
Square-summable actual H1 vectors form an H1 source with the spectral
index as a counting-measure Hilbert factor. Bounded coordinate evaluation
commutes with the Bochner weak identity, so no ensemble regularity
premise is introduced.
-/

noncomputable section

namespace GptLean.PhysicalEnsembleH1

open MeasureTheory Filter GptLean.SymmetricLift GptLean.ElectronicH1Space
open GptLean.PhysicalEnsembleSource
open scoped ENNReal Topology ContDiff

set_option backward.isDefEq.respectTransparency.types false

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Evaluation is bounded on counting-measure L2, realized by a singleton integral. -/
def countEval (n : ℕ) : Fiber H →L[ℝ] H :=
  l2SetIntegralCLM (μ := Measure.count) {n} (measurableSet_singleton n) (by simp)

omit [TopologicalSpace.SeparableSpace H] in
@[simp] theorem countEval_apply (n : ℕ) (v : Fiber H) : countEval n v = v n := by
  rw [countEval, l2SetIntegralCLM_apply, integral_singleton]
  simp

omit [DecidableEq I] in
theorem countEval_integral_test (v : ℕ → L2 H I)
    (hv : Summable (fun n => ‖v n‖ ^ 2)) (φ : EuclideanSpace ℝ I → ℝ)
    (hφ : MemLp φ 2 volume) (n : ℕ) :
    countEval n (∫ x, φ x • ensemble v hv x) = ∫ x, φ x • v n x := by
  rw [← (countEval n).integral_comp_comm (integrable_l2_test hφ (ensemble v hv))]
  apply integral_congr_ae
  filter_upwards [ensemble_represents_ae v hv] with x hx
  rw [map_smul, countEval_apply, hx n]

/-- Each counted source component satisfies the original distributional identity. -/
theorem ensemble_weak (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) :
    HasWeakH1Local (ensemble (fun n => value (v n)) hv)
      (fun i => ensemble (fun n => derivative i (v n)) (hd i)) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun i K _ => (Lp.memLp _).restrict K, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro n
  rw [← countEval_apply n, ← countEval_apply n]
  rw [map_neg, countEval_integral_test _ _ φ
    (hφ.continuous.memLp_of_hasCompactSupport hs) n,
    countEval_integral_test _ _ _
      (hdφ.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)) n]
  exact (weak (v n)).weak i φ hφ hs

def ensembleH1 (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) : H1 (Fiber H) I :=
  ⟨(ensemble (fun n => value (v n)) hv,
      fun i => ensemble (fun n => derivative i (v n)) (hd i)), ensemble_weak v hv hd⟩

@[simp] theorem value_ensembleH1 (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) :
    value (ensembleH1 v hv hd) = ensemble (fun n => value (v n)) hv := rfl

@[simp] theorem derivative_ensembleH1 (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) (i : I) :
    derivative i (ensembleH1 v hv hd) = ensemble (fun n => derivative i (v n)) (hd i) := rfl

theorem norm_value_ensembleH1_sq (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) :
    ‖value (ensembleH1 v hv hd)‖ ^ 2 = ∑' n, ‖value (v n)‖ ^ 2 :=
  ensemble_norm_sq _ hv

theorem norm_derivative_ensembleH1_sq (v : ℕ → H1 H I)
    (hv : Summable (fun n => ‖value (v n)‖ ^ 2))
    (hd : ∀ i, Summable (fun n => ‖derivative i (v n)‖ ^ 2)) (i : I) :
    ‖derivative i (ensembleH1 v hv hd)‖ ^ 2 = ∑' n, ‖derivative i (v n)‖ ^ 2 :=
  ensemble_norm_sq _ (hd i)

end GptLean.PhysicalEnsembleH1
