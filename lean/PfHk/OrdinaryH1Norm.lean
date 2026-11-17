import GptLean.ElectronicH1Space
import GptLean.PhysicalLpUpgrade

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.OrdinaryH1Norm
open MeasureTheory GptLean.ElectronicH1Space
open scoped ENNReal
set_option Elab.async false
set_option maxHeartbeats 30000

theorem lp_upgrade_bound {X Q H : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (L : Q →L[ℝ] Lp H p μ) (hm : ∀ u, MemLp (L u) q μ) (u : Q) :
    (eLpNorm (L u) q μ).toReal ≤ ‖GptLean.PhysicalLpUpgrade.map L hm‖ * ‖u‖ := by
  have he := GptLean.PhysicalLpUpgrade.map_ae L hm u
  have hn : (eLpNorm (L u) q μ).toReal = ‖GptLean.PhysicalLpUpgrade.map L hm u‖ :=
    (congrArg ENNReal.toReal (eLpNorm_congr_ae he.symm)).trans (Lp.norm_def _).symm
  exact hn.le.trans ((GptLean.PhysicalLpUpgrade.map L hm).le_opNorm u)

private theorem product_gradient_bound {I A B : Type*} [Fintype I]
    [NormedAddCommGroup A] [NormedAddCommGroup B] (x : A) (d : I → B) :
    (max ‖x‖ ‖d‖) ^ 2 ≤ ‖x‖ ^ 2 + ∑ i, ‖d i‖ ^ 2 := by
  classical
  have hd : 0 ≤ ∑ i, ‖d i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : ‖d‖ ≤ Real.sqrt (∑ i, ‖d i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖d j‖) (Finset.mem_univ i))
  have hg2 := (pow_le_pow_left₀ (norm_nonneg _) hg 2).trans_eq (Real.sq_sqrt hd)
  rcases le_total ‖x‖ ‖d‖ with h | h
  · rw [max_eq_right h]
    linarith only [hg2, sq_nonneg ‖x‖]
  · rw [max_eq_left h]
    linarith only [hd]

theorem h1_norm_sq_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] {I : Type*} [Fintype I] [DecidableEq I]
    (u : H1 H I) : ‖u‖ ^ 2 ≤ ‖value u‖ ^ 2 + derivativeEnergy u := by
  have he : derivativeEnergy u = ∑ i, ‖gradient u i‖ ^ 2 := by
    unfold derivativeEnergy
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : L2 H I => ‖z‖ ^ 2)
      ((derivative_apply u i).trans (congrFun (gradient_apply u).symm i))
  have hb := product_gradient_bound (I := I) (A := L2 H I) (B := L2 H I)
    (value (E := H) (I := I) u) (gradient (E := H) (I := I) u)
  exact (congrArg (fun r : ℝ => r ^ 2) (norm_eq_max (E := H) (I := I) u)).le.trans
    (hb.trans_eq (congrArg (fun r : ℝ => ‖value (E := H) (I := I) u‖ ^ 2 + r) he.symm))

end PfHk.OrdinaryH1Norm

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
