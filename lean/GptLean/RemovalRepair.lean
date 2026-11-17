import GptLean.Repair.MeasuredTagSobolev
import GptLean.Repair.CountableFrame
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
The actual six-component repair tag supplies the Lipschitz bound needed
by the recursive tensor lift. Its derivative metric, connection and weak
H1 regularity therefore require only bounds on the residual velocity and
its Jacobian. No regularity or metric of the finished lift is assumed.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Multipliers
open scoped NNReal

abbrev RepairSpace := EuclideanSpace ℝ (Fin 3)

def repairTag (V M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : RepairSpace) : SixTag :=
  selectedTag V M v (WithLp.ofLp x)

def repairTagGradient (V M : ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (j : Fin 3) (x : RepairSpace) : SixTag :=
  selectedTagDerivative V M v (WithLp.ofLp x) j

theorem repairTag_differentiable {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hv : Differentiable ℝ v) (hvV : ∀ x j, |v x j| ≤ V) :
    Differentiable ℝ (repairTag V M v) := by
  by_cases hz : V = 0
  · subst V
    change Differentiable ℝ (fun x : RepairSpace => selectedTag 0 M v (WithLp.ofLp x))
    simp only [selectedTag_zero]
    exact differentiable_const _
  · have hp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
    have hq := three_mul_lt_sqrt_max hp M
    have hqp : 0 < Real.sqrt (max (36 * V ^ 2) M) := by linarith
    intro x
    apply (differentiableAt_piLp 2).mpr
    intro j
    have hvj0 : Differentiable ℝ (fun y => v y j.1) := (differentiable_pi.mp hv) j.1
    have hvj : DifferentiableAt ℝ (fun x : RepairSpace => v (WithLp.ofLp x) j.1) x :=
      hvj0.differentiableAt.comp x (PiLp.hasFDerivAt_ofLp 2 x).differentiableAt
    have ha := amp_pos (v := v) (y := WithLp.ofLp x) hqp j
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hvV _ _) (by norm_num)) hq)
    have ha' : DifferentiableAt ℝ
        (fun x : RepairSpace => amp (Real.sqrt (max (36 * V ^ 2) M)) v j
          (WithLp.ofLp x)) x := by
      unfold amp
      fun_prop
    have hs := ha'.sqrt ha.ne'
    change DifferentiableAt ℝ (fun x : RepairSpace =>
      K (selectedWaveNumber V M) v j (WithLp.ofLp x)) x
    simp only [selectedWaveNumber, hz, ite_false, K, apVal]
    have hx : DifferentiableAt ℝ (fun x : RepairSpace => x j.1) x :=
      (PiLp.hasFDerivAt_apply 2 x j.1).differentiableAt
    fun_prop

/-- A coordinate bound gives an operator bound in three dimensions. -/
theorem norm_linearMap_le_three {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : RepairSpace →L[ℝ] H) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ j, ‖A (EuclideanSpace.single j 1)‖ ≤ c) : ‖A‖ ≤ 3 * c := by
  apply A.opNorm_le_bound (by positivity)
  intro x
  have hx : x = ∑ j : Fin 3, (x j) • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Pi.single_apply, mul_ite]
  calc
    ‖A x‖ = ‖∑ j : Fin 3, x j • A (EuclideanSpace.single j 1)‖ := by
      conv_lhs => rw [hx]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ j : Fin 3, ‖x j • A (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖x‖ * c := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le x j) (hA j) (norm_nonneg _) (norm_nonneg _)
    _ = (3 * c) * ‖x‖ := by simp; ring

def repairLipschitzConstant (V M : ℝ) : ℝ≥0 :=
  ⟨3 * Real.sqrt (36 * V ^ 2 + 2 * M), by positivity⟩

theorem repairTag_lipschitz {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hv : Differentiable ℝ v)
    (hvV : ∀ x j, |v x j| ≤ V)
    (hdv : ∀ x, ∑ i, ∑ j,
      (fderiv ℝ v x (Pi.single j (1 : ℝ)) i) ^ 2 ≤ M ^ 2) :
    LipschitzWith (repairLipschitzConstant V M) (repairTag V M v) := by
  have ht := repairTag_differentiable (M := M) hV hv hvV
  apply lipschitzWith_of_nnnorm_fderiv_le ht
  intro x
  change ‖fderiv ℝ (repairTag V M v) x‖ ≤ 3 * Real.sqrt (36 * V ^ 2 + 2 * M)
  apply norm_linearMap_le_three _ (Real.sqrt_nonneg _)
  intro j
  have hd (i l : Fin 3) := hasDerivAt_pi.mp
    ((hv (WithLp.ofLp x)).hasFDerivAt.hasLineDerivAt (Pi.single l (1 : ℝ))) i
  have he := (ht x).hasFDerivAt.hasLineDerivAt (EuclideanSpace.single j 1)
  have he' := selectedTag_hasLineDerivAt (M := M) x hV (hvV _) hd j
  have hident := he.unique he'
  rw [hident]
  have hmetric := selectedTag_metric_le hV hM (hvV (WithLp.ofLp x))
    (hdv (WithLp.ofLp x)) hd
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun l _ => sq_nonneg
    ‖selectedTagDerivative V M v (WithLp.ofLp x) l‖) (Finset.mem_univ j)).trans hmetric

theorem repairTag_metric {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hv : Differentiable ℝ v)
    (hvV : ∀ x j, |v x j| ≤ V)
    (hdv : ∀ x, ∑ i, ∑ j,
      (fderiv ℝ v x (Pi.single j (1 : ℝ)) i) ^ 2 ≤ M ^ 2) (x : RepairSpace) :
    (∑ j, ‖repairTagGradient V M v j x‖ ^ 2) ≤
      (repairLipschitzConstant V M : ℝ) ^ 2 := by
  have hm := selectedTag_metric_le hV hM (hvV (WithLp.ofLp x))
    (hdv (WithLp.ofLp x)) (fun i j => hasDerivAt_pi.mp
      ((hv (WithLp.ofLp x)).hasFDerivAt.hasLineDerivAt (Pi.single j (1 : ℝ))) i)
  have hnon : 0 ≤ 36 * V ^ 2 + 2 * M := by positivity
  change (∑ j, ‖selectedTagDerivative V M v (WithLp.ofLp x) j‖ ^ 2) ≤ _
  change (∑ j, ‖selectedTagDerivative V M v (WithLp.ofLp x) j‖ ^ 2) ≤
    (3 * Real.sqrt (36 * V ^ 2 + 2 * M)) ^ 2
  rw [mul_pow, Real.sq_sqrt hnon]
  nlinarith

/-- Explicit residual bounds yield the full many-particle metric. -/
theorem repairLift_metric (B : TensorBackground SixTag) (T : TensorMultilinearData B)
    (N : ℕ) {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hv : Differentiable ℝ v)
    (hvV : ∀ x j, |v x j| ≤ V)
    (hdv : ∀ x, ∑ i, ∑ j,
      (fderiv ℝ v x (Pi.single j (1 : ℝ)) i) ^ 2 ≤ M ^ 2) :
    ∀ᵐ x ∂volume, (∑ q, ‖recursiveLiftWeakGradient B N (repairTag V M v)
      (repairTagGradient V M v) q x‖ ^ 2) ≤
        9 * ((N : ℝ) + liftMetricConstant N) * (36 * V ^ 2 + 2 * M) := by
  have h := recursiveLift_metric_uniform_ae B T N (repairTag V M v)
    (repairTagGradient V M v)
    (fun x => selectedTag_norm V M v hV _ (hvV _))
    (repairLipschitzConstant V M) (repairTag_lipschitz hV hM hv hvV hdv)
    (Eventually.of_forall (repairTag_metric hV hM hv hvV hdv))
  filter_upwards [h] with x hx
  apply hx.trans_eq
  change ((N : ℝ) + liftMetricConstant N) * (3 * Real.sqrt (36 * V ^ 2 + 2 * M)) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 36 * V ^ 2 + 2 * M)]
  ring

end GptLean.Repair
