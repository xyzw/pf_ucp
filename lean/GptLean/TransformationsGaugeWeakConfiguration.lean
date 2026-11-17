import GptLean.TransformationsGaugeWeak
import GptLean.RepresentabilityAmplitudePullback

/-! The full many-electron phase for an article-regular spatial gauge.
Pull back the proved weak one-particle phase and multiply its finitely many
unit-modulus factors. This avoids any extra regularity assumption on S. -/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory Filter SymmetricLift Repair TransformationsPhase Representability
open scoped ENNReal ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem weakH1Local_mul_of_norm_le_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {f g : EuclideanSpace ℝ I → ℂ} {df dg : I → EuclideanSpace ℝ I → ℂ}
    (hf : HasWeakH1Local f df) (hg : HasWeakH1Local g dg)
    (hfn : ∀ x, ‖f x‖ ≤ 1) (hgn : ∀ x, ‖g x‖ ≤ 1) :
    HasWeakH1Local (fun x => f x * g x)
      (fun i x => f x * dg i x + df i x * g x) := by
  apply weakH1Local_complex_smul_of_weighted hf hg
  · intro K hK
    apply (hg.function_memLp K hK).mono ((hf.function_memLp K hK).1.mul (hg.function_memLp K hK).1)
    exact ae_of_all _ fun x => by
      change ‖f x * g x‖ ≤ ‖g x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hfn x)
  · intro i K hK
    apply (hg.derivative_memLp i K hK).mono
      ((hf.function_memLp K hK).1.mul (hg.derivative_memLp i K hK).1)
    exact ae_of_all _ fun x => by
      change ‖f x * dg i x‖ ≤ ‖dg i x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hfn x)
  · intro i K hK
    apply (hf.derivative_memLp i K hK).mono
      ((hf.derivative_memLp i K hK).1.mul (hg.function_memLp K hK).1)
    exact ae_of_all _ fun x => by
      change ‖df i x * g x‖ ≤ ‖df i x‖
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hgn x)

namespace WeakSpatialGauge

variable (G : WeakSpatialGauge) (N : ℕ)

def configurationAngle (x : Configuration N) : ℝ := ∑ j, G.fn (particle x j)

theorem configurationAngle_measurable : AEStronglyMeasurable (G.configurationAngle N) volume := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro j _
  have h := locallyIntegrable_comp_surjective_linearMap (μ := volume)
    (particleLinear j) (particleLinear_surjective j) G.locallyIntegrable
  exact h.aestronglyMeasurable

def configurationPhase (x : Configuration N) : ℂ :=
  ∏ j, factor G.fn (particle x j)

theorem factor_configurationAngle (x : Configuration N) :
    factor (G.configurationAngle N) x = G.configurationPhase N x := by
  simp only [factor, configurationAngle, configurationPhase, Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]

theorem norm_configurationPhase (x : Configuration N) : ‖G.configurationPhase N x‖ = 1 := by
  simp only [configurationPhase, norm_prod, norm_factor, Finset.prod_const_one]

theorem weak_configurationPhase : HasWeakH1Local (G.configurationPhase N)
    (fun q x => G.configurationPhase N x * (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ))) := by
  classical
  have hpartial (s : Finset (Fin N)) :
      HasWeakH1Local (fun x : Configuration N => ∏ j ∈ s, factor G.fn (particle x j))
        (fun q x => if q.1 ∈ s then
          (∏ j ∈ s, factor G.fn (particle x j)) *
            (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ)) else 0) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa using (weakH1Local_of_contDiff
        (contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration N => (1 : ℂ))))
    | @insert j s hjs ih =>
      have hj := hasWeakH1Local_particlePullback j G.weak_phase
      have hp := weakH1Local_mul_of_norm_le_one hj ih
        (fun x => (norm_factor G.fn (particle x j)).le)
        (fun x => by simp only [norm_prod, norm_factor, Finset.prod_const_one, le_refl])
      apply hp.congr
      · exact ae_of_all _ fun x => by simp only [Finset.prod_insert hjs]
      · intro q
        exact ae_of_all _ fun x => by
          simp only [particlePullbackGradient, phaseDerivative_apply, factor,
            Finset.mem_insert, Finset.prod_insert hjs]
          by_cases hqj : q.1 = j
          · subst j
            simp [hjs] <;> ring
          · simp only [hqj, if_false, false_or, zero_mul, add_zero]
            split_ifs <;> ring
  change HasWeakH1Local (fun x : Configuration N => ∏ j, factor G.fn (particle x j))
    (fun q x => (∏ j, factor G.fn (particle x j)) *
      (Complex.I * (G.gradient q.2 (particle x q.1) : ℂ)))
  simpa only [Finset.mem_univ, if_true] using hpartial Finset.univ

end WeakSpatialGauge

end GptLean.TransformationsGauge
