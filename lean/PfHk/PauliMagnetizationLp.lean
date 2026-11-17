import PfHk.PauliMagnetizationWeak
import PfHk.PauliMagneticOperator

/-! Integrable representatives of spin pairings and their bounded scalar
tests. These connect the H1 product rule to distributional derivatives. -/

noncomputable section
namespace PfHk.PauliMagnetizationLp

open MeasureTheory GptLean GptLean.PhotonLocalization
  PfHk.PauliSpin PfHk.PauliCurrentCorrection

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ} {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}

def pointPair (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) (x : X) : ℂ :=
  spinPair n (fun s => u s x) (fun s => v s x) k

theorem pair_ae (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    (fun x => ∑ s, inner ℂ (u s x) (sigmaFamily n k v s x)) =ᵐ[μ]
      pointPair n u v k := by
  filter_upwards [ae_all_iff.mpr (fun s => PauliMagneticOperator.sigma_ae μ n k v s)]
    with x hx
  exact Finset.sum_congr rfl (fun s _ => congrArg (inner ℂ (u s x)) (hx s))

theorem pair_integrable (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    Integrable (pointPair n u v k) μ :=
  (integrable_finsetSum Finset.univ (fun s _ => L2.integrable_inner (𝕜 := ℂ)
    (u s) (sigmaFamily n k v s))).congr (pair_ae n u v k)

theorem pair_integral (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    spinPair n u v k = ∫ x, pointPair n u v k x ∂μ := by
  unfold spinPair
  simp_rw [L2.inner_def]
  exact (integral_finsetSum Finset.univ (fun s _ => L2.integrable_inner (𝕜 := ℂ)
    (u s) (sigmaFamily n k v s))).symm.trans (integral_congr_ae (pair_ae n u v k))

theorem pair_integral_re (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    (spinPair n u v k).re = ∫ x, (pointPair n u v k x).re ∂μ :=
  (congrArg Complex.re (pair_integral n u v k)).trans
    (integral_re (pair_integrable n u v k)).symm

theorem weighted_pair_ae (w : X → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B)
    (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    (fun x => (pointPair n (fun s => realL2Multiplier w hw B hB (u s)) v k x).re) =ᵐ[μ]
      fun x => w x * (pointPair n u v k x).re := by
  filter_upwards [ae_all_iff.mpr (fun s => realL2Multiplier_apply w hw B hB (u s))]
    with x hx
  unfold pointPair spinPair
  simp only [hx, inner_smul_left_eq_smul, Complex.re_sum, Complex.smul_re,
    smul_eq_mul, Finset.mul_sum]

theorem weighted_pair_integrable (w : X → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B)
    (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    Integrable (fun x => w x * (pointPair n u v k x).re) μ :=
  ((pair_integrable n (fun s => realL2Multiplier w hw B hB (u s)) v k).re).congr
    (weighted_pair_ae w hw B hB n u v k)

theorem weighted_pair_integral (w : X → ℝ) (hw : AEStronglyMeasurable w μ)
    (B : ℝ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B)
    (n : Fin N) (u v : SpinIndex N → Lp H 2 μ) (k : Fin 3) :
    (spinPair n (fun s => realL2Multiplier w hw B hB (u s)) v k).re =
      ∫ x, w x * (pointPair n u v k x).re ∂μ :=
  (pair_integral_re n (fun s => realL2Multiplier w hw B hB (u s)) v k).trans
    (integral_congr_ae (weighted_pair_ae w hw B hB n u v k))

end PfHk.PauliMagnetizationLp
