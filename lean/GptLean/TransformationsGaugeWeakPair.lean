import GptLean.TransformationsGaugeWeakH1
import GptLean.TransformationsGaugePair
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! The density-current pair action for the article's weak gauge class.
Hölder estimates for the L3 and Linfinity parts replace uniform bounds on
the gradient. Both terms of the energy shift are integrable on the full
physical pair space. -/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalPairSpace SymmetricLift TransformationsPhase
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 600000

namespace InLpThreeAddTop

theorem mul_memLp_one {g f : Position → ℝ} (hg : InLpThreeAddTop g)
    (hf1 : MemLp f 1 volume) (hf32 : MemLp f (3 / 2) volume) :
    MemLp (fun x => g x * f x) 1 volume := by
  let : ENNReal.HolderTriple 3 (3 / 2) 1 :=
    ENNReal.HolderTriple.of_toReal
      ⟨by norm_num [ENNReal.toReal_div], by norm_num [ENNReal.toReal_div], by norm_num⟩
  obtain ⟨a, b, ha, hb, he⟩ := hg
  apply ((hf32.mul' ha).add (hf1.mul' hb)).ae_eq
  filter_upwards [he] with x hx
  change a x * f x + b x * f x = g x * f x
  rw [hx, add_mul]

theorem mul_memLp_three_halves {g f : Position → ℝ} (hg : InLpThreeAddTop g)
    (hf32 : MemLp f (3 / 2) volume) (hf3 : MemLp f 3 volume) :
    MemLp (fun x => g x * f x) (3 / 2) volume := by
  let : ENNReal.HolderTriple 3 3 (3 / 2) :=
    ENNReal.HolderTriple.of_toReal
      ⟨by norm_num [ENNReal.toReal_div], by norm_num [ENNReal.toReal_div], by norm_num⟩
  obtain ⟨a, b, ha, hb, he⟩ := hg
  apply ((hf3.mul' ha).add (hf32.mul' hb)).ae_eq
  filter_upwards [he] with x hx
  change a x * f x + b x * f x = g x * f x
  rw [hx, add_mul]

theorem square_mul_integrable {g f : Position → ℝ} (hg : InLpThreeAddTop g)
    (hf1 : MemLp f 1 volume) (hf3 : MemLp f 3 volume) :
    Integrable (fun x => g x ^ 2 * f x) volume := by
  have hf32 := memLp_three_halves hf1 hf3
  have h1 := hg.mul_memLp_one hf1 hf32
  have h32 := hg.mul_memLp_three_halves hf32 hf3
  have h := memLp_one_iff_integrable.mp (hg.mul_memLp_one h1 h32)
  simpa only [pow_two, mul_assoc] using h

end InLpThreeAddTop

namespace WeakSpatialGauge

variable (G : WeakSpatialGauge)

def gradientVector (x : Position) : Vector := WithLp.toLp 2 (fun a => G.gradient a x)

theorem gradientVector_apply (x : Position) (a : Fin 3) :
    G.gradientVector x a = G.gradient a x := rfl

theorem neg_gradientVector (x : Position) : G.neg.gradientVector x = -G.gradientVector x := by
  ext a
  rfl

theorem gradient_density_memLp_one (p : Pair) (a : Fin 3) :
    MemLp (fun x => G.gradient a x * densityL1 p x) 1 volume :=
  (G.gradient_in_sum a).mul_memLp_one (Lp.memLp _)
    (memLp_three_halves (Lp.memLp _) (SpatialGauge.density_memLp_three p))

theorem gradient_density_memLp_three_halves (p : Pair) (a : Fin 3) :
    MemLp (fun x => G.gradient a x * densityL1 p x) (3 / 2) volume :=
  (G.gradient_in_sum a).mul_memLp_three_halves
    (memLp_three_halves (Lp.memLp _) (SpatialGauge.density_memLp_three p))
    (SpatialGauge.density_memLp_three p)

theorem shift_memLp_one (p : Pair) :
    MemLp (fun x => densityL1 p x • G.gradientVector x) 1 volume := by
  apply MemLp.of_eval_piLp
  intro a
  simpa only [PiLp.smul_apply, gradientVector_apply, smul_eq_mul, mul_comm] using
    G.gradient_density_memLp_one p a

theorem shift_memLp_three_halves (p : Pair) :
    MemLp (fun x => densityL1 p x • G.gradientVector x) (3 / 2) volume := by
  apply MemLp.of_eval_piLp
  intro a
  simpa only [PiLp.smul_apply, gradientVector_apply, smul_eq_mul, mul_comm] using
    G.gradient_density_memLp_three_halves p a

def shiftPair (p : Pair) : Pair :=
  ofFunctions (densityL1 p) (fun x => currentL1 p x + densityL1 p x • G.gradientVector x)
    (Lp.memLp _) (SpatialGauge.density_memLp_three p)
    ((Lp.memLp (currentL1 p)).add (G.shift_memLp_one p))
    ((SpatialGauge.current_memLp_three_halves p).add (G.shift_memLp_three_halves p))

theorem densityL1_shiftPair (p : Pair) : densityL1 (G.shiftPair p) = densityL1 p := by
  simp only [shiftPair, densityL1_ofFunctions, Lp.toLp_coeFn]

theorem currentL1_shiftPair (p : Pair) :
    (currentL1 (G.shiftPair p) : Position → Vector) =ᵐ[volume]
      fun x => currentL1 p x + densityL1 p x • G.gradientVector x :=
  ((Lp.memLp (currentL1 p)).add (G.shift_memLp_one p)).coeFn_toLp

theorem neg_shiftPair (p : Pair) : G.neg.shiftPair (G.shiftPair p) = p := by
  apply pair_ext_ae
  · rw [G.neg.densityL1_shiftPair, G.densityL1_shiftPair]
  · filter_upwards [G.neg.currentL1_shiftPair (G.shiftPair p), G.currentL1_shiftPair p]
      with x h₁ h₂
    rw [G.densityL1_shiftPair] at h₁
    rw [h₁, h₂, neg_gradientVector, smul_neg]
    abel

theorem shiftPair_neg (p : Pair) : G.shiftPair (G.neg.shiftPair p) = p := by
  apply pair_ext_ae
  · rw [G.densityL1_shiftPair, G.neg.densityL1_shiftPair]
  · filter_upwards [G.currentL1_shiftPair (G.neg.shiftPair p), G.neg.currentL1_shiftPair p]
      with x h₁ h₂
    rw [G.neg.densityL1_shiftPair] at h₁
    rw [h₁, h₂, neg_gradientVector, smul_neg]
    abel

def shiftEquiv : Pair ≃ Pair where
  toFun := G.shiftPair
  invFun := G.neg.shiftPair
  left_inv := G.neg_shiftPair
  right_inv := G.shiftPair_neg

theorem gradient_current_integrable (p : Pair) (a : Fin 3) :
    Integrable (fun x => G.gradient a x * currentL1 p x a) volume :=
  memLp_one_iff_integrable.mp ((G.gradient_in_sum a).mul_memLp_one
    ((Lp.memLp (currentL1 p)).eval_piLp a)
    ((SpatialGauge.current_memLp_three_halves p).eval_piLp a))

theorem gradient_square_density_integrable (p : Pair) (a : Fin 3) :
    Integrable (fun x => G.gradient a x ^ 2 * densityL1 p x) volume :=
  (G.gradient_in_sum a).square_mul_integrable (Lp.memLp _)
    (SpatialGauge.density_memLp_three p)

theorem gradient_norm_sq_density_integrable (p : Pair) :
    Integrable (fun x => (∑ a, G.gradient a x ^ 2) * densityL1 p x) volume := by
  simpa only [Finset.sum_mul] using
    integrable_finsetSum Finset.univ (fun a _ => G.gradient_square_density_integrable p a)

def energyShift (p : Pair) : ℝ :=
  (∑ a, ∫ x, G.gradient a x * currentL1 p x a) +
    (1 / 2 : ℝ) * ∫ x, (∑ a, G.gradient a x ^ 2) * densityL1 p x

theorem tested_density_shiftPair (p : Pair) (t : Position → ℝ) :
    (∫ x, t x * densityL1 (G.shiftPair p) x) = ∫ x, t x * densityL1 p x := by
  rw [G.densityL1_shiftPair]

theorem tested_current_shiftPair (p : Pair) (b : Fin 3) (t : Position → ℝ)
    (ht : AEStronglyMeasurable t volume) {c : ℝ} (hc : ∀ x, ‖t x‖ ≤ c) :
    (∫ x, t x * currentL1 (G.shiftPair p) x b) =
      (∫ x, t x * currentL1 p x b) + ∫ x, (t x * G.gradient b x) * densityL1 p x := by
  have h₁ : Integrable (fun x => t x * currentL1 p x b) volume :=
    (current_component_integrable p b).bdd_mul ht (ae_of_all _ hc)
  have h₂ : Integrable (fun x => (t x * G.gradient b x) * densityL1 p x) volume := by
    simpa only [mul_assoc] using
      (memLp_one_iff_integrable.mp (G.gradient_density_memLp_one p b)).bdd_mul
        ht (ae_of_all _ hc)
  rw [← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards [G.currentL1_shiftPair p] with x hx
  rw [hx, PiLp.add_apply, PiLp.smul_apply, gradientVector_apply, smul_eq_mul]
  ring

theorem energyShift_neg_shiftPair (p : Pair) :
    G.neg.energyShift (G.shiftPair p) = -G.energyShift p := by
  have hcurrent (a : Fin 3) :
      (∫ x, G.neg.gradient a x * currentL1 (G.shiftPair p) x a) =
        -(∫ x, G.gradient a x * currentL1 p x a) -
          ∫ x, G.gradient a x ^ 2 * densityL1 p x := by
    calc
      _ = ∫ x, -(G.gradient a x * currentL1 p x a) -
          G.gradient a x ^ 2 * densityL1 p x := by
        apply integral_congr_ae
        filter_upwards [G.currentL1_shiftPair p] with x hx
        rw [hx, PiLp.add_apply, PiLp.smul_apply, gradientVector_apply, smul_eq_mul]
        change -G.gradient a x * _ = _
        ring
      _ = _ := (integral_sub (G.gradient_current_integrable p a).neg
          (G.gradient_square_density_integrable p a)).trans
        (congrArg (fun r : ℝ => r - ∫ x, G.gradient a x ^ 2 * densityL1 p x)
          (integral_neg (fun x => G.gradient a x * currentL1 p x a)))
  have hnorm :
      (∫ x, (∑ a, G.neg.gradient a x ^ 2) * densityL1 (G.shiftPair p) x) =
        ∑ a, ∫ x, G.gradient a x ^ 2 * densityL1 p x := by
    rw [G.densityL1_shiftPair]
    simp only [neg, Pi.neg_apply, neg_sq, Finset.sum_mul]
    exact integral_finsetSum _ (fun a _ => G.gradient_square_density_integrable p a)
  have hnorm' : (∫ x, (∑ a, G.gradient a x ^ 2) * densityL1 p x) =
      ∑ a, ∫ x, G.gradient a x ^ 2 * densityL1 p x := by
    simp only [Finset.sum_mul]
    exact integral_finsetSum _ (fun a _ => G.gradient_square_density_integrable p a)
  simp only [energyShift, hcurrent, hnorm, hnorm', Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

end WeakSpatialGauge

end GptLean.TransformationsGauge
