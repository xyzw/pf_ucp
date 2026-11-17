import PfHk.PauliMagnetizationDistribution
import GptLean.TransformationsGaugePair
import GptLean.PhysicalSourceCoordinates
import GptLean.PhysicalSourcePair

/-! One-body spin magnetization is the sum of the electronic marginals.
Its weak derivatives are obtained from bounded lifted tests and Fubini,
without differentiating arbitrary representatives of marginal functions. -/

noncomputable section
namespace PfHk.PauliMagnetizationMarginal

open MeasureTheory GptLean GptLean.ElectronicH1Complex GptLean.ElectronicH1Multiplier
  GptLean.PhysicalSourceCoordinates PfHk.PauliSpin
open scoped ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

variable {N : ℕ}

theorem lifted_derivative (a : SmoothMultiplier (Fin 3)) (n : Fin N)
    (q : Fin N × Fin 3) (X : Configuration N) :
    fderiv ℝ (fun Y => a.weight (SymmetricLift.particle Y n)) X (EuclideanSpace.single q 1) =
      if n = q.1 then a.gradient q.2 (SymmetricLift.particle X n) else 0 := by
  have h := ((a.smooth.differentiable (by simp) (SymmetricLift.particle X n)).hasFDerivAt).comp X
    (TransformationsGauge.SpatialGauge.particleCLM n).hasFDerivAt
  have h' : HasFDerivAt (fun Y => a.weight (SymmetricLift.particle Y n))
      ((fderiv ℝ a.weight (SymmetricLift.particle X n)).comp
        (TransformationsGauge.SpatialGauge.particleCLM n)) X := by
    simpa only [Function.comp_def, TransformationsGauge.SpatialGauge.particleCLM_apply] using h
  rw [h'.fderiv, ContinuousLinearMap.comp_apply,
    TransformationsGauge.SpatialGauge.particleCLM_apply,
    TransformationsGauge.SpatialGauge.particle_single]
  split_ifs <;> simp only [SmoothMultiplier.gradient, map_zero]

def lift (a : SmoothMultiplier (Fin 3)) (n : Fin N) : SmoothMultiplier (Fin N × Fin 3) where
  weight X := a.weight (SymmetricLift.particle X n)
  smooth := a.smooth.comp (TransformationsGauge.SpatialGauge.particleCLM n).contDiff
  bound := a.bound
  bounded X := a.bounded _
  derivativeBound := |a.derivativeBound|
  derivative_bounded q X := by
    rw [lifted_derivative]
    split_ifs
    · exact (a.derivative_bounded q.2 _).trans (le_abs_self _)
    · exact (abs_zero.le).trans (abs_nonneg _)

theorem lift_weight (a : SmoothMultiplier (Fin 3)) (n : Fin N) (X : Configuration N) :
    (lift a n).weight X = a.weight (SymmetricLift.particle X n) := rfl

theorem lift_gradient (a : SmoothMultiplier (Fin 3)) (n : Fin N) (b : Fin 3)
    (X : Configuration N) :
    (lift a n).gradient (n,b) X = a.gradient b (SymmetricLift.particle X n) := by
  exact (lifted_derivative a n (n,b) X).trans (by simp)

def marginal (n : Fin N) (f : Configuration N → ℝ) (x : Position) : ℝ :=
  ∫ y, f ((split n).symm (x,y))

theorem marginal_integrable (n : Fin N) (f : Configuration N → ℝ)
    (hf : Integrable f volume) : Integrable (marginal n f) volume :=
  ((split_symm_measurePreserving n).integrable_comp_of_integrable hf).integral_prod_left

theorem tested_marginal (n : Fin N) (f : Configuration N → ℝ)
    (hf : Integrable f volume) (a : Position → ℝ) (ha : Continuous a)
    (B : ℝ) (hB : ∀ x, |a x| ≤ B) :
    (∫ x, a x * marginal n f x) =
      ∫ X, a (SymmetricLift.particle X n) * f X := by
  have hw : Integrable (fun X => a (SymmetricLift.particle X n) * f X) volume :=
    hf.bdd_mul (ha.comp (TransformationsGauge.SpatialGauge.particleCLM n).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using hB _)
  have he : (fun p : Position × Spectator n =>
      a p.1 * f ((split n).symm p)) =
      (fun X => a (SymmetricLift.particle X n) * f X) ∘ (split n).symm := by
    funext p
    rw [Function.comp_apply, ← PhysicalSourcePair.split_fst_eq_particle,
      (split n).apply_symm_apply]
  have hi : Integrable (fun p : Position × Spectator n =>
      a p.1 * f ((split n).symm p)) (volume.prod volume) :=
    (congrArg (fun g : Position × Spectator n → ℝ => Integrable g (volume.prod volume)) he).mpr
      ((split_symm_measurePreserving n).integrable_comp_of_integrable hw)
  calc
    _ = ∫ x, ∫ y, a x * f ((split n).symm (x,y)) := by
      simp only [marginal, integral_const_mul]
    _ = ∫ p : Position × Spectator n, a p.1 * f ((split n).symm p) ∂volume.prod volume :=
      (integral_prod _ hi).symm
    _ = _ := (congrArg (fun g : Position × Spectator n → ℝ => ∫ p, g p ∂volume.prod volume) he).trans
      ((split_symm_measurePreserving n).integral_comp
        (split n).symm.toHomeomorph.measurableEmbedding
        (fun X : Configuration N => a (SymmetricLift.particle X n) * f X))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def magnetization (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (k : Fin 3)
    (x : Position) : ℝ :=
  ∑ n, marginal n (PauliMagnetizationDistribution.magnetization n u k) x

def weakGradient (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (b k : Fin 3)
    (x : Position) : ℝ :=
  ∑ n, marginal n (PauliMagnetizationDistribution.weakGradient n u (n,b) k) x

theorem magnetization_integrable (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3))
    (k : Fin 3) : Integrable (magnetization u k) volume :=
  integrable_finsetSum Finset.univ (fun n _ => marginal_integrable n _
    (PauliMagnetizationDistribution.magnetization_integrable n u k))

theorem weakGradient_integrable (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3))
    (b k : Fin 3) : Integrable (weakGradient u b k) volume :=
  integrable_finsetSum Finset.univ (fun n _ => marginal_integrable n _
    (PauliMagnetizationDistribution.weakGradient_integrable n u (n,b) k))

theorem weak_derivative_multiplier (a : SmoothMultiplier (Fin 3))
    (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (b k : Fin 3) :
    (∫ x, a.gradient b x * magnetization u k x) =
      -(∫ x, a.weight x * weakGradient u b k x) := by
  have hm (n : Fin N) := PauliMagnetizationDistribution.magnetization_integrable n u k
  have hd (n : Fin N) := PauliMagnetizationDistribution.weakGradient_integrable n u (n,b) k
  have hmi (n : Fin N) : Integrable (fun x => a.gradient b x * marginal n
      (PauliMagnetizationDistribution.magnetization n u k) x) volume :=
    (marginal_integrable n _ (hm n)).bdd_mul (a.gradient_continuous b).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, SmoothMultiplier.gradient] using a.derivative_bounded b x)
  have hdi (n : Fin N) : Integrable (fun x => a.weight x * marginal n
      (PauliMagnetizationDistribution.weakGradient n u (n,b) k) x) volume :=
    (marginal_integrable n _ (hd n)).bdd_mul a.smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using a.bounded x)
  simp only [magnetization, weakGradient, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun n _ => hmi n), integral_finsetSum Finset.univ (fun n _ => hdi n),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [tested_marginal n _ (hm n) (a.gradient b) (a.gradient_continuous b)
    a.derivativeBound (a.derivative_bounded b),
    tested_marginal n _ (hd n) a.weight a.smooth.continuous a.bound a.bounded]
  have h := PauliMagnetizationDistribution.weak_derivative_multiplier (lift a n) n u (n,b) k
  simpa only [lift_gradient, lift_weight] using h

theorem weak_derivative (u : SpinIndex N → ComplexH1 H (Fin N × Fin 3)) (b k : Fin 3)
    (η : Position → ℝ) (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    (∫ x, fderiv ℝ η x (EuclideanSpace.single b 1) * magnetization u k x) =
      -(∫ x, η x * weakGradient u b k x) := by
  obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
  obtain ⟨D, hD⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  let a : SmoothMultiplier (Fin 3) := {
    weight := η
    smooth := hη
    bound := B
    bounded := fun x => by simpa only [Real.norm_eq_abs] using hB x
    derivativeBound := D
    derivative_bounded := fun j x => by
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
        (fderiv ℝ η x).le_of_opNorm_le (hD x) (EuclideanSpace.single j 1) }
  exact weak_derivative_multiplier a u b k

end PfHk.PauliMagnetizationMarginal
