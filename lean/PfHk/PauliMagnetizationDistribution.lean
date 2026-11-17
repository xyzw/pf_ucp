import PfHk.PauliMagnetizationLp
import PfHk.SmoothCutoffBounds

/-! The spin magnetization and its actual weak derivative are integrable.
The identity is proved for all compact smooth scalar tests, so the curl
used in the Pauli current is a distributional curl. -/

noncomputable section
namespace PfHk.PauliMagnetizationDistribution

open MeasureTheory GptLean GptLean.ElectronicH1Complex
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliCurrentCorrection
  PfHk.PauliMagnetizationLp
open scoped ContDiff

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 60000

attribute [local irreducible] ElectronicH1Complex.complexWeakGraph
  ElectronicH1Complex.value ElectronicH1Complex.derivative

variable {N : ℕ} {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [DecidableEq I]

def magnetization (n : Fin N) (u : SpinIndex N → ComplexH1 H I) (k : Fin 3)
    (X : EuclideanSpace ℝ I) : ℝ :=
  (pointPair n (fun s => value (E := H) (I := I) (u s)) (fun s => value (E := H) (I := I) (u s)) k X).re

def weakGradient (n : Fin N) (u : SpinIndex N → ComplexH1 H I) (i : I) (k : Fin 3)
    (X : EuclideanSpace ℝ I) : ℝ :=
  2 * (pointPair n (fun s => value (E := H) (I := I) (u s)) (fun s => derivative (E := H) (I := I) i (u s)) k X).re

theorem magnetization_integrable (n : Fin N) (u : SpinIndex N → ComplexH1 H I)
    (k : Fin 3) : Integrable (magnetization n u k) volume :=
  (pair_integrable n (fun s => value (E := H) (I := I) (u s)) (fun s => value (E := H) (I := I) (u s)) k).re

theorem weakGradient_integrable (n : Fin N) (u : SpinIndex N → ComplexH1 H I)
    (i : I) (k : Fin 3) : Integrable (weakGradient n u i k) volume :=
  ((pair_integrable n (fun s => value (E := H) (I := I) (u s)) (fun s => derivative (E := H) (I := I) i (u s)) k).re).const_mul 2

theorem weak_derivative_multiplier (a : SmoothMultiplier I) (n : Fin N)
    (u : SpinIndex N → ComplexH1 H I) (i : I) (k : Fin 3) :
    (∫ X, a.gradient i X * magnetization n u k X) =
      -(∫ X, a.weight X * weakGradient n u i k X) := by
  let v := fun s => value (E := H) (I := I) (u s)
  let d := fun s => derivative (E := H) (I := I) i (u s)
  have hleft := weighted_pair_integral (a.gradient i)
    (a.gradient_continuous i).aestronglyMeasurable a.derivativeBound
    (Filter.Eventually.of_forall (a.derivative_bounded i)) n v v k
  have hright := weighted_pair_integral a.weight a.smooth.continuous.aestronglyMeasurable
    a.bound (Filter.Eventually.of_forall a.bounded) n d v k
  have hswap := PauliMagnetizationWeak.spinPair_re_swap n
    v (fun s => a.multiplier (d s)) k
  have hi : (∫ X, a.weight X * weakGradient n u i k X) =
      2 * ∫ X, a.weight X * (pointPair n d v k X).re := by
    calc
      _ = ∫ X, 2 * (a.weight X * (pointPair n d v k X).re) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun X => by
          change a.weight X *
            (2 * (spinPair n (fun s => v s X) (fun s => d s X) k).re) =
              2 * (a.weight X * (spinPair n (fun s => d s X) (fun s => v s X) k).re)
          rw [PauliMagnetizationWeak.spinPair_re_swap n
            (fun s => v s X) (fun s => d s X) k]
          ring
      _ = _ := integral_const_mul _ _
  have hp := PauliMagnetizationWeak.weighted_product_rule a n k u i
  change (∫ X, a.gradient i X * (pointPair n v v k X).re) = _
  rw [← hleft, hi, ← hright]
  change (spinPair n (fun s => a.derivativeMultiplier i (v s)) v k).re =
    -(2 * (spinPair n (fun s => a.multiplier (d s)) v k).re)
  rw [hp, hswap]
  ring

theorem weak_derivative (n : Fin N) (u : SpinIndex N → ComplexH1 H I)
    (i : I) (k : Fin 3) (η : EuclideanSpace ℝ I → ℝ)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    (∫ X, fderiv ℝ η X (EuclideanSpace.single i 1) * magnetization n u k X) =
      -(∫ X, η X * weakGradient n u i k X) := by
  obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
  obtain ⟨D, hD⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  let a : SmoothMultiplier I := {
    weight := η
    smooth := hη
    bound := B
    bounded := fun X => by simpa only [Real.norm_eq_abs] using hB X
    derivativeBound := D
    derivative_bounded := fun j X => by
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
        (fderiv ℝ η X).le_of_opNorm_le (hD X) (EuclideanSpace.single j 1) }
  exact weak_derivative_multiplier a n u i k

end PfHk.PauliMagnetizationDistribution
