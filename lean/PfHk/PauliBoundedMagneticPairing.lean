import PfHk.PauliMagnetizationDistribution
import PfHk.PauliExternalEnergyLp

/-! Integration of the Pauli magnetization current against bounded smooth
vector coefficients. This is the global H1 identity used at zero coupling. -/

noncomputable section
namespace PfHk.PauliBoundedMagneticPairing

open MeasureTheory GptLean GptLean.ElectronicH1Complex
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.PauliCurrentCorrection
  PfHk.PauliMagnetizationDistribution
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 150000

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

abbrev Index := Fin N × Fin 3
abbrev Components := SpinIndex N → ComplexH1 H (Index (N := N))

def orbital (u : Components (H := H) (N := N)) (n : Fin N) (a : Fin 3)
    (X : EuclideanSpace ℝ (Index (N := N))) : ℝ :=
  orbitalCurrent (fun s => value (u s) X)
    (fun b s => (-Complex.I) • derivative (n,b) (u s) X) a

def current (u : Components (H := H) (N := N)) (n : Fin N) (a : Fin 3)
    (X : EuclideanSpace ℝ (Index (N := N))) : ℝ :=
  PauliCurrentAlgebra.current n (fun s => value (u s) X)
    (fun b s => (-Complex.I) • derivative (n,b) (u s) X) a

theorem orbital_integrable (u : Components (H := H) (N := N))
    (n : Fin N) (a : Fin 3) : Integrable (orbital u n a) volume := by
  have h := (integrable_finsetSum Finset.univ fun s _ =>
    L2.integrable_inner (𝕜 := ℂ) (value (u s)) (derivative (n,a) (u s))).im
  apply h.congr
  exact Filter.Eventually.of_forall fun X => by
    change (∑ s, inner ℂ (value (u s) X) (derivative (n,a) (u s) X)).im = _
    simp only [orbital, orbitalCurrent, inner_smul_right, Complex.mul_re,
      Complex.neg_re, Complex.I_re, zero_mul, Complex.I_im, neg_mul, one_mul,
      zero_sub, neg_neg, Complex.re_sum, Complex.im_sum]

theorem weighted_integrable (a : SmoothMultiplier (Index (N := N)))
    (g : EuclideanSpace ℝ (Index (N := N)) → ℝ) (hg : Integrable g volume) :
    Integrable (fun X => a.weight X * g X) volume :=
  hg.bdd_mul a.smooth.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => by simpa only [Real.norm_eq_abs] using a.bounded X)

theorem point_current (u : Components (H := H) (N := N)) (n : Fin N)
    (a : Fin 3) (X : EuclideanSpace ℝ (Index (N := N))) :
    current u n a X = orbital u n a X + (1 / 2 : ℝ) *
      ![weakGradient n u (n,1) 2 X - weakGradient n u (n,2) 1 X,
        weakGradient n u (n,2) 0 X - weakGradient n u (n,0) 2 X,
        weakGradient n u (n,0) 1 X - weakGradient n u (n,1) 0 X] a := by
  have h := current_correction n (fun s => value (u s) X) 0
    (fun b s => derivative (n,b) (u s) X) (fun _ _ => (0 : H))
    (by intro b k; simp [spinPair, sigmaFamily]) a
  have hd : PauliCurrentCorrection.covariantDerivative 0
      (fun b s => derivative (n,b) (u s) X) (fun _ _ => (0 : H)) =
      (fun b s => (-Complex.I) • derivative (n,b) (u s) X) := by
    funext b s
    simp [PauliCurrentCorrection.covariantDerivative]
  rw [hd] at h
  simpa only [current, orbital, magnetizationCurl, magnetizationDerivative,
    weakGradient, PauliMagnetizationLp.pointPair] using h

private theorem split_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g h : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, f x + (1 / 2 : ℝ) * (g x - h x) ∂μ) =
      (∫ x, f x ∂μ) + (1 / 2 : ℝ) * ((∫ x, g x ∂μ) - ∫ x, h x ∂μ) := by
  have hd : Integrable (fun x => g x - h x) μ := hg.sub hh
  have hm : Integrable (fun x => (1 / 2 : ℝ) * (g x - h x)) μ := hd.const_mul _
  exact (integral_add hf hm).trans
    (congrArg (fun r : ℝ => (∫ x, f x ∂μ) + r)
      ((integral_const_mul (1 / 2 : ℝ) (fun x => g x - h x)).trans
        (congrArg (fun r : ℝ => (1 / 2 : ℝ) * r) (integral_sub hg hh))))

/-- Each component of the magnetization current can be integrated by
parts against any bounded smooth multiplier with bounded derivatives. -/
theorem weighted_current (a : SmoothMultiplier (Index (N := N)))
    (u : Components (H := H) (N := N)) (n : Fin N) (j : Fin 3) :
    (∫ X, a.weight X * current u n j X) =
      (∫ X, a.weight X * orbital u n j X) + (1 / 2 : ℝ) *
        ![(∫ X, a.gradient (n,2) X * magnetization n u 1 X) -
            (∫ X, a.gradient (n,1) X * magnetization n u 2 X),
          (∫ X, a.gradient (n,0) X * magnetization n u 2 X) -
            (∫ X, a.gradient (n,2) X * magnetization n u 0 X),
          (∫ X, a.gradient (n,1) X * magnetization n u 0 X) -
            (∫ X, a.gradient (n,0) X * magnetization n u 1 X)] j := by
  have ho := weighted_integrable a _ (orbital_integrable u n j)
  have hg (b k : Fin 3) := weighted_integrable a _ (weakGradient_integrable n u (n,b) k)
  have hsplit (b k c l : Fin 3) :
      (∫ X, a.weight X * (orbital u n j X + (1 / 2 : ℝ) *
        (weakGradient n u (n,b) k X - weakGradient n u (n,c) l X))) =
      (∫ X, a.weight X * orbital u n j X) + (1 / 2 : ℝ) *
        ((∫ X, a.gradient (n,c) X * magnetization n u l X) -
          (∫ X, a.gradient (n,b) X * magnetization n u k X)) := by
    have he := split_integral
      (fun X => a.weight X * orbital u n j X)
      (fun X => a.weight X * weakGradient n u (n,b) k X)
      (fun X => a.weight X * weakGradient n u (n,c) l X) ho (hg b k) (hg c l)
    have hb := weak_derivative_multiplier a n u (n,b) k
    have hc := weak_derivative_multiplier a n u (n,c) l
    calc
      _ = (∫ X, a.weight X * orbital u n j X + (1 / 2 : ℝ) *
          (a.weight X * weakGradient n u (n,b) k X -
            a.weight X * weakGradient n u (n,c) l X)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun X => by ring
      _ = _ := by rw [he]; linarith
  simp_rw [point_current]
  fin_cases j <;> exact hsplit _ _ _ _

end PfHk.PauliBoundedMagneticPairing
