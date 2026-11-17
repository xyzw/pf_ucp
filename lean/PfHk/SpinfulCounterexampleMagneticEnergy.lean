import PfHk.PauliBoundedMagneticPairing
import PfHk.SpinfulCounterexampleMultiplier
import PfHk.SpinfulCounterexampleSpin
import PfHk.SpinfulCounterexampleSpectral
import PfHk.PauliMagnetizationMarginal

/-! The integrated magnetization term for the cylindrical field. The
identity holds on every photon-valued H1 spinor. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.SpinfulCounterexampleMagneticEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.ElectronicH1Complex
  GptLean.ElectronicH1Multiplier PfHk.PauliSpin PfHk.SpinfulCounterexampleState
  PfHk.SpinfulCounterexampleSpectral PfHk.PauliMagnetizationDistribution
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [local irreducible] ElectronicH1Complex.value ElectronicH1Complex.derivative

abbrev Components := SpinIndex 1 → Electronic
abbrev Space := CounterexampleSpectral.Space

private def coefficient (j : Fin 3) : SmoothMultiplier (Fin 1 × Fin 3) :=
  PauliMagnetizationMarginal.lift (SpinfulCounterexampleField.fieldSmoothMultiplier j) 0

private theorem coefficient_weight (j : Fin 3) (X : Space) :
    (coefficient j).weight X = SpinfulCounterexampleField.field (position X) j := rfl

private theorem coefficient_gradient_two (j : Fin 3) (X : Space) :
    (coefficient j).gradient (0,2) X = 0 :=
  (PauliMagnetizationMarginal.lift_gradient _ _ _ _).trans
    (SpinfulCounterexampleField.field_coordinate_derivative_two j _)

private theorem coefficient_curl (X : Space) :
    (coefficient 1).gradient (0,0) X - (coefficient 0).gradient (0,1) X =
      2 * SpinfulCounterexampleField.weight (position X) ^ 2 := by
  simp only [coefficient, PauliMagnetizationMarginal.lift_gradient]
  exact SpinfulCounterexampleField.field_planar_curl _

private theorem gradient_integrable (j b k : Fin 3) (u : Components) :
    Integrable (fun X => (coefficient j).gradient (0,b) X * magnetization 0 u k X) volume := by
  have hb (X : Space) : ‖(coefficient j).gradient (0,b) X‖ ≤ (coefficient j).derivativeBound := by
    rw [Real.norm_eq_abs]
    exact (coefficient j).derivative_bounded (0,b) X
  exact (magnetization_integrable 0 u k).bdd_mul
    ((coefficient j).gradient_continuous (0,b)).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

private theorem weighted_inner_integrable (u : Components) (j : Fin 3) (s : SpinIndex 1) :
    Integrable (fun X => SpinfulCounterexampleField.field (position X) j *
      (inner ℂ (value (u s) X) ((-Complex.I) • derivative (0,j) (u s) X)).re) volume := by
  have hi := PauliBoundedMagneticPairing.weighted_integrable (coefficient j) _
    (L2.integrable_inner (𝕜 := ℂ) (value (u s)) (derivative (0,j) (u s))).im
  refine hi.congr (Filter.Eventually.of_forall fun X => ?_)
  simp only [coefficient_weight, inner_smul_right, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, RCLike.im_to_complex]
  ring

/-- The generic orbital current at one point, written with the concrete
electronic coordinates. -/
private theorem orbital_point (u : Components) (j : Fin 3) (X : Space) :
    PauliBoundedMagneticPairing.orbital u 0 j X =
      (inner ℂ (value (u up) X) ((-Complex.I) • derivative (0,j) (u up) X)).re +
      (inner ℂ (value (u down) X) ((-Complex.I) • derivative (0,j) (u down) X)).re :=
  (congrArg Complex.re (sum_spin (fun s =>
    inner ℂ (value (u s) X) ((-Complex.I) • derivative (0,j) (u s) X)))).trans
    (Complex.add_re _ _)

private theorem orbital_sum (u : Components) :
    (∑ j : Fin 3, ∫ X, SpinfulCounterexampleField.field (position X) j *
      PauliBoundedMagneticPairing.orbital u 0 j X) = rotationForm (u up) + rotationForm (u down) := by
  have hrow (j : Fin 3) :
      (∫ X, SpinfulCounterexampleField.field (position X) j *
        PauliBoundedMagneticPairing.orbital u 0 j X) =
      (∫ X, SpinfulCounterexampleField.field (position X) j *
        (inner ℂ (value (u up) X) ((-Complex.I) • derivative (0,j) (u up) X)).re) +
      ∫ X, SpinfulCounterexampleField.field (position X) j *
        (inner ℂ (value (u down) X) ((-Complex.I) • derivative (0,j) (u down) X)).re := by
    rw [← integral_add (weighted_inner_integrable u j up) (weighted_inner_integrable u j down)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [orbital_point, mul_add]
  rw [Finset.sum_congr rfl fun j _ => hrow j, Finset.sum_add_distrib]
  rfl

/-- The generic magnetization density at one point. -/
private theorem magnetization_point (u : Components) (X : Space) :
    magnetization 0 u 2 X = ‖value (u up) X‖ ^ 2 - ‖value (u down) X‖ ^ 2 :=
  spinPair_two_self_re (fun s => value (u s) X)

private theorem curl_point (g0 g1 w m a b : ℝ) (hg : g1 - g0 = 2 * w ^ 2) (hm : m = a - b) :
    g1 * m - g0 * m = 2 * (w ^ 2 * a - w ^ 2 * b) := by
  rw [← sub_mul, hg, hm]
  ring

private theorem magnetic_curl_integral (u : Components) :
    (∫ X, (coefficient 1).gradient (0,0) X * magnetization 0 u 2 X) -
      (∫ X, (coefficient 0).gradient (0,1) X * magnetization 0 u 2 X) =
      2 * (upWeight (u up) - upWeight (u down)) := by
  rw [← integral_sub (gradient_integrable 1 0 2 u) (gradient_integrable 0 1 2 u)]
  have hup := upWeight_integrable (u up)
  have hdown := upWeight_integrable (u down)
  calc
    _ = ∫ X, 2 * (SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value (u up) X‖ ^ 2 -
        SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value (u down) X‖ ^ 2) :=
      integral_congr_ae (Filter.Eventually.of_forall fun X =>
        curl_point _ _ _ _ _ _ (coefficient_curl X) (magnetization_point u X))
    _ = 2 * ((∫ X, SpinfulCounterexampleField.weight (position X) ^ 2 *
          ‖value (u up) X‖ ^ 2) -
        ∫ X, SpinfulCounterexampleField.weight (position X) ^ 2 * ‖value (u down) X‖ ^ 2) :=
      (integral_const_mul 2 _).trans (congrArg (fun r : ℝ => 2 * r) (integral_sub hup hdown))
    _ = _ := rfl

/-- The cylinder field couples to the orbital angular form and to the
spin-up minus spin-down Zeeman densities, with the exact coefficient. -/
theorem current_pairing (u : Components) :
    (∑ j : Fin 3, ∫ X, SpinfulCounterexampleField.field (position X) j *
      PauliBoundedMagneticPairing.current u 0 j X) =
      rotationForm (u up) + rotationForm (u down) + upWeight (u up) - upWeight (u down) := by
  have hz (X : Space) : SpinfulCounterexampleField.field (position X) 2 = 0 :=
    (SpinfulCounterexampleField.field_components _).2.2
  have h0 : (∫ X, SpinfulCounterexampleField.field (position X) 0 *
      PauliBoundedMagneticPairing.current u 0 0 X) =
      (∫ X, SpinfulCounterexampleField.field (position X) 0 *
        PauliBoundedMagneticPairing.orbital u 0 0 X) + (1 / 2 : ℝ) *
      ((∫ X, (coefficient 0).gradient (0,2) X * magnetization 0 u 1 X) -
        (∫ X, (coefficient 0).gradient (0,1) X * magnetization 0 u 2 X)) :=
    PauliBoundedMagneticPairing.weighted_current (coefficient 0) u 0 0
  have h1 : (∫ X, SpinfulCounterexampleField.field (position X) 1 *
      PauliBoundedMagneticPairing.current u 0 1 X) =
      (∫ X, SpinfulCounterexampleField.field (position X) 1 *
        PauliBoundedMagneticPairing.orbital u 0 1 X) + (1 / 2 : ℝ) *
      ((∫ X, (coefficient 1).gradient (0,0) X * magnetization 0 u 2 X) -
        (∫ X, (coefficient 1).gradient (0,2) X * magnetization 0 u 0 X)) :=
    PauliBoundedMagneticPairing.weighted_current (coefficient 1) u 0 1
  have hz0 : (∫ X, (coefficient 0).gradient (0,2) X * magnetization 0 u 1 X) = 0 := by
    simp only [coefficient_gradient_two, zero_mul, integral_zero]
  have hz1 : (∫ X, (coefficient 1).gradient (0,2) X * magnetization 0 u 0 X) = 0 := by
    simp only [coefficient_gradient_two, zero_mul, integral_zero]
  have h2 : (∫ X, SpinfulCounterexampleField.field (position X) 2 *
      PauliBoundedMagneticPairing.current u 0 2 X) = 0 := by
    simp only [hz, zero_mul, integral_zero]
  have ho : (∫ X, SpinfulCounterexampleField.field (position X) 0 *
        PauliBoundedMagneticPairing.orbital u 0 0 X) +
      (∫ X, SpinfulCounterexampleField.field (position X) 1 *
        PauliBoundedMagneticPairing.orbital u 0 1 X) =
      rotationForm (u up) + rotationForm (u down) := by
    have h := orbital_sum u
    rw [Fin.sum_univ_three] at h
    have h2o : (∫ X, SpinfulCounterexampleField.field (position X) 2 *
        PauliBoundedMagneticPairing.orbital u 0 2 X) = 0 := by
      simp only [hz, zero_mul, integral_zero]
    linarith only [h, h2o]
  have hc := magnetic_curl_integral u
  rw [Fin.sum_univ_three]
  linarith only [h0, h1, hz0, hz1, h2, ho, hc]

end PfHk.SpinfulCounterexampleMagneticEnergy
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
