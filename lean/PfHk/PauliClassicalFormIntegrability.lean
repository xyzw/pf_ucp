import PfHk.PauliClassicalCurlForm
import PfHk.CoordinateComparisonSpectral

/-! The global classical magnetic pairing is an integrable form on every
reference vector. Its estimate uses only form-domain coordinate Bessel
regularity, and does not require an L2 magnetic source. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliClassicalFormIntegrability

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.CoordinateSobolev PfHk.PauliClassicalCurlForm PfHk.PhysicalOperatorDomain

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

private theorem exponent_bounds {p : ℝ} (hp : 2 < p) :
    0 ≤ 3 / (2 * p) ∧ 3 / (2 * p) ≤ 1 := by
  have hp0 : 0 < p := by linarith only [hp]
  refine ⟨div_nonneg (by norm_num) (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * p)).mpr
  linarith only [hp]

private theorem product_bound {K a b c d : ℝ} (hK : 0 ≤ K)
    (ha : a ≤ c) (hb : b ≤ d) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    K * a * b ≤ K * c * d :=
  mul_le_mul (mul_le_mul_of_nonneg_left ha hK) hb hb0 (mul_nonneg hK hc0)

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion weightedInner pairing BesselPair

variable (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)

include S spectral joint

theorem classical_pairing_integrable_bound {p : ℝ} (hp : 2 < p)
    (n : Fin N) (b : PhysicalSourceCoordinates.Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal p) volume)
    (z u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (weightedInner (coordinateCoefficient n b)
      (inclusion (Fin N × Fin 3) (fun _ => 0) z)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)) volume ∧
    ‖pairing n b (inclusion (Fin N × Fin 3) (fun _ => 0) z)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)‖ ≤
      S.constant (2 * p) ^ 2 * (eLpNorm b (ENNReal.ofReal p) volume).toReal *
        ‖spectral.root z‖ * ‖spectral.root u‖ := by
  have hs := exponent_bounds hp
  have hexz := joint.form_value n (3 / (2 * p)) hs.1 hs.2 z
  have hexu := joint.form_value n (3 / (2 * p)) hs.1 hs.2 u
  let zB := Classical.choose hexz
  let uB := Classical.choose hexu
  have hzB := (Classical.choose_spec hexz).1
  have hz := (Classical.choose_spec hexz).2
  have huB := (Classical.choose_spec hexu).1
  have hu := (Classical.choose_spec hexu).2
  have h := coordinate_bound S hp n b hb
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) zB uB hzB huB
  refine ⟨h.1, h.2.trans ?_⟩
  have hK : 0 ≤ S.constant (2 * p) ^ 2 * (eLpNorm b (ENNReal.ofReal p) volume).toReal :=
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  exact product_bound hK hz hu (norm_nonneg uB) (norm_nonneg (spectral.root z))

theorem classical_pairing_integrable {p : ℝ} (hp : 2 < p)
    (n : Fin N) (b : PhysicalSourceCoordinates.Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal p) volume)
    (z u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (weightedInner (coordinateCoefficient n b)
      (inclusion (Fin N × Fin 3) (fun _ => 0) z)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u)) volume :=
  (classical_pairing_integrable_bound S spectral joint hp n b hb z u).1

end PfHk.PauliClassicalFormIntegrability

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
