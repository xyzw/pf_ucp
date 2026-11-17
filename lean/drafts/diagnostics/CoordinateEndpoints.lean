import PfHk.CoordinateMultiplication
import PfHk.CoordinateComparisonSpectral
import PfHk.PhysicalMultiplierField
import PfHk.ScalarCoefficientNormAlgebra

/-!
The physical endpoint multipliers are consequences of the ordinary
Hilbert-valued coordinate Sobolev embedding and commuting spectral calculus.
All products are actual L2 functions, represented by `roughMultiply_ae`.
The quantized-field contribution uses the proved pointwise creation and
annihilation estimate and requires no spatial derivative of the field.
-/

noncomputable section
namespace PfHk.PhysicalCoordinateMultipliers

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalOperatorDomain PfHk.PhysicalDyadicIntegralFractional
open PfHk.PhysicalLocalEnergy PfHk.CoordinateSobolev
open GptLean.PhysicalSourceCoordinates
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 5000

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation
  PhysicalPFReference.field PhysicalPFReference.covariant

variable {N : ℕ}

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START sum_hasMultiplier"
  out.flush

theorem sum_hasMultiplier {J : Type*} (s : Finset J)
    (b : J → Configuration N → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hb : ∀ j ∈ s, HasMultiplier (b j) u) :
    HasMultiplier (fun x => ∑ j ∈ s, b j x) u := by
  unfold HasMultiplier at hb ⊢
  simpa only [Finset.sum_smul] using memLp_finsetSum s hb

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START square_memLp_three"
  out.flush

theorem square_memLp_three {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {b : X → ℝ} (hb : MemLp b 6 μ) : MemLp (fun x => b x ^ 2) 3 μ := by
  let : ENNReal.HolderTriple 6 6 3 :=
    ENNReal.HolderTriple.of_toReal ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [pow_two] using (show MemLp (fun x => b x * b x) 3 μ from hb.mul' hb)

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START square_lpNorm"
  out.flush

theorem square_lpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (b : X → ℝ) :
    (eLpNorm (fun x => b x ^ 2) 3 μ).toReal = (eLpNorm b 6 μ).toReal ^ 2 := by
  have he := eLpNorm_norm_rpow (μ := μ) (p := (3 : ℝ≥0∞)) b
    (by norm_num : (0 : ℝ) < 2)
  norm_num [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.rpow_two] at he
  rw [he, ENNReal.toReal_pow]

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START bounded_multiplier"
  out.flush

theorem bounded_multiplier (b : Configuration N → ℝ) (hb : MemLp b ∞ volume)
    (u : WaveSpace (Fin N × Fin 3)) :
    ∃ hm : HasMultiplier b u,
      ‖roughMultiply b u hm‖ ^ 2 ≤ (eLpNorm b ∞ volume).toReal ^ 2 * ‖u‖ ^ 2 := by
  exact ScalarCoefficientNormAlgebra.bounded_multiplier (H := PhotonFock) b hb u

def coefficientNormSq (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : ℝ :=
  (S.constant q) ^ 2 * (eLpNorm b (ENNReal.ofReal q) volume).toReal ^ 2

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START coefficientNormSq_nonneg"
  out.flush

theorem coefficientNormSq_nonneg (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : 0 ≤ coefficientNormSq S q b := by
  unfold coefficientNormSq
  positivity

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START coefficientNormSq_square"
  out.flush

theorem coefficientNormSq_square (S : CoordinateSobolev.Data PhotonFock N)
    (b : Position → ℝ) : coefficientNormSq S 3 (fun x => b x ^ 2) =
      (S.constant 3) ^ 2 * (eLpNorm b 6 volume).toReal ^ 4 := by
  norm_num only [coefficientNormSq, ENNReal.ofReal_ofNat]
  rw [square_lpNorm]
  ring

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START multiplier_of_bessel"
  out.flush

theorem multiplier_of_bessel (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    {q t : ℝ} (hq : 2 < q) (n : Fin N) (b : Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v)
    (w v : WaveSpace (Fin N × Fin 3)) (hv : BesselPair (H := PhotonFock) n (3 / q) w v)
    (hvn : ‖v‖ ≤ ‖fractionalVector spectral t u hu‖) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b) w,
      ‖roughMultiply (coordinateCoefficient n b) w hm‖ ^ 2 ≤
        coefficientNormSq S q b * fractionalNormSq spectral t u hu := by
  obtain ⟨hm, hn⟩ := coordinate_multiplier S hq n b hb w v hv
  refine ⟨hm, ?_⟩
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hvn
    (mul_nonneg (S.constant_nonneg q) ENNReal.toReal_nonneg))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn' 2
  exact hs.trans_eq (by unfold coefficientNormSq fractionalNormSq; ring)

/-- Scalar Lq coefficients multiply graph-domain vectors at the exact
fractional order `3/q`, for every `q>2`. -/
run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START scalar_multiplier"
  out.flush

theorem scalar_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {q : ℝ} (hq : 2 < q) (n : Fin N) (b : Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b) (inclusion _ (fun _ => 0) u),
      ‖roughMultiply (coordinateCoefficient n b) (inclusion _ (fun _ => 0) u) hm‖ ^ 2 ≤
        coefficientNormSq S q b * fractionalNormSq spectral (3 / q) u hu := by
  have hq0 : 0 < q := by linarith only [hq]
  have hs : 0 ≤ 3 / q := by positivity
  have hs2 : 3 / q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith only [hq])
  obtain ⟨v, hv, hvn⟩ := joint.value n (3 / q) (3 / q) hs le_rfl hs2 u hu
  exact multiplier_of_bessel S spectral hq n b hb u hu _ v hv hvn

/-- The same argument on the comparison form domain. This gives actual
bounded multiplication for all reference vectors, without a graph witness. -/
run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START scalar_form_multiplier"
  out.flush

theorem scalar_form_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {q : ℝ} (hq : 3 ≤ q) (n : Fin N) (b : Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b) (inclusion _ (fun _ => 0) u),
      ‖roughMultiply (coordinateCoefficient n b) (inclusion _ (fun _ => 0) u) hm‖ ≤
        S.constant q * (eLpNorm b (ENNReal.ofReal q) volume).toReal * ‖spectral.root u‖ := by
  have hq0 : 0 < q := by linarith only [hq]
  have hs : 0 ≤ 3 / q := by positivity
  have hs1 : 3 / q ≤ 1 := (div_le_iff₀ hq0).mpr (by linarith only [hq])
  obtain ⟨v, hv, hvn⟩ := joint.form_value n (3 / q) hs hs1 u
  obtain ⟨hm, hn⟩ := coordinate_multiplier S (by linarith only [hq]) n b hb _ v hv
  exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_left hvn
    (mul_nonneg (S.constant_nonneg q) ENNReal.toReal_nonneg))⟩

/-- The magnetic first-order endpoint for each actual covariant coordinate. -/
run_cmd do
  let out ← IO.getStderr
  out.putStrLn "START covariant_coordinate_multiplier"
  out.flush

theorem covariant_coordinate_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
    (e : ℝ) (n : Fin N) (i : Fin N × Fin 3) (b : Position → ℝ)
    (hb : MemLp b 6 volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b)
      (covariant _ (fun _ => 0) C κ hκ M hbound e i u),
      ‖roughMultiply (coordinateCoefficient n b)
        (covariant _ (fun _ => 0) C κ hκ M hbound e i u) hm‖ ^ 2 ≤
      (2 + 20 * e ^ 2 * (max M 0) ^ 2) * coefficientNormSq S 6 b *
        fractionalNormSq spectral (3 / 2) u hu := by
  have hb' : MemLp b (ENNReal.ofReal (6 : ℝ)) volume := by simpa using hb
  obtain ⟨vP, hP, hnP⟩ := joint.ordinary n i u hu
  obtain ⟨vR, hR, hnR⟩ := joint.radiation n u hu
  obtain ⟨vJ, hJ, hnJ⟩ := joint.value n (1 / 2) (3 / 2)
    (by norm_num) (by norm_num) (by norm_num) u hu
  have hP' : BesselPair (H := PhotonFock) n (3 / 6) (ordinary _ (fun _ => 0) i u) vP := by
    norm_num at hP ⊢
    exact hP
  have hR' : BesselPair (H := PhotonFock) n (3 / 6) (radiation _ (fun _ => 0) u) vR := by
    norm_num at hR ⊢
    exact hR
  have hJ' : BesselPair (H := PhotonFock) n (3 / 6) (inclusion _ (fun _ => 0) u) vJ := by
    norm_num at hJ ⊢
    exact hJ
  obtain ⟨hmP, hbP⟩ := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vP hP' hnP
  obtain ⟨hmR, hbR⟩ := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vR hR' hnR
  obtain ⟨hmJ, hbJ⟩ := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vJ hJ' hnJ
  obtain ⟨hm, hn⟩ := covariant_multiplier (fun _ => 0) C κ hκ M hbound
    (coordinateCoefficient n b) (coordinateCoefficient_measurable n hb.aestronglyMeasurable)
    e u i hmP hmR hmJ
  refine ⟨hm, hn.trans ?_⟩
  calc
    _ ≤ 2 * (coefficientNormSq S 6 b * fractionalNormSq spectral (3 / 2) u hu) +
        16 * e ^ 2 * (max M 0) ^ 2 *
          (coefficientNormSq S 6 b * fractionalNormSq spectral (3 / 2) u hu) +
        4 * e ^ 2 * (max M 0) ^ 2 *
          (coefficientNormSq S 6 b * fractionalNormSq spectral (3 / 2) u hu) := by
      gcongr
    _ = _ := by ring

end PfHk.PhysicalCoordinateMultipliers
