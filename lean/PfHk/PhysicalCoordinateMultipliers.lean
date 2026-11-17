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
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 10000

attribute [local irreducible] PhysicalPFReference.inclusion
  PhysicalPFReference.ordinary PhysicalPFReference.radiation
  PhysicalPFReference.field PhysicalPFReference.covariant

local instance endpointPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

variable {N : ℕ}

theorem sum_hasMultiplier {J : Type*} (s : Finset J)
    (b : J → Configuration N → ℝ) (u : WaveSpace (Fin N × Fin 3))
    (hb : ∀ j ∈ s, HasMultiplier (b j) u) :
    HasMultiplier (fun x => ∑ j ∈ s, b j x) u := by
  exact ScalarCoefficientNormAlgebra.sum_multiplier (H := PhotonFock) s b u hb

theorem square_memLp_three {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {b : X → ℝ} (hb : MemLp b 6 μ) : MemLp (fun x => b x ^ 2) 3 μ := by
  let : ENNReal.HolderTriple 6 6 3 :=
    ENNReal.HolderTriple.of_toReal ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [pow_two] using (show MemLp (fun x => b x * b x) 3 μ from hb.mul' hb)

theorem square_lpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (b : X → ℝ) :
    (eLpNorm (fun x => b x ^ 2) 3 μ).toReal = (eLpNorm b 6 μ).toReal ^ 2 := by
  have he := eLpNorm_norm_rpow (μ := μ) (p := (3 : ℝ≥0∞)) b
    (by norm_num : (0 : ℝ) < 2)
  norm_num [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.rpow_two] at he
  rw [he, ENNReal.toReal_pow]

theorem bounded_multiplier (b : Configuration N → ℝ) (hb : MemLp b ∞ volume)
    (u : WaveSpace (Fin N × Fin 3)) :
    ∃ hm : HasMultiplier b u,
      ‖roughMultiply b u hm‖ ^ 2 ≤ (eLpNorm b ∞ volume).toReal ^ 2 * ‖u‖ ^ 2 := by
  exact ScalarCoefficientNormAlgebra.bounded_multiplier (H := PhotonFock) b hb u

def coefficientNormSq (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : ℝ :=
  (S.constant q) ^ 2 * (eLpNorm b (ENNReal.ofReal q) volume).toReal ^ 2

theorem coefficientNormSq_nonneg (S : CoordinateSobolev.Data PhotonFock N)
    (q : ℝ) (b : Position → ℝ) : 0 ≤ coefficientNormSq S q b := by
  unfold coefficientNormSq
  positivity

theorem coefficientNormSq_square (S : CoordinateSobolev.Data PhotonFock N)
    (b : Position → ℝ) : coefficientNormSq S 3 (fun x => b x ^ 2) =
      (S.constant 3) ^ 2 * (eLpNorm b 6 volume).toReal ^ 4 := by
  norm_num only [coefficientNormSq, ENNReal.ofReal_ofNat]
  rw [square_lpNorm]
  ring

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
  have hex := coordinate_multiplier S hq n b hb w v hv
  let hm := Classical.choose hex
  have hn := Classical.choose_spec hex
  refine ⟨hm, ?_⟩
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hvn
    (mul_nonneg (S.constant_nonneg q) ENNReal.toReal_nonneg))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn' 2
  exact hs.trans_eq ((mul_pow _ _ 2).trans
    (congrArg (fun a : ℝ => a * ‖fractionalVector spectral t u hu‖ ^ 2) (mul_pow _ _ 2)))

/-- Scalar Lq coefficients multiply graph-domain vectors at the exact
fractional order `3/q`, for every `q>2`. -/
theorem scalar_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {q : ℝ} (hq : 2 < q) (n : Fin N) (b : Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b) (inclusion (Fin N × Fin 3) (fun _ => 0) u),
      ‖roughMultiply (coordinateCoefficient n b) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hm‖ ^ 2 ≤
        coefficientNormSq S q b * fractionalNormSq spectral (3 / q) u hu := by
  have hq0 : 0 < q := by linarith only [hq]
  have hs : 0 ≤ 3 / q := by positivity
  have hs2 : 3 / q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith only [hq])
  have hex := joint.value n (3 / q) (3 / q) hs le_rfl hs2 u hu
  let v : WaveSpace (Fin N × Fin 3) := Classical.choose hex
  have hv := (Classical.choose_spec hex).1
  have hvn := (Classical.choose_spec hex).2
  exact multiplier_of_bessel S spectral hq n b hb u hu _ v hv hvn

/-- The same argument on the comparison form domain. This gives actual
bounded multiplication for all reference vectors, without a graph witness. -/
theorem scalar_form_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    {q : ℝ} (hq : 3 ≤ q) (n : Fin N) (b : Position → ℝ)
    (hb : MemLp b (ENNReal.ofReal q) volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b) (inclusion (Fin N × Fin 3) (fun _ => 0) u),
      ‖roughMultiply (coordinateCoefficient n b) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hm‖ ≤
        S.constant q * (eLpNorm b (ENNReal.ofReal q) volume).toReal * ‖spectral.root u‖ := by
  have hq0 : 0 < q := by linarith only [hq]
  have hs : 0 ≤ 3 / q := by positivity
  have hs1 : 3 / q ≤ 1 := (div_le_iff₀ hq0).mpr (by linarith only [hq])
  have hex := joint.form_value n (3 / q) hs hs1 u
  let v : WaveSpace (Fin N × Fin 3) := Classical.choose hex
  have hv := (Classical.choose_spec hex).1
  have hvn := (Classical.choose_spec hex).2
  have hmul := coordinate_multiplier S (by linarith only [hq]) n b hb _ v hv
  let hm := Classical.choose hmul
  have hn := Classical.choose_spec hmul
  exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_left hvn
    (mul_nonneg (S.constant_nonneg q) ENNReal.toReal_nonneg))⟩

set_option maxHeartbeats 20000 in
/-- The magnetic first-order endpoint for each actual covariant coordinate. -/
theorem covariant_coordinate_multiplier (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (C : CanonicalSectorCCR photonMeasure)
    (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
    (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M)
    (e : ℝ) (n : Fin N) (i : Fin N × Fin 3) (b : Position → ℝ)
    (hb : MemLp b 6 volume)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ v, IsComparisonPair (fun _ => 0) u v) :
    ∃ hm : HasMultiplier (coordinateCoefficient n b)
      (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u),
      ‖roughMultiply (coordinateCoefficient n b)
        (covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hbound e i u) hm‖ ^ 2 ≤
      (2 + 20 * e ^ 2 * (max M 0) ^ 2) * coefficientNormSq S 6 b *
        fractionalNormSq spectral (3 / 2) u hu := by
  have hb' : MemLp b (ENNReal.ofReal (6 : ℝ)) volume := by simpa using hb
  have hexP := joint.ordinary n i u hu
  let vP : WaveSpace (Fin N × Fin 3) := Classical.choose hexP
  have hP := (Classical.choose_spec hexP).1
  have hnP := (Classical.choose_spec hexP).2
  have hexR := joint.radiation n u hu
  let vR : WaveSpace (Fin N × Fin 3) := Classical.choose hexR
  have hR := (Classical.choose_spec hexR).1
  have hnR := (Classical.choose_spec hexR).2
  have hexJ := joint.value n (1 / 2) (3 / 2)
    (by norm_num) (by norm_num) (by norm_num) u hu
  let vJ : WaveSpace (Fin N × Fin 3) := Classical.choose hexJ
  have hJ := (Classical.choose_spec hexJ).1
  have hnJ := (Classical.choose_spec hexJ).2
  have hP' := ScalarCoefficientNormAlgebra.bessel_half_to_sixth (H := PhotonFock) n
    (ordinary (Fin N × Fin 3) (fun _ => 0) i u) vP hP
  have hR' := ScalarCoefficientNormAlgebra.bessel_half_to_sixth (H := PhotonFock) n
    (radiation (Fin N × Fin 3) (fun _ => 0) u) vR hR
  have hJ' := ScalarCoefficientNormAlgebra.bessel_half_to_sixth (H := PhotonFock) n
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) vJ hJ
  have hmulP := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vP hP' hnP
  let hmP := Classical.choose hmulP
  have hbP := Classical.choose_spec hmulP
  have hmulR := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vR hR' hnR
  let hmR := Classical.choose hmulR
  have hbR := Classical.choose_spec hmulR
  have hmulJ := multiplier_of_bessel S spectral (by norm_num : (2 : ℝ) < 6)
    n b hb' u hu _ vJ hJ' hnJ
  let hmJ := Classical.choose hmulJ
  have hbJ := Classical.choose_spec hmulJ
  have hmul := covariant_multiplier (fun _ => 0) C κ hκ M hbound
    (coordinateCoefficient n b) (coordinateCoefficient_measurable n hb.aestronglyMeasurable)
    e u i hmP hmR hmJ
  let hm := Classical.choose hmul
  have hn := Classical.choose_spec hmul
  exact ⟨hm, hn.trans (ScalarCoefficientNormAlgebra.three_endpoint_bound _ _ _
    (coefficientNormSq S 6 b) (fractionalNormSq spectral (3 / 2) u hu) e (max M 0)
    hbP hbR hbJ)⟩

end PfHk.PhysicalCoordinateMultipliers
