import PfHk.PhysicalExternalTermsIdentity
import PfHk.PhysicalRelativeMultiplier

/-! Infinitesimal relative boundedness of the actual external perturbation,
derived term by term from coordinate Sobolev endpoints and spectral interpolation. -/

noncomputable section
namespace PfHk.PhysicalExternalRelativeBound

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.SymmetricLift PfHk.PhysicalLocalEnergy PfHk.PhysicalOperatorDomain
open PfHk.PhysicalExternalOperator PfHk.PhysicalExternalCoefficients
open PfHk.PhysicalExternalSource PfHk.PhysicalCoordinateMultipliers PfHk.CoordinateSobolev
open PfHk.PhysicalDyadicIntegralFractional PfHk.InfinitesimalBound
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant roughMultiply HasMultiplier perturbation total term
  PhysicalPFReference.referenceSubspace

variable {N : ℕ} {X : Type*}

private theorem scalar_order {q : ℝ} (hq : 2 < q) : 0 ≤ 3 / q ∧ 3 / q < 2 := by
  have hq0 : 0 < q := by linarith
  exact ⟨by positivity, (div_lt_iff₀ hq0).mpr (by linarith)⟩

private theorem contractive_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (hc : ‖c‖ ≤ 1) (w : H) : ‖c • w‖ ≤ ‖w‖ := by
  calc
    ‖c • w‖ = ‖c‖ * ‖w‖ := norm_smul c w
    _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg w)
    _ = ‖w‖ := one_mul _

variable (a : PfHk.PhysicalExternalCoefficients.Data N) (S : CoordinateSobolev.Data PhotonFock N)
  (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
  (joint : CoordinateComparisonSpectral.Data spectral)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ i : Fin N × Fin 3, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : Fin N × Fin 3, ∀ᵐ x : Configuration N ∂volume, ‖(κ i x).val‖ ≤ M)
  (e : ℝ)

include S spectral joint

theorem term_comparison_relative
    (u : X → Reference (Fin N × Fin 3) (fun _ => 0)) (L : X → WaveSpace (Fin N × Fin 3))
    (hL : ∀ x, IsComparisonPair (fun _ => 0) (u x) (L x))
    (P : ∀ x, Products a C κ hκ M hbound e (u x)) (t : Term N) :
    Bound (fun x => ‖L x‖) (fun x => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u x)‖)
      (fun x => ‖term a C κ hκ M hbound e (u x) (P x) t‖) := by
  rcases t with i | i | n | n | t <;> simp only [term]
  · apply PhysicalRelativeMultiplier.of_fractional_norm_sq spectral u L _ hL
      (s := 3 / 2) (B := (2 + 20 * e ^ 2 * (max M 0) ^ 2) *
        coefficientNormSq S 6 (a.vectorCoefficient i.1 i.2))
      (by norm_num) (by norm_num)
      (mul_nonneg (by positivity) (coefficientNormSq_nonneg S _ _))
    intro x
    exact (Classical.choose_spec (covariant_coordinate_multiplier S spectral joint C κ hκ M hbound e
      i.1 i (a.vectorCoefficient i.1 i.2) (a.vector_memLp i.1 i.2) (u x) ⟨L x, hL x⟩))
  · apply PhysicalRelativeMultiplier.of_fractional_norm_sq spectral u L _ hL
      (s := 1) (B := coefficientNormSq S 3 (fun y => a.vectorCoefficient i.1 i.2 y ^ 2))
      (by norm_num) (by norm_num) (coefficientNormSq_nonneg S _ _)
    intro x
    have hex := scalar_multiplier S spectral joint (by norm_num : (2 : ℝ) < 3)
      i.1 (fun y => a.vectorCoefficient i.1 i.2 y ^ 2)
      (by simpa using square_memLp_three (a.vector_memLp i.1 i.2)) (u x) ⟨L x, hL x⟩
    have hn := Classical.choose_spec hex
    have heq : roughMultiply (coordinateCoefficient i.1 (fun y => a.vectorCoefficient i.1 i.2 y ^ 2))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u x)) (Classical.choose hex) =
        roughMultiply (fun y => a.vector i y ^ 2)
          (inclusion (Fin N × Fin 3) (fun _ => 0) (u x)) ((P x).square i) := rfl
    have hs := congrArg (fun s : ℝ =>
      coefficientNormSq S 3 (fun y => a.vectorCoefficient i.1 i.2 y ^ 2) *
        fractionalNormSq spectral s (u x) ⟨L x, hL x⟩) (by norm_num : (3 : ℝ) / 3 = 1)
    exact (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ‖w‖ ^ 2) heq).symm.trans_le
      (hn.trans_eq hs)
  · have hs := scalar_order a.divergenceExponent_gt_two
    apply PhysicalRelativeMultiplier.of_fractional_norm_sq spectral u L _ hL
      hs.1 hs.2 (coefficientNormSq_nonneg S a.divergenceExponent (a.divergenceCoefficient n))
    intro x
    exact (Classical.choose_spec (scalar_multiplier S spectral joint a.divergenceExponent_gt_two
      n (a.divergenceCoefficient n) (a.divergence_memLp n) (u x) ⟨L x, hL x⟩))
  · have hs := scalar_order a.scalarExponent_gt_two
    apply PhysicalRelativeMultiplier.of_fractional_norm_sq spectral u L _ hL
      hs.1 hs.2 (coefficientNormSq_nonneg S a.scalarExponent (a.scalarCoefficient n))
    intro x
    exact (Classical.choose_spec (scalar_multiplier S spectral joint a.scalarExponent_gt_two
      n (a.scalarCoefficient n) (a.scalar_memLp n) (u x) ⟨L x, hL x⟩))
  · apply InfinitesimalBound.bounded (fun _ => norm_nonneg _)
      (eLpNorm a.boundedCoefficient ∞ volume).toReal ENNReal.toReal_nonneg
    intro x
    have hn := (Classical.choose_spec (bounded_multiplier a.boundedCoefficient a.bounded_memLp
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u x))))
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))).mp
    simpa only [mul_pow] using hn

theorem total_comparison_relative
    (u : X → Reference (Fin N × Fin 3) (fun _ => 0)) (L : X → WaveSpace (Fin N × Fin 3))
    (hL : ∀ x, IsComparisonPair (fun _ => 0) (u x) (L x))
    (P : ∀ x, Products a C κ hκ M hbound e (u x)) :
    Bound (fun x => ‖L x‖) (fun x => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u x)‖)
      (fun x => ‖total a C κ hκ M hbound e (u x) (P x)‖) := by
  have ht (t : Term N) : Bound (fun x => ‖L x‖)
      (fun x => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u x)‖)
      (fun x => ‖coefficient t • term a C κ hκ M hbound e (u x) (P x) t‖) :=
    InfinitesimalBound.mono (term_comparison_relative a S spectral joint C κ hκ M hbound e u L hL P t)
      (fun x => contractive_smul (coefficient t) (coefficient_norm t) _)
  apply InfinitesimalBound.mono
    (InfinitesimalBound.sum Finset.univ
      (fun t x => ‖coefficient t • term a C κ hκ M hbound e (u x) (P x) t‖)
      (fun _ => norm_nonneg _) (fun t _ => ht t))
  intro x
  unfold total
  exact norm_sum_le Finset.univ _

/-- Uniform infinitesimal free-operator boundedness of the actual magnetic
and signed scalar perturbation, with no assumed physical multiplier bound. -/
theorem infinitesimal_perturbation
    (hD : HaslerHerbstDomain C κ hκ M hbound e)
    (hG : HaslerHerbstGraphNorm C κ hκ M hbound e) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : Reference (Fin N × Fin 3) (fun _ => 0)) (f : WaveSpace (Fin N × Fin 3)),
        FreeGraph C κ hκ M hbound e u f →
        ∀ hu : OperatorMultipliers (fun _ => 0) C κ hκ M hbound e
          a.vector a.positive a.negative a.divergence u,
        ‖perturbation (fun _ => 0) C κ hκ M hbound e a.vector a.positive a.negative a.divergence u hu‖ ≤
          ε * ‖f‖ + K * ‖inclusion (Fin N × Fin 3) (fun _ => 0) u‖ := by
  let X := {p : Reference (Fin N × Fin 3) (fun _ => 0) × WaveSpace (Fin N × Fin 3) //
    FreeGraph C κ hκ M hbound e p.1 p.2}
  let u (x : X) := x.val.1
  let f (x : X) := x.val.2
  have hc (x : X) : ComparisonDomain (fun _ => 0) (u x) := (hD (u x)).mp ⟨f x, x.property⟩
  let L (x : X) := Classical.choose (hc x)
  have hL (x : X) : IsComparisonPair (fun _ => 0) (u x) (L x) := Classical.choose_spec (hc x)
  let P (x : X) := products_of_comparison a C κ hκ M hbound e (u x) S spectral joint (hc x)
  have ht := total_comparison_relative a S spectral joint C κ hκ M hbound e u L hL P
  have hf := InfinitesimalBound.comparison hG.bound_nonneg
    (fun x : X => norm_nonneg (f x)) (fun x : X => norm_nonneg (inclusion (Fin N × Fin 3) (fun _ => 0) (u x)))
    (fun x : X => hG.comparison_le (u x) (f x) (L x) x.property (hL x)) ht
  intro ε hε
  have hex := hf ε hε
  let K := Classical.choose hex
  have hk := Classical.choose_spec hex
  refine ⟨K, hk.1, ?_⟩
  intro v g hg hv
  let x : X := ⟨(v, g), hg⟩
  have heq := perturbation_eq_total a C κ hκ M hbound e v (P x) hv
    (a.scalar_hasMultiplier S spectral joint v (hc x))
  exact (congrArg norm heq).trans_le (hk.2 x)

end PfHk.PhysicalExternalRelativeBound
