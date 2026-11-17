import PfHk.PhysicalComparisonDomain
import PfHk.PhysicalCutoffCommutatorEstimate
import PfHk.ScalarWeightedCommutator
import PfHk.WeightedNorm
import PfHk.L2ScalarNorm
import PfHk.DyadicIntegralBounds

/-! The second dyadic endpoint starts with the actual cutoff graph image.
The standard graph-norm theorem is applied only after the exact physical
commutator has placed the localized vector in the operator domain. -/

noncomputable section
namespace PfHk.PhysicalDyadicGraph

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalCutoffCommutator PfHk.PhysicalOperatorDomain PfHk.PhysicalLocalEnergy

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
set_option Elab.async false

local instance dyadicPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  PfHk.PhysicalOperatorDomain.comparisonPhotonDirectInner

private theorem weighted_sum_identity {J : Type*} (S : Finset J)
    (c x y z : J → ℝ) (C : ℝ) :
    (∑ j ∈ S, c j * (C * (2 * x j + 2 * y j + z j))) =
      C * (2 * (∑ j ∈ S, c j * x j) + 2 * (∑ j ∈ S, c j * y j) +
        (∑ j ∈ S, c j * z j)) := by
  calc
    _ = ∑ j ∈ S, C * (2 * (c j * x j) + 2 * (c j * y j) + c j * z j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem square_graph_bound (x y z b : ℝ) (hx : 0 ≤ x)
    (h : x ≤ b * (y + z)) : x ^ 2 ≤ (2 * b ^ 2) * (y ^ 2 + z ^ 2) := by
  have hp := pow_le_pow_left₀ hx h 2
  have hn := mul_nonneg (sq_nonneg b) (sq_nonneg (y - z))
  nlinarith only [hp, hn]

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.ordinary PhysicalPFReference.radiation externalCovariant
  PhysicalPFReference.referenceSubspace IsOperatorPair IsComparisonPair
  PhysicalCutoffCommutator.commutator scalarCommutator
  GptLean.ElectronicH1Multiplier.DifferentiableMultiplier.multiplier

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

/-- Actual domain inclusion and graph estimate for a smooth localized
operator vector. The comparison graph is `-Δ + Hrad + 1`. -/
theorem localized_comparison_bound
    (hD : DomainIdentification V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (hG : GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (a : TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f) :
    ∃ L, IsComparisonPair V (PhysicalPFScalarMultiplier.multiply V a.scalar u) L ∧
      ‖L‖ ^ 2 ≤ (2 * hG.bound ^ 2) *
        (2 * ‖a.scalar.multiplier (H := PhotonFock) f‖ ^ 2 +
          2 * ‖commutator V C κ hκ M hbound e A positive negative a u hu‖ ^ 2 +
          ‖a.scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2) := by
  have hpair := operatorPair_localize V C κ hκ M hbound e A positive negative a hf
  have hlocalized : OperatorGraph V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar u)
      (a.scalar.multiplier (H := PhotonFock) f +
        commutator V C κ hκ M hbound e A positive negative a u hu) :=
    ⟨hu.localize V a.scalar, hpair⟩
  have hex := comparison_graph_bound
    (u := PhysicalPFScalarMultiplier.multiply V a.scalar u)
    (f := a.scalar.multiplier (H := PhotonFock) f +
      commutator V C κ hκ M hbound e A positive negative a u hu) hD hG hlocalized
  let L := Classical.choose hex
  have hL := (Classical.choose_spec hex).1
  have hb := (Classical.choose_spec hex).2
  refine ⟨L, hL, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (WeightedNorm.add_sq_bound (a.scalar.multiplier (H := PhotonFock) f)
      (commutator V C κ hκ M hbound e A positive negative a u hu))
    ((congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar u)).le)

/-- The commutator part of the graph estimate consists of the actual
covariant energy and actual mass on the derivative-support annulus. -/
theorem commutator_norm_bound (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    {s : Set (Position I)} (hs : MeasurableSet s) {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hgrad : ∀ x ∈ s, ∑ i, a.scalar.gradient i x ^ 2 ≤ G)
    (hlap : ∀ x ∈ s, laplacian a x ^ 2 ≤ L)
    (houtgrad : ∀ x ∉ s, ∀ i, a.scalar.gradient i x = 0)
    (houtlap : ∀ x ∉ s, laplacian a x = 0) :
    ‖commutator V C κ hκ M hbound e A positive negative a u hu‖ ^ 2 ≤
      2 * G * (∑ i, massOn s
        (externalCovariant V C κ hκ M hbound e A positive negative u hu i)) +
        (1 / 2 : ℝ) * L * massOn s (inclusion I V u) := by
  have h := weighted_commutator_bound V C κ hκ M hbound e A positive negative a u hu
    hs (w := fun _ => 1) (W := 1) aestronglyMeasurable_const
    (fun _ => zero_le_one) zero_le_one hG hL (fun _ _ => le_rfl)
    hgrad hlap houtgrad houtlap
  simpa only [one_mul, ← l2_norm_sq, PhysicalCutoffCommutator.commutator] using h.2

/-- Pointwise exponential derivative weights remain inside their actual
energy integrals. This is the version used for the weighted dyadic cutoffs. -/
theorem commutator_variable_norm_bound (a : TwiceDifferentiableMultiplier I) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (G L : Position I → ℝ)
    (hgrad : ∀ x, (∑ i, a.scalar.gradient i x ^ 2) ≤ G x)
    (hlap : ∀ x, laplacian a x ^ 2 ≤ L x)
    (hGI : Integrable (fun x => G x * (∑ i,
      ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) volume)
    (hLI : Integrable (fun x => L x * ‖inclusion I V u x‖ ^ 2) volume) :
    ‖commutator V C κ hκ M hbound e A positive negative a u hu‖ ^ 2 ≤
      2 * (∫ x, G x * (∑ i,
        ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) +
        (1 / 2 : ℝ) * (∫ x, L x * ‖inclusion I V u x‖ ^ 2) := by
  have h := scalar_weighted_variable_commutator_bound (H := PhotonFock) a (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu)
    (fun _ => 1) G L aestronglyMeasurable_const (fun _ => zero_le_one) hgrad hlap
    (by simpa only [one_mul] using hGI) (by simpa only [one_mul] using hLI)
  simpa only [one_mul, ← l2_norm_sq, PhysicalCutoffCommutator.commutator] using h.2

/-- The finite annular graph sum is derived by applying the actual product
formula separately to every localized vector. In the dyadic application
`coefficient j = βⱼ Rⱼ² / τ`. -/
theorem localized_comparison_sum {J : Type*} (S : Finset J)
    (coefficient : J → ℝ) (hc : ∀ j ∈ S, 0 ≤ coefficient j)
    (hD : DomainIdentification V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (hG : GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (a : J → TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f) :
    ∃ L : J → WaveSpace I,
      (∀ j, IsComparisonPair V (PhysicalPFScalarMultiplier.multiply V (a j).scalar u) (L j)) ∧
      (∑ j ∈ S, coefficient j * ‖L j‖ ^ 2) ≤ (2 * hG.bound ^ 2) *
        (2 * (∑ j ∈ S, coefficient j * ‖(a j).scalar.multiplier (H := PhotonFock) f‖ ^ 2) +
          2 * (∑ j ∈ S, coefficient j *
            ‖commutator V C κ hκ M hbound e A positive negative (a j) u hu‖ ^ 2) +
          (∑ j ∈ S, coefficient j *
            ‖(a j).scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2)) := by
  classical
  have hex := fun j => localized_comparison_bound
    V C κ hκ M hbound e A positive negative hD hG (a j) hf
  let L := fun j => Classical.choose (hex j)
  have hL := fun j => (Classical.choose_spec (hex j)).1
  have hb := fun j => (Classical.choose_spec (hex j)).2
  refine ⟨L, hL, ?_⟩
  calc
    _ ≤ ∑ j ∈ S, coefficient j * ((2 * hG.bound ^ 2) *
        (2 * ‖(a j).scalar.multiplier (H := PhotonFock) f‖ ^ 2 +
          2 * ‖commutator V C κ hκ M hbound e A positive negative (a j) u hu‖ ^ 2 +
          ‖(a j).scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2)) :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hb j) (hc j hj)
    _ = _ := weighted_sum_identity S coefficient _ _ _ _

/-- A pointwise sum of scalar cutoff squares controls the actual localized
Hilbert-space norms. No separate annular norm estimate is assumed. -/
theorem multiplier_norm_sum_bound {J : Type*} (S : Finset J)
    (a : J → TwiceDifferentiableMultiplier I) (c : J → ℝ)
    (f : WaveSpace I) (W : Position I → ℝ)
    (hweight : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ W x)
    (hWI : Integrable (fun x => W x * ‖f x‖ ^ 2) volume) :
    (∑ j ∈ S, c j * ‖(a j).scalar.multiplier (H := PhotonFock) f‖ ^ 2) ≤
      ∫ x, W x * ‖f x‖ ^ 2 := by
  exact scalar_multiplier_norm_sum_bound (H := PhotonFock) S a c f W hweight hWI

/-- Actual comparison graph images and their integrated second-order
estimate follow from scalar finite-overlap bounds and the product rule. -/
theorem localized_comparison_integral_sum {J : Type*} (S : Finset J)
    (c : J → ℝ) (hc : ∀ j ∈ S, 0 ≤ c j)
    (hD : DomainIdentification V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (hG : GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (a : J → TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f)
    (Wf Wu G L : Position I → ℝ)
    (hsource : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ Wf x)
    (hmass : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ Wu x)
    (hgrad : ∀ x, (∑ j ∈ S, c j * (∑ i, (a j).scalar.gradient i x ^ 2)) ≤ G x)
    (hlap : ∀ x, (∑ j ∈ S, c j * laplacian (a j) x ^ 2) ≤ L x)
    (hfI : Integrable (fun x => Wf x * ‖f x‖ ^ 2) volume)
    (huI : Integrable (fun x => Wu x * ‖inclusion I V u x‖ ^ 2) volume)
    (hGI : Integrable (fun x => G x * (∑ i,
      ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) volume)
    (hLI : Integrable (fun x => L x * ‖inclusion I V u x‖ ^ 2) volume) :
    ∃ v : J → WaveSpace I,
      (∀ j, IsComparisonPair V (PhysicalPFScalarMultiplier.multiply V (a j).scalar u) (v j)) ∧
      (∑ j ∈ S, c j * ‖v j‖ ^ 2) ≤ (2 * hG.bound ^ 2) *
        (2 * (∫ x, Wf x * ‖f x‖ ^ 2) +
          4 * (∫ x, G x * (∑ i,
            ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) +
          (∫ x, L x * ‖inclusion I V u x‖ ^ 2) +
          (∫ x, Wu x * ‖inclusion I V u x‖ ^ 2)) := by
  have hex := localized_comparison_sum V C κ hκ M hbound e A positive negative
    S c hc hD hG a hf
  let v := Classical.choose hex
  have hv := (Classical.choose_spec hex).1
  have hb := (Classical.choose_spec hex).2
  have hfb := multiplier_norm_sum_bound S a c f Wf hsource hfI
  have hub := multiplier_norm_sum_bound S a c (inclusion I V u) Wu hmass huI
  have hcb := scalar_commutator_sum_bound S a c hc (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu) G L hgrad hlap hGI hLI
  simp only [← l2_norm_sq] at hcb
  refine ⟨v, hv, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [PhysicalCutoffCommutator.commutator]
  linarith only [hfb, hub, hcb]

/-- The graph estimate for a specified comparison image. Its graph
membership already supplies the comparison-domain condition. -/
theorem localized_comparison_bound_fixed
    (hG : GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (a : TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f)
    (v : WaveSpace I)
    (hv : IsComparisonPair V (PhysicalPFScalarMultiplier.multiply V a.scalar u) v) :
    ‖v‖ ^ 2 ≤ (2 * hG.bound ^ 2) *
      (2 * ‖a.scalar.multiplier (H := PhotonFock) f‖ ^ 2 +
        2 * ‖PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative a u hu‖ ^ 2 +
        ‖a.scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2) := by
  have hpair := operatorPair_localize V C κ hκ M hbound e A positive negative a hf
  have hlocalized : OperatorGraph V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a.scalar u)
      (a.scalar.multiplier (H := PhotonFock) f +
        PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative a u hu) :=
    ⟨hu.localize V a.scalar, hpair⟩
  have hn := hG.comparison_le _ _ v hlocalized hv
  have hb := square_graph_bound _ _ _ _ (norm_nonneg v) hn
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (WeightedNorm.add_sq_bound (a.scalar.multiplier (H := PhotonFock) f)
      (PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative a u hu))
    ((congrArg (fun z : WaveSpace I => ‖z‖ ^ 2)
      (PhysicalPFScalarMultiplier.value_multiply V a.scalar u)).le)

/-- Integrated graph estimate for fixed comparison images, without a
second choice of operator images or a uniqueness substitution. -/
theorem localized_comparison_integral_sum_fixed {J : Type*} (S : Finset J)
    (c : J → ℝ) (hc : ∀ j ∈ S, 0 ≤ c j)
    (hG : GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative))
    (a : J → TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f)
    (v : J → WaveSpace I)
    (hv : ∀ j, IsComparisonPair V (PhysicalPFScalarMultiplier.multiply V (a j).scalar u) (v j))
    (Wf Wu G L : Position I → ℝ)
    (hsource : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ Wf x)
    (hmass : ∀ x, (∑ j ∈ S, c j * (a j).scalar.weight x ^ 2) ≤ Wu x)
    (hgrad : ∀ x, (∑ j ∈ S, c j * (∑ i, (a j).scalar.gradient i x ^ 2)) ≤ G x)
    (hlap : ∀ x, (∑ j ∈ S, c j * laplacian (a j) x ^ 2) ≤ L x)
    (hfI : Integrable (fun x => Wf x * ‖f x‖ ^ 2) volume)
    (huI : Integrable (fun x => Wu x * ‖inclusion I V u x‖ ^ 2) volume)
    (hGI : Integrable (fun x => G x * (∑ i,
      ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) volume)
    (hLI : Integrable (fun x => L x * ‖inclusion I V u x‖ ^ 2) volume) :
    (∑ j ∈ S, c j * ‖v j‖ ^ 2) ≤ (2 * hG.bound ^ 2) *
      (2 * (∫ x, Wf x * ‖f x‖ ^ 2) +
        4 * (∫ x, G x * (∑ i,
          ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i x‖ ^ 2)) +
        (∫ x, L x * ‖inclusion I V u x‖ ^ 2) +
        (∫ x, Wu x * ‖inclusion I V u x‖ ^ 2)) := by
  have hb : (∑ j ∈ S, c j * ‖v j‖ ^ 2) ≤ (2 * hG.bound ^ 2) *
      (2 * (∑ j ∈ S, c j * ‖(a j).scalar.multiplier (H := PhotonFock) f‖ ^ 2) +
        2 * (∑ j ∈ S, c j *
          ‖PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative (a j) u hu‖ ^ 2) +
        (∑ j ∈ S, c j * ‖(a j).scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2)) := by
    calc
      _ ≤ ∑ j ∈ S, c j * ((2 * hG.bound ^ 2) *
          (2 * ‖(a j).scalar.multiplier (H := PhotonFock) f‖ ^ 2 +
            2 * ‖PhysicalCutoffCommutator.commutator V C κ hκ M hbound e A positive negative (a j) u hu‖ ^ 2 +
            ‖(a j).scalar.multiplier (H := PhotonFock) (inclusion I V u)‖ ^ 2)) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (localized_comparison_bound_fixed V C κ hκ M hbound e A positive negative
            hG (a j) hf (v j) (hv j)) (hc j hj)
      _ = _ := weighted_sum_identity S c _ _ _ _
  have hfb := multiplier_norm_sum_bound S a c f Wf hsource hfI
  have hub := multiplier_norm_sum_bound S a c (inclusion I V u) Wu hmass huI
  have hcb := scalar_commutator_sum_bound S a c hc (inclusion I V u)
    (externalCovariant V C κ hκ M hbound e A positive negative u hu) G L hgrad hlap hGI hLI
  simp only [← l2_norm_sq] at hcb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [PhysicalCutoffCommutator.commutator]
  linarith only [hfb, hub, hcb]

end PfHk.PhysicalDyadicGraph
