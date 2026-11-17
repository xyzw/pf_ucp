import GptLean.RemovalSourceMarginal

/-!
Original spectral tests and universal operator locality are packaged
independently of localization and repair. Their methods derive the actual
localized WIS source sums, including the phased density and current
expressions consumed by exact trace-class constraint assembly.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure Filter ElectronicLocalization

variable {Q X H K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- One original bounded spectral test. Both locality formulas are
universal in their reference vectors and mention no localized output. -/
structure ProductTestData
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)) (ψ : ℕ → Lp H 2 ν) (target : ℂ) where
  operator : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν)
  sourceMultiplier : X → H →L[ℂ] H
  targetMultiplier : Q × X → K →L[ℂ] K
  sourceBound : ℝ
  targetBound : ℝ
  source_bounded : ∀ᵐ x ∂ν, ‖sourceMultiplier x‖ ≤ sourceBound
  target_bounded : ∀ᵐ qx ∂μ.prod ν, ‖targetMultiplier qx‖ ≤ targetBound
  source_measurable : ∀ n, AEStronglyMeasurable (fun x => sourceMultiplier x (ψ n x)) ν
  target_measurable : ∀ v : Lp K 2 (μ.prod ν),
    AEStronglyMeasurable (fun qx => targetMultiplier qx (v qx)) (μ.prod ν)
  source_rankOne : ∀ v : Lp H 2 ν, inner ℂ v (conjugatedOperator U operator v) =
    ∫ x, inner ℂ (v x) (sourceMultiplier x (v x)) ∂ν
  target_rankOne : ∀ v : Lp K 2 (μ.prod ν), inner ℂ v (operator v) =
    ∫ qx, inner ℂ (v qx) (targetMultiplier qx (v qx)) ∂μ.prod ν
  original : HasSum (fun n => inner ℂ (ψ n) (conjugatedOperator U operator (ψ n))) target

namespace ProductTestData

variable {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} {ψ : ℕ → Lp H 2 ν} {target : ℂ}
  (D : ProductTestData U ψ target)

theorem localized_hasSum (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (hmass : Summable (fun n => ‖ψ n‖ ^ 2)) :
    HasSum (fun i => ∫ q, ∫ x, inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
      (D.targetMultiplier (q, x) (localizedFiber U f hpart hf ψ i (q, x))) ∂ν ∂μ) target :=
  localizedFiber_product_test_hasSum U D.operator D.sourceMultiplier D.targetMultiplier
    D.source_bounded D.target_bounded D.target_measurable D.source_rankOne D.target_rankOne
    f hpart hf ψ D.source_measurable hmass D.original

theorem phased_hasSum (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => ∫ q, ∫ x,
      inner ℂ (phaseSource (w i (q, x)) (localizedFiber U f hpart hf ψ i (q, x)))
        (D.targetMultiplier (q, x)
          (phaseSource (w i (q, x)) (localizedFiber U f hpart hf ψ i (q, x)))) ∂ν ∂μ) target := by
  simpa only [phaseSource_test _ (hw _ _)] using D.localized_hasSum f hpart hf hmass

end ProductTestData

/-- A separating family of original hard-photon tests yields the exact
vector-valued source marginal. Only ordinary per-term norm and rank-one
test formulas remain, with no localized marginal sum assumption. -/
theorem ProductTestData.marginal_hasSum
    {F Test : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} {ψ : ℕ → Lp H 2 ν}
    (target : F) (tests : Test → F →L[ℝ] ℝ)
    (D : ∀ t, ProductTestData U ψ (tests t target : ℂ))
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (hmass : HasSum (fun n => ‖ψ n‖ ^ 2) 1)
    (sourceMarginal : ℕ → F)
    (separate : ∀ a b : F, (∀ t, tests t a = tests t b) → a = b)
    (C : ℝ) (hbound : ∀ i, ‖sourceMarginal i‖ ≤ C *
      ‖localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2‖ ^ 2)
    (htest : ∀ t i, tests t (sourceMarginal i) =
      (∫ q, ∫ x, inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
        ((D t).targetMultiplier (q, x) (localizedFiber U f hpart hf ψ i (q, x))) ∂ν ∂μ).re) :
    HasSum sourceMarginal target :=
  localizedFiber_product_marginal_hasSum U (fun t => (D t).operator)
    (fun t => (D t).sourceMultiplier) (fun t => (D t).targetMultiplier)
    (fun t => (D t).sourceBound) (fun t => (D t).targetBound)
    (fun t => (D t).source_bounded) (fun t => (D t).target_bounded)
    (fun t => (D t).target_measurable) (fun t => (D t).source_rankOne)
    (fun t => (D t).target_rankOne) f hpart hf ψ (fun t => (D t).source_measurable)
    hmass sourceMarginal target tests separate C hbound htest (fun t => (D t).original)

/-- A density test adds only the scalar action of the universal target
multiplier, together with the bounded physical spatial test function. -/
structure ProductDensityTest
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)) (ψ : ℕ → Lp H 2 ν) (target : ℝ)
    extends ProductTestData U ψ (target : ℂ) where
  weight : X → ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  weight_measurable : AEStronglyMeasurable weight ν
  weight_bounded : ∀ᵐ x ∂ν, ‖weight x‖ ≤ bound
  scalar : ∀ qx v, inner ℂ v (targetMultiplier qx v) = ((weight qx.2 * ‖v‖ ^ 2 : ℝ) : ℂ)

theorem ProductDensityTest.phased_density_hasSum
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} {ψ : ℕ → Lp H 2 ν} {target : ℝ}
    (D : ProductDensityTest U ψ target) (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (w : ℕ → Q × X → ℂ) (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => ∫ q, ∫ x, D.weight x *
      ‖phaseSource (w i (q, x)) (localizedFiber U f hpart hf ψ i (q, x))‖ ^ 2 ∂ν ∂μ) target := by
  have hs := D.toProductTestData.phased_hasSum f hpart hf hmass w hw
  have hr := Complex.hasSum_re hs
  simp_rw [D.scalar, integral_complex_ofReal, Complex.ofReal_re] at hr
  exact hr

/-- Conversion to the exact real-part-of-integral source-current
convention. Its complex integral is controlled by the two original L²
vectors and the bounded test, before the phase cancels. -/
theorem phaseSource_current_iterated
    (ψ dψ : Lp K 2 (μ.prod ν)) (w : Q × X → ℂ) (s : Q × X → ℝ)
    (hw : ∀ᵐ qx ∂μ.prod ν, ‖w qx‖ = 1)
    (weight : X → ℝ) (hm : AEStronglyMeasurable weight ν) {C : ℝ}
    (hb : ∀ᵐ x ∂ν, ‖weight x‖ ≤ C) :
    (∫ q, (∫ x,
      inner ℂ (phaseSource (w (q, x)) (ψ (q, x)))
        ((weight x : ℂ) • phaseSourceDerivative (w (q, x)) (s (q, x)) (dψ (q, x)) (ψ (q, x))) +
      ((weight x * s (q, x) : ℝ) : ℂ) *
        ‖phaseSource (w (q, x)) (ψ (q, x))‖ ^ 2 ∂ν).re ∂μ) =
      ∫ q, ∫ x, weight x * (inner ℂ (ψ (q, x)) (dψ (q, x))).re ∂ν ∂μ := by
  have hm' : AEStronglyMeasurable (fun qx : Q × X => (weight qx.2 : ℂ)) (μ.prod ν) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm).comp_quasiMeasurePreserving
      quasiMeasurePreserving_snd
  have hb' : ∀ᵐ qx : Q × X ∂μ.prod ν, ‖(weight qx.2 : ℂ)‖ ≤ C := by
    have h := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hb
    simpa only [Complex.norm_real] using h
  have hi := (L2.integrable_inner (𝕜 := ℂ) ψ dψ).bdd_mul hm' hb'
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae, ae_ae_of_ae_prod hw] with q hq huw
  have he : (∫ x,
      inner ℂ (phaseSource (w (q, x)) (ψ (q, x)))
        ((weight x : ℂ) • phaseSourceDerivative (w (q, x)) (s (q, x)) (dψ (q, x)) (ψ (q, x))) +
      ((weight x * s (q, x) : ℝ) : ℂ) *
        ‖phaseSource (w (q, x)) (ψ (q, x))‖ ^ 2 ∂ν) =
      ∫ x, (weight x : ℂ) * inner ℂ (ψ (q, x)) (dψ (q, x)) ∂ν :=
    integral_congr_ae (huw.mono (fun x hx =>
      phaseSource_weighted_current (w (q, x)) hx (weight x) (s (q, x)) (dψ (q, x)) (ψ (q, x))))
  have hre : (∫ x, (weight x : ℂ) * inner ℂ (ψ (q, x)) (dψ (q, x)) ∂ν).re =
      ∫ x, ((weight x : ℂ) * inner ℂ (ψ (q, x)) (dψ (q, x))).re ∂ν :=
    (integral_re hq).symm
  rw [he, hre]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

section Current

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Original current data uses one actual covariant derivative spectral
family. Operator locality and its original trace series are universal. -/
structure ProductCurrentData
    (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν))
    (ψ dψ : ℕ → Lp H 2 ν) (target : ℝ) where
  operator : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν)
  sourceWeight : X → ℝ
  weight : X → ℝ
  sourceBound : ℝ
  bound : ℝ
  source_measurable : AEStronglyMeasurable sourceWeight ν
  source_bounded : ∀ᵐ x ∂ν, ‖sourceWeight x‖ ≤ sourceBound
  weight_measurable : AEStronglyMeasurable weight ν
  weight_bounded : ∀ᵐ x ∂ν, ‖weight x‖ ≤ bound
  source_rankOne : ∀ v d : Lp H 2 ν, (inner ℂ v (conjugatedOperator U operator d)).re =
    ∫ x, sourceWeight x * (inner ℂ (v x) (d x)).re ∂ν
  target_rankOne : ∀ v d : Lp K 2 (μ.prod ν), (inner ℂ v (operator d)).re =
    ∫ qx, weight qx.2 * (inner ℂ (v qx) (d qx)).re ∂μ.prod ν
  original : HasSum (fun n => (inner ℂ (ψ n) (conjugatedOperator U operator (dψ n))).re) target

theorem ProductCurrentData.localized_hasSum
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} {ψ dψ : ℕ → Lp H 2 ν} {target : ℝ}
    (D : ProductCurrentData U ψ dψ target)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2)) :
    HasSum (fun i => ∫ q, ∫ x, D.weight x *
      (inner ℂ (localizedFiber U f hpart hf ψ i (q, x))
        (localizedDerivativeFiber U f ψ dψ v hmem i (q, x))).re ∂ν ∂μ) target := by
  exact localizedFiber_product_current_hasSum U D.operator D.source_measurable D.source_bounded
    (D.weight_measurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
    (quasiMeasurePreserving_snd.ae D.weight_bounded)
    D.source_rankOne D.target_rankOne f hpart hf ψ dψ v hmem hmass hkinetic D.original

theorem ProductCurrentData.phased_current_hasSum
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} {ψ dψ : ℕ → Lp H 2 ν} {target : ℝ}
    (D : ProductCurrentData U ψ dψ target)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (v : X)
    (hmem : ∀ n a, MemLp (localizedDerivative f (dψ n) (ψ n) v a) 2 ν)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkinetic : Summable (fun p : ℕ × ℕ =>
      ‖localizedDerivativeVector f (ψ p.1) (dψ p.1) v (hmem p.1) p.2‖ ^ 2))
    (w : ℕ → Q × X → ℂ) (s : ℕ → Q × X → ℝ) (hw : ∀ i qx, ‖w i qx‖ = 1) :
    HasSum (fun i => ∫ q, (∫ x,
      inner ℂ (phaseSource (w i (q, x)) (localizedFiber U f hpart hf ψ i (q, x)))
        ((D.weight x : ℂ) • phaseSourceDerivative (w i (q, x)) (s i (q, x))
          (localizedDerivativeFiber U f ψ dψ v hmem i (q, x)) (localizedFiber U f hpart hf ψ i (q, x))) +
        ((D.weight x * s i (q, x) : ℝ) : ℂ) *
          ‖phaseSource (w i (q, x)) (localizedFiber U f hpart hf ψ i (q, x))‖ ^ 2 ∂ν).re ∂μ) target := by
  apply (D.localized_hasSum f hpart hf v hmem hmass hkinetic).congr_fun
  intro i
  exact phaseSource_current_iterated
    (U (localizedVector f hpart hf (ψ (Nat.unpair i).1) (Nat.unpair i).2))
    (U (localizedDerivativeVector f (ψ (Nat.unpair i).1) (dψ (Nat.unpair i).1)
      v (hmem (Nat.unpair i).1) (Nat.unpair i).2))
    (w i) (s i) (Eventually.of_forall (hw i)) D.weight D.weight_measurable D.weight_bounded

end Current
end GptLean.RemovalSource
