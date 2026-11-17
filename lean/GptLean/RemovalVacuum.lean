import GptLean.RemovalConstruction
import GptLean.SymmetricLift.CompletedTensor
import GptLean.RemovalEstimates

/-!
Soft-vacuum preparation on the actual completed Hilbert tensor product.
The vector map, its current pairing and its kinetic correction are
constructed here. A finite-energy repaired operator is then prepared by
mapping each of its Kraus vectors. Positivity, normalization, convergence
and the aggregate energy bound follow from the vector estimates.

The trace-class pushforward and the rank-one form evaluations are standard
operator background. The latter must identify the physical covariant
derivative with the displayed tensor expression on its form domain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.RemovalVacuum

open MeasureTheory Filter UniformSpace RemovalState RemovalConstruction
open scoped ENNReal InnerProductSpace

variable {K V : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The full hard/soft Hilbert space, with the Hilbert completion retained. -/
abbrev VacuumSpace (K V : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] := Completion (TensorProduct ℂ K V)

/-- Tensoring with a normalized soft vacuum is a concrete linear isometry. -/
def vacuumEmbedding (Ω : V) (hΩ : ‖Ω‖ = 1) : K →ₗᵢ[ℂ] VacuumSpace K V :=
  (Completion.toComplₗᵢ : TensorProduct ℂ K V →ₗᵢ[ℂ] VacuumSpace K V).comp
    { toLinearMap := (TensorProduct.mk ℂ K V).flip Ω
      norm_map' := fun u => by
        change ‖u ⊗ₜ[ℂ] Ω‖ = ‖u‖
        rw [TensorProduct.norm_tmul, hΩ, mul_one] }

/-- The full covariant derivative of a prepared vector, with its vacuum
field term. This expression is an element of the completed tensor product. -/
def vacuumDerivative (Ω χ : V) (e : ℝ) (u ψ : K) : VacuumSpace K V :=
  ((u ⊗ₜ[ℂ] Ω - (e : ℂ) • (ψ ⊗ₜ[ℂ] χ) : TensorProduct ℂ K V) : VacuumSpace K V)

theorem vacuumDerivative_norm_sq (Ω χ : V) (hΩ : ‖Ω‖ = 1)
    (hχ : inner ℂ Ω χ = 0) (e : ℝ) (u ψ : K) :
    ‖vacuumDerivative Ω χ e u ψ‖ ^ 2 =
      ‖u‖ ^ 2 + e ^ 2 * ‖χ‖ ^ 2 * ‖ψ‖ ^ 2 := by
  simpa only [vacuumDerivative, Completion.norm_coe] using
    RemovalEstimates.norm_tmul_vacuum_sub_sq u ψ hΩ hχ e

/-- Vacuum expectation zero removes the soft term from the tested current. -/
theorem vacuumDerivative_inner (Ω χ : V) (hΩ : ‖Ω‖ = 1)
    (hχ : inner ℂ Ω χ = 0) (e : ℝ) (u ψ φ : K) :
    inner ℂ (vacuumEmbedding Ω hΩ φ) (vacuumDerivative Ω χ e u ψ) =
      inner ℂ φ u := by
  change inner ℂ ((φ ⊗ₜ[ℂ] Ω : TensorProduct ℂ K V) : VacuumSpace K V)
    ((u ⊗ₜ[ℂ] Ω - (e : ℂ) • (ψ ⊗ₜ[ℂ] χ) : TensorProduct ℂ K V) : VacuumSpace K V) = _
  rw [Completion.inner_coe, TensorProduct.smul_tmul', inner_sub_right,
    TensorProduct.inner_tmul, TensorProduct.inner_tmul, hχ,
    inner_self_eq_norm_sq_to_K, hΩ]
  simp

/-- The added full kinetic energy depends only on the vacuum variance and
the mass, with no contribution from the measured cluster-field value. -/
theorem vacuum_kinetic_eq {I : Type*} [Fintype I]
    (Ω : V) (χ : I → V) (hΩ : ‖Ω‖ = 1)
    (hχ : ∀ i, inner ℂ Ω (χ i) = 0) (e : ℝ) (u : I → K) (ψ : K) :
    (1 / 2 : ℝ) * ∑ i, ‖vacuumDerivative Ω (χ i) e (u i) ψ‖ ^ 2 =
      1 / 2 * ∑ i, ‖u i‖ ^ 2 +
        (e ^ 2 / 2 * ∑ i, ‖χ i‖ ^ 2) * ‖ψ‖ ^ 2 := by
  simp_rw [vacuumDerivative_norm_sq Ω _ hΩ (hχ _) e]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Standard rank-one form evaluations and the proved tensor calculation
give the energy identity needed by the operator preparation below. -/
theorem vacuum_rankOne_energy {I : Type*} [Fintype I]
    (Ω : V) (χ : I → V) (hΩ : ‖Ω‖ = 1)
    (hχ : ∀ i, inner ℂ Ω (χ i) = 0) (e : ℝ) (u : I → K) (ψ : K)
    (rest hard full : ℝ)
    (hhard : hard = 1 / 2 * ∑ i, ‖u i‖ ^ 2 + rest)
    (hfull : full = 1 / 2 * ∑ i, ‖vacuumDerivative Ω (χ i) e (u i) ψ‖ ^ 2 + rest) :
    full = hard + (e ^ 2 / 2 * ∑ i, ‖χ i‖ ^ 2) * ‖ψ‖ ^ 2 := by
  rw [hfull, vacuum_kinetic_eq Ω χ hΩ hχ e u ψ, hhard]
  ring

/-- The physical vacuum field may depend on the electron configuration.
The fibre identity is integrated before it is used as a form evaluation.
Only the total vacuum variance is required to be constant almost everywhere. -/
theorem integrated_vacuum_kinetic_eq {X I : Type*} [MeasurableSpace X]
    [Fintype I] {ν : Measure X} (Ω : V) (χ : I → X → V) (hΩ : ‖Ω‖ = 1)
    (hχ : ∀ᵐ x ∂ν, ∀ i, inner ℂ Ω (χ i x) = 0)
    (e σ : ℝ) (hvariance : ∀ᵐ x ∂ν, ∑ i, ‖χ i x‖ ^ 2 = σ)
    (u : I → X → K) (ψ : X → K)
    (hu : Integrable (fun x => (1 / 2 : ℝ) * ∑ i, ‖u i x‖ ^ 2) ν)
    (hψ : Integrable (fun x => ‖ψ x‖ ^ 2) ν) :
    Integrable (fun x => (1 / 2 : ℝ) *
      ∑ i, ‖vacuumDerivative Ω (χ i x) e (u i x) (ψ x)‖ ^ 2) ν ∧
    (∫ x, (1 / 2 : ℝ) * ∑ i,
        ‖vacuumDerivative Ω (χ i x) e (u i x) (ψ x)‖ ^ 2 ∂ν) =
      (∫ x, (1 / 2 : ℝ) * ∑ i, ‖u i x‖ ^ 2 ∂ν) +
        (e ^ 2 / 2 * σ) * ∫ x, ‖ψ x‖ ^ 2 ∂ν := by
  have heq : (fun x => (1 / 2 : ℝ) *
      ∑ i, ‖vacuumDerivative Ω (χ i x) e (u i x) (ψ x)‖ ^ 2) =ᵐ[ν]
      (fun x => (1 / 2 : ℝ) * ∑ i, ‖u i x‖ ^ 2 +
        (e ^ 2 / 2 * σ) * ‖ψ x‖ ^ 2) := by
    filter_upwards [hχ, hvariance] with x hx hv
    rw [vacuum_kinetic_eq Ω (fun i => χ i x) hΩ hx e (fun i => u i x) (ψ x), hv]
  have hi := hu.add (hψ.const_mul (e ^ 2 / 2 * σ))
  refine ⟨hi.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hu (hψ.const_mul _)]
  simp only [integral_const_mul]

/-- Spatial integration preserves the tested current with a
configuration-dependent soft vacuum field. -/
theorem integrated_vacuum_current_eq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Ω : V) (χ : X → V) (hΩ : ‖Ω‖ = 1)
    (hχ : ∀ᵐ x ∂ν, inner ℂ Ω (χ x) = 0) (e : ℝ) (u ψ φ : X → K)
    (hi : Integrable (fun x => inner ℂ (φ x) (u x)) ν) :
    Integrable (fun x => inner ℂ (vacuumEmbedding Ω hΩ (φ x))
      (vacuumDerivative Ω (χ x) e (u x) (ψ x))) ν ∧
    (∫ x, inner ℂ (vacuumEmbedding Ω hΩ (φ x))
      (vacuumDerivative Ω (χ x) e (u x) (ψ x)) ∂ν) =
      ∫ x, inner ℂ (φ x) (u x) ∂ν := by
  have heq : (fun x => inner ℂ (vacuumEmbedding Ω hΩ (φ x))
      (vacuumDerivative Ω (χ x) e (u x) (ψ x))) =ᵐ[ν]
      (fun x => inner ℂ (φ x) (u x)) := by
    filter_upwards [hχ] with x hx
    exact vacuumDerivative_inner Ω (χ x) hΩ hx e (u x) (ψ x) (φ x)
  exact ⟨hi.congr heq.symm, integral_congr_ae heq⟩

section OperatorPreparation

variable {H Q T U : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace Q] {μ : Measure Q} [IsProbabilityMeasure μ]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  {R : Gaussian.RankOneData K T} {S : Gaussian.RankOneData H U}
  {Tr : PositiveTraceData T} {Tr' : PositiveTraceData U}
  {E : PositiveForm Tr} {E' : PositiveForm Tr'}

/-- Preparation of every vector constructs a new finite-energy ensemble.
The sole energy input is a rank-one bound on finite-energy vectors.
No property of an output operator is supplied. -/
def prepareVectorData (D : VectorData R Tr E μ) (J : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (J v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2)) :
    VectorData S Tr' E' μ where
  vector a k q := J (D.vector a k q)
  measurable a k := J.continuous.comp_aestronglyMeasurable (D.measurable a k)
  mass := D.mass
  mass_sum a := by simpa only [J.norm_map] using D.mass_sum a
  mass_integrable := D.mass_integrable
  normalized := D.normalized
  positive_compatible := hpositive
  trace_compatible := htrace
  energyCap a q := D.energyCap a q + c * D.mass a q
  cap_integrable a := (D.cap_integrable a).add ((D.mass_integrable a).const_mul c)
  cap_nonneg a := by
    filter_upwards [D.cap_nonneg a, D.mass_sum a] with q hcap hmass
    have hm : 0 ≤ D.mass a q := by
      rw [← hmass.tsum_eq]
      exact tsum_nonneg (fun k => sq_nonneg _)
    exact add_nonneg hcap (mul_nonneg hc hm)
  cap_summable := by
    simpa only [integral_add (D.cap_integrable _) ((D.mass_integrable _).const_mul c),
      integral_const_mul] using D.cap_summable.add (D.normalized.summable.mul_left c)
  vector_energy_le a := by
    filter_upwards [D.vector_energy_le a, D.cap_nonneg a, D.mass_sum a]
      with q he hcap hmass
    have hfinite (k : ℕ) : E.expectation (R.rankOne (D.vector a k q)) < ⊤ :=
      (ENNReal.le_tsum k).trans_lt (he.trans_lt ENNReal.ofReal_lt_top)
    have hm : 0 ≤ D.mass a q := by
      rw [← hmass.tsum_eq]
      exact tsum_nonneg (fun k => sq_nonneg _)
    calc
      _ ≤ ∑' k, (E.expectation (R.rankOne (D.vector a k q)) +
          ENNReal.ofReal (c * ‖D.vector a k q‖ ^ 2)) :=
        ENNReal.tsum_le_tsum (fun k => henergy _ (hfinite k))
      _ = (∑' k, E.expectation (R.rankOne (D.vector a k q))) +
          ENNReal.ofReal (c * D.mass a q) := by
        rw [ENNReal.tsum_add]
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg hc (sq_nonneg _)) (hmass.summable.mul_left c),
          tsum_mul_left, hmass.tsum_eq]
      _ ≤ ENNReal.ofReal (D.energyCap a q + c * D.mass a q) := by
        rw [ENNReal.ofReal_add hcap (mul_nonneg hc hm)]
        exact add_le_add he le_rfl

omit [CompleteSpace T] in
/-- The constructed output has exactly the expected global vacuum cost.
Normalization reduces the added mass term to one. -/
theorem prepared_energy_le (D : VectorData R Tr E μ) (J : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (J v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2)) :
    E'.expectation (prepareVectorData D J hpositive htrace hc henergy).output ≤
      ENNReal.ofReal ((∑' a, ∫ q, D.energyCap a q ∂μ) + c) := by
  have h := (prepareVectorData D J hpositive htrace hc henergy).output_energy_le
  convert h using 1
  congr 1
  simp only [prepareVectorData,
    integral_add (D.cap_integrable _) ((D.mass_integrable _).const_mul c), integral_const_mul]
  rw [D.cap_summable.tsum_add (D.normalized.summable.mul_left c),
    tsum_mul_left, D.normalized.tsum_eq, mul_one]

omit [CompleteSpace T] in
/-- The prepared output has zero soft energy when the standard vacuum
rank-one form evaluation vanishes. This holds for the very same output
whose full energy and marginal are evaluated below. -/
theorem prepared_soft_energy_zero (D : VectorData R Tr E μ) (J : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (J v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2))
    (F : PositiveForm Tr') (hzero : ∀ v, F.expectation (S.rankOne (J v)) = 0) :
    F.expectation (prepareVectorData D J hpositive htrace hc henergy).output = 0 := by
  let D' := prepareVectorData D J hpositive htrace hc henergy
  change F.expectation D'.output = 0
  rw [VectorData.output, F.expectation_aggregate D'.conditional_integrable
    D'.conditional_positive D'.conditional_norm_summable]
  have hlocal (a : ℕ) : ∀ᵐ q ∂μ, F.expectation (D'.conditional a q) = 0 := by
    filter_upwards [D'.mass_sum a] with q hq
    rw [VectorData.conditional, Repair.rankOneSeries_expectation S F hpositive hq]
    simp only [D', prepareVectorData, hzero, tsum_zero]
  simp only [lintegral_congr_ae (hlocal _), lintegral_zero, tsum_zero]

/-- The vector construction agrees with ordinary trace-class vacuum
pushforward whenever its standard rank-one identity is supplied. -/
theorem prepared_output_eq (D : VectorData R Tr E μ) (J : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (J v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2))
    (P : T →L[ℝ] U) (hP : ∀ v, P (R.rankOne v) = S.rankOne (J v)) :
    (prepareVectorData D J hpositive htrace hc henergy).output = P D.output := by
  rw [← (P.hasSum D.output_hasSum).tsum_eq]
  unfold VectorData.output aggregate
  apply tsum_congr
  intro a
  rw [← P.integral_comp_comm (D.conditional_integrable a)]
  apply integral_congr_ae
  filter_upwards [D.mass_sum a] with q hq
  change (∑' k, S.rankOne (J (D.vector a k q))) =
    P (∑' k, R.rankOne (D.vector a k q))
  rw [P.map_tsum (Repair.rankOneSeries_hasSum R hq).summable]
  exact tsum_congr (fun k => (hP _).symm)

/-- Every bounded marginal is transported on the same constructed output.
The map identity is the standard partial-trace compatibility of vacuum
preparation, rather than an equality asserted of the final state. -/
theorem prepared_marginal {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VectorData R Tr E μ) (J : K →ₗᵢ[ℂ] H)
    (hpositive : S.positive ⊆ Tr'.positive) (htrace : S.trace = Tr'.trace)
    {c : ℝ} (hc : 0 ≤ c)
    (henergy : ∀ v, E.expectation (R.rankOne v) < ⊤ →
      E'.expectation (S.rankOne (J v)) ≤
        E.expectation (R.rankOne v) + ENNReal.ofReal (c * ‖v‖ ^ 2))
    (P : T →L[ℝ] U) (hP : ∀ v, P (R.rankOne v) = S.rankOne (J v))
    (M : U →L[ℝ] F) (Mhard : T →L[ℝ] F) (hM : M.comp P = Mhard) :
    M (prepareVectorData D J hpositive htrace hc henergy).output = Mhard D.output := by
  rw [prepared_output_eq D J hpositive htrace hc henergy P hP]
  exact congrArg (fun L : T →L[ℝ] F => L D.output) hM

end OperatorPreparation
end GptLean.RemovalVacuum
