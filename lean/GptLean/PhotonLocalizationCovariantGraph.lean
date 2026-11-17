import GptLean.PhotonLocalizationKineticChannel
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
Full covariant graph identities from a dense reference-form core.

The candidate derivative is the actual Kraus image of the source
derivative and field correction, plus the discarded-vacuum vector.
Continuity in the reference-form norm and closedness of the physical
covariant operators prove its domain and derivative at every source.
The universal kinetic graph formula then evaluates every Kraus vector.
No full-domain localized graph or coordinate energy identity is assumed.
-/

namespace GptLean.PhotonLocalization

open Filter Topology
open PhotonLocalizationChannel
open scoped InnerProductSpace ENNReal

section Graph

variable {Q H : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A closed graph identity between bounded maps extends from a dense
reference-form core. Density is in the reference norm, so both the
vector and its proposed covariant derivative converge. -/
theorem closed_graph_of_dense_reference
    (D : H →ₗ.[ℂ] H) (hD : D.IsClosed)
    (inclusion derivative : Q →L[ℂ] H) (core : Set Q) (hdense : Dense core)
    (hcore : ∀ q ∈ core, (inclusion q, derivative q) ∈ D.graph) (q : Q) :
    (inclusion q, derivative q) ∈ D.graph := by
  have hclosed : IsClosed {q : Q | (inclusion q, derivative q) ∈ D.graph} := by
    change IsClosed (D.graph : Set (H × H)) at hD
    exact hD.preimage (inclusion.continuous.prodMk derivative.continuous)
  have hclosure := closure_minimal hcore hclosed
  rw [hdense.closure_eq] at hclosure
  exact hclosure (Set.mem_univ q)

end Graph

section Dilation

variable {Q H T ι : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T] [Fintype ι]
  {A : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}

/-- The proposed derivative in the actual dilation Hilbert space. -/
noncomputable def covariantDilationDerivative
    (U : KrausIsometry H) (derivative ann cre : Q →L[ℂ] H)
    (noise : Q →L[ℂ] lp (fun _ : ℕ => H) 2) (charge : ℝ) :
    Q →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  U.toContinuousLinearMap.comp (derivative + (charge : ℂ) • (ann + cre)) + noise

/-- Coordinate evaluation is continuous, so each actual Kraus vector
inherits the closed covariant graph identity from the source core. -/
theorem kraus_covariant_graph_of_core
    (U : KrausIsometry H) (inclusion : Q →L[ℂ] H)
    (D : H →ₗ.[ℂ] H) (hD : D.IsClosed)
    (localized : Q →L[ℂ] lp (fun _ : ℕ => H) 2)
    (core : Set Q) (hdense : Dense core)
    (hcore : ∀ q ∈ core, ∀ k, (U (inclusion q) k, localized q k) ∈ D.graph)
    (q : Q) (k : ℕ) : (U (inclusion q) k, localized q k) ∈ D.graph := by
  exact closed_graph_of_dense_reference D hD
    (((lp.evalCLM ℂ (fun _ : ℕ => H) 2 k).comp U.toContinuousLinearMap).comp inclusion)
    ((lp.evalCLM ℂ (fun _ : ℕ => H) 2 k).comp localized)
    core hdense (fun q hq => hcore q hq k) q

/-- The finite derivative cap is a consequence of the reference graph
norm, with a constant independent of the source vector. -/
theorem reference_derivative_sum_bound (derivative : ι → Q →L[ℂ] H) (q : Q) :
    ∑ i, ‖derivative i q‖ ≤ (∑ i, ‖derivative i‖) * ‖q‖ := by
  simpa only [Finset.sum_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => (derivative i).le_opNorm q)

/-- Construct the sharp kinetic source witness from universal reference
graph data and an arbitrary-split covariant identity only on a dense core.
The localized domain and coordinate form evaluations are conclusions.
The field hypotheses are the ordinary annihilation, creation and vacuum
relations for the supplied kernels and operators. -/
noncomputable def KineticDilationSource.ofReferenceCore
    (kinetic controlForm : RemovalState.PositiveForm Tr)
    (U : KrausIsometry H) (inclusion radiation : Q →L[ℂ] H)
    (derivative ann cre : ι → Q →L[ℂ] H)
    (noise : ι → Q →L[ℂ] lp (fun _ : ℕ => H) 2)
    (D : ι → H →ₗ.[ℂ] H) (hclosed : ∀ i, (D i).IsClosed)
    (core : Set Q) (hdense : Dense core)
    (hsource : ∀ q ∈ core, ∀ i, (inclusion q, derivative i q) ∈ (D i).graph)
    (hkinetic : ∀ (v : H) (z : ι → H), (∀ i, (v, z i) ∈ (D i).graph) →
      kinetic.expectation (A.rankOne v) =
        ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖z i‖ ^ 2))
    (hcontrol : ∀ q, controlForm.expectation (A.rankOne (inclusion q)) =
      ENNReal.ofReal (‖q‖ ^ 2))
    (hinclusion : ‖inclusion‖ ≤ 1)
    (charge ε : ℝ)
    (hcore : ∀ q ∈ core, ∀ i k,
      (U (inclusion q) k,
        covariantDilationDerivative U (derivative i) (ann i) (cre i) (noise i) charge q k)
          ∈ (D i).graph)
    (hann : ∀ q i, ‖ann i q‖ ≤ ε * ‖radiation q‖)
    (hcre : ∀ q i, ‖cre i q‖ ^ 2 ≤ ‖ann i q‖ ^ 2 + ε ^ 2 * ‖inclusion q‖ ^ 2)
    (hnoise : ∀ q i, ‖noise i q‖ ^ 2 ≤ charge ^ 2 * ε ^ 2 * ‖inclusion q‖ ^ 2)
    (horthogonal : ∀ q i,
      ⟪U (derivative i q + (charge : ℂ) • (ann i q + cre i q)), noise i q⟫_ℂ = 0)
    (q : Q) :
    KineticDilationSource (A := A) (ι := ι) kinetic controlForm U (inclusion q)
      charge ε (2 * ‖radiation‖ + ‖inclusion‖) (∑ i, ‖derivative i‖) where
  control := ‖q‖ ^ 2
  control_nonneg := sq_nonneg _
  control_eq := hcontrol q
  derivative i := derivative i q
  annihilated i := ann i q
  created i := cre i q
  noise i := noise i q
  localized i := covariantDilationDerivative U (derivative i) (ann i) (cre i) (noise i) charge q
  radiationNorm := ‖radiation q‖
  massNorm := ‖inclusion q‖
  radiationNorm_nonneg := norm_nonneg _
  massNorm_nonneg := norm_nonneg _
  annihilation i := hann q i
  creation i := hcre q i
  scale_le := by
    rw [Real.sqrt_sq (norm_nonneg q)]
    nlinarith only [radiation.le_opNorm q, inclusion.le_opNorm q]
  mass_le := by
    have hnorm : ‖inclusion q‖ ≤ ‖q‖ := by
      exact (inclusion.le_opNorm q).trans
        ((mul_le_mul_of_nonneg_right hinclusion (norm_nonneg q)).trans_eq (one_mul _))
    nlinarith only [hnorm, norm_nonneg (inclusion q), norm_nonneg q]
  derivative_le := by
    rw [Real.sqrt_sq (norm_nonneg q)]
    exact reference_derivative_sum_bound derivative q
  noise_le i := hnoise q i
  intertwining i := rfl
  orthogonality i := horthogonal q i
  original_form := hkinetic _ _ (fun i =>
    closed_graph_of_dense_reference (D i) (hclosed i) inclusion (derivative i)
      core hdense (fun r hr => hsource r hr i) q)
  coordinate_form k := hkinetic _ _ (fun i =>
    kraus_covariant_graph_of_core U inclusion (D i) (hclosed i)
      (covariantDilationDerivative U (derivative i) (ann i) (cre i) (noise i) charge)
      core hdense (fun r hr a => hcore r hr i a) q k)

end Dilation

end GptLean.PhotonLocalization
