import GptLean.SymmetricLift.RecursiveCharts
import GptLean.SymmetricLift.ChartExtension
import GptLean.SymmetricLift.Targets
import GptLean.SymmetricLift.GluingProperties

/-!
Concrete recursive chart families for the full particle-number construction.
Every local operator is built from lower-particle operators by coordinate
restriction, finite tensor product, completion and fixed tensor reindexing.
The tensor reindexing is independent of all local operator families.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift
open UniformSpace TopologicalSpace
open scoped ContDiff BigOperators

/-- Real scalar multiplication on complex operators is continuous, including
the bounded-convergence topology used by the general derivative API. -/
instance complexOperator_continuousSMul_real {A C : Type}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] :
    ContinuousSMul ℝ (A →L[ℂ] C) := by
  constructor
  have hc := (Complex.continuous_ofReal.comp
    (continuous_fst : Continuous (Prod.fst : ℝ × (A →L[ℂ] C) → ℝ))).smul continuous_snd
  change Continuous (fun p : ℝ × (A →L[ℂ] C) => (p.1 : ℂ) • p.2) at hc
  simpa only [Complex.coe_smul] using hc

section GlobalDefinition
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]

/-- Operator data retained by the particle-number recursion. -/
structure LiftCandidate (B : TensorBackground V) (n : ℕ) where
  target : TensorHilbert
  operator : Configuration n → B.H n →L[ℂ] target
  fixedOperator : B.H n →L[ℂ] target

/-- The qualitative properties of a constructed candidate. These are output
properties of the recursion, not background tensor assumptions. -/
structure SmoothLiftProperties (B : TensorBackground V) (n : ℕ)
    (L : LiftCandidate B n) : Prop where
  smooth : ContDiffOn ℝ ∞ L.operator (distinctConfigurations n)
  norm : ∀ x ∈ distinctConfigurations n, ∀ u, ‖L.operator x u‖ = ‖u‖
  equivariant : ∀ (π : Equiv.Perm (Fin n)) x, x ∈ distinctConfigurations n → ∀ u,
    L.operator (permuteConfiguration π x) (B.R n π u) = L.operator x u
  fixed : ∀ x ∈ distinctConfigurations n, ∀ u, L.operator x (B.P n u) = L.fixedOperator u
  flat : ∀ x ∈ distinctConfigurations n, ∀ d u v,
    inner ℂ (L.operator x u) (fderiv ℝ L.operator x d v) = 0

variable (B : TensorBackground V) (N : ℕ) (lower : ∀ n, LiftCandidate B n)

def liftChartRepresentation : ChartRepresentation (Equiv.Perm (Fin N)) (Configuration N) (B.H N) where
  base := configurationRepresentation N
  fiber := B.R N

abbrev liftChartTarget (a : (centeredAtlas N).charts) :=
  Completion (ChartBlockTarget (fun n => (lower n).target) (a.val : Configuration N))

abbrev liftCommonTarget := PiLp 2 (fun a : (centeredAtlas N).charts => liftChartTarget B N lower a)

/-- Local chart operators are the explicitly constructed completed lower-N tensor products. -/
def liftLocalChart (a : (centeredAtlas N).charts) (x : Configuration N) :
    B.H N →L[ℂ] liftChartTarget B N lower a :=
  recursiveChartFamily (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator) (a.val : Configuration N) (B.regroup (a.val : Configuration N)) x

theorem liftLocalChart_smooth (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) :
    ContDiffOn ℝ ∞ (liftLocalChart B N lower a) (distinctConfigurations N) :=
  recursiveChartFamily_smooth (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator) _ a.val.property _ (fun n hn => (ih n hn).smooth)

theorem liftLocalChart_norm (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (u : B.H N) : ‖liftLocalChart B N lower a x u‖ = ‖u‖ :=
  recursiveChartFamily_norm (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator) _ a.val.property _ (fun n hn => (ih n hn).norm) hx u

theorem liftLocalChart_flat (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (d : Configuration N) (u v : B.H N) :
    inner ℂ (liftLocalChart B N lower a x u)
      (fderiv ℝ (liftLocalChart B N lower a) x d v) = 0 :=
  recursiveChartFamily_flat (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator) _ a.val.property _ (fun n hn => (ih n hn).smooth)
    (fun n hn => (ih n hn).flat) hx d u v

theorem liftLocalChart_equivariant (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) (π : Equiv.Perm (Fin N))
    (hπ : permuteConfiguration π (a.val : Configuration N) = a.val)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) (u : B.H N) :
    liftLocalChart B N lower a (permuteConfiguration π x) (B.R N π u) =
      liftLocalChart B N lower a x u := by
  apply recursiveChartFamily_equivariant (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator)
    (fun n σ => (B.R n σ).toLinearIsometry.toContinuousLinearMap)
    (a.val : Configuration N) a.val.property (B.regroup (a.val : Configuration N))
    (fun n hn σ y hy z => (ih n hn).equivariant σ y hy z) π hπ ?_ hx u
  intro z
  rw [algebraicBlockPermutation,
    blockTensorFamily_const_eq _ _ _ _ (a.val : Configuration N) (0 : ℝ)]
  exact B.regroup_permutation _ π hπ z

def liftOrbitDomain (a : (centeredAtlas N).charts) : Set (Configuration N) :=
  (liftChartRepresentation B N).orbitDomain ((centeredAtlas N).chartDomain a)

theorem liftOrbitDomain_isOpen (hN : 2 ≤ N) (a : (centeredAtlas N).charts) :
    IsOpen (liftOrbitDomain B N a) :=
  (liftChartRepresentation B N).orbitDomain_isOpen ((centeredAtlas N).chartDomain_isOpen hN a)

theorem liftWeight_support (hN : 2 ≤ N) (a : (centeredAtlas N).charts) :
    tsupport ((centeredAtlas N).configurationWeights a) ∩ distinctConfigurations N ⊆
      liftOrbitDomain B N a := by
  intro x hx
  obtain ⟨π, hπ⟩ := (centeredAtlas N).configurationWeights_support hN a hx
  refine ⟨π⁻¹, ?_⟩
  change permuteConfiguration ((π⁻¹)⁻¹) x ∈ (centeredAtlas N).chartDomain a
  simpa only [inv_inv] using hπ

theorem liftChart_separated (a : (centeredAtlas N).charts)
    (π σ : Equiv.Perm (Fin N)) (x : Configuration N)
    (hπ : (liftChartRepresentation B N).base π⁻¹ x ∈ (centeredAtlas N).chartDomain a)
    (hσ : (liftChartRepresentation B N).base σ⁻¹ x ∈ (centeredAtlas N).chartDomain a) :
    π⁻¹ * σ ∈ (liftChartRepresentation B N).baseStabilizer (a.val : Configuration N) :=
  (centeredAtlas N).chartDomain_separated a π σ x hπ hσ

/-- The stabilizer-compatible orbit extension is constructed by the proved chart extension. -/
def liftExtendedChart (a : (centeredAtlas N).charts) (x : Configuration N) :
    B.H N →L[ℂ] liftChartTarget B N lower a :=
  (liftChartRepresentation B N).chartExtension ((centeredAtlas N).chartDomain a)
    (liftLocalChart B N lower a) x

theorem liftExtendedChart_smooth (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n)) (a : (centeredAtlas N).charts) :
    ContDiffOn ℝ ∞ (liftExtendedChart B N lower a) (liftOrbitDomain B N a) := by
  apply (liftChartRepresentation B N).chartExtension_contDiffOn
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) ((centeredAtlas N).chartDomain_isOpen hN a)
    (liftChart_separated B N a)
  · intro π hπ y hy u
    exact liftLocalChart_equivariant B N lower ih a π hπ hy.1 u
  · exact (liftLocalChart_smooth B N lower ih a).mono (fun _ hy => hy.1)

theorem liftExtendedChart_norm (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (u : B.H N) : ‖liftExtendedChart B N lower a x u‖ = ‖u‖ := by
  apply (liftChartRepresentation B N).chartExtension_norm
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) (liftChart_separated B N a)
  · intro π hπ y hy v
    exact liftLocalChart_equivariant B N lower ih a π hπ hy.1 v
  · intro y hy v
    exact liftLocalChart_norm B N lower ih a hy.1 v
  · exact hx

theorem liftExtendedChart_equivariant (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (π : Equiv.Perm (Fin N)) (u : B.H N) :
    liftExtendedChart B N lower a (permuteConfiguration π x) (B.R N π u) =
      liftExtendedChart B N lower a x u := by
  apply (liftChartRepresentation B N).chartExtension_equivariant
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) (liftChart_separated B N a)
  · intro σ hσ y hy v
    exact liftLocalChart_equivariant B N lower ih a σ hσ hy.1 v
  · exact hx

theorem liftExtendedChart_flat (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (d : Configuration N) (u v : B.H N) :
    inner ℂ (liftExtendedChart B N lower a x u)
      (fderiv ℝ (liftExtendedChart B N lower a) x d v) = 0 := by
  apply (liftChartRepresentation B N).chartExtension_flat
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) ((centeredAtlas N).chartDomain_isOpen hN a)
    (liftChart_separated B N a)
  · intro π hπ y hy w
    exact liftLocalChart_equivariant B N lower ih a π hπ hy.1 w
  · exact ((liftLocalChart_smooth B N lower ih a).mono
      (fun _ hy => hy.1)).differentiableOn (by simp)
  · intro y hy d z w
    exact liftLocalChart_flat B N lower ih a hy.1 d z w
  · exact hx

def liftLocalFixedOperator (a : (centeredAtlas N).charts) :
    B.H N →L[ℂ] liftChartTarget B N lower a :=
  (transportCompleteOperator (B.regroup (a.val : Configuration N))
    (algebraicChartConstant (fun n => B.H n) (fun n => (lower n).target)
      (fun n => (lower n).fixedOperator) (a.val : Configuration N))).comp (B.P N)

theorem liftLocalChart_fixed (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (u : B.H N) :
    liftLocalChart B N lower a x (B.P N u) = liftLocalFixedOperator B N lower a u :=
  recursiveChartFamily_fixed (fun n => B.H n) (fun n => (lower n).target)
    (fun n => (lower n).operator) B.P (fun n => (lower n).fixedOperator)
    _ a.val.property _ (fun n hn => (ih n hn).fixed)
    (B.regroup_projection (a.val : Configuration N)) hx u

theorem liftExtendedChart_fixed (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (u : B.H N) :
    liftExtendedChart B N lower a x (B.P N u) = liftLocalFixedOperator B N lower a u := by
  apply (liftChartRepresentation B N).chartExtension_fixed
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) (liftChart_separated B N a)
  · intro π hπ y hy w
    exact liftLocalChart_equivariant B N lower ih a π hπ hy.1 w
  · exact B.projection_right N
  · intro y hy w
    exact liftLocalChart_fixed B N lower ih a hy.1 w
  · exact hx

/-- Heterogeneous chart targets embed isometrically into their actual finite Hilbert sum. -/
def liftUniformChart (a : (centeredAtlas N).charts) (x : Configuration N) :
    B.H N →L[ℂ] liftCommonTarget B N lower := by
  classical
  exact (chartTargetEmbedding (fun a => liftChartTarget B N lower a) a).toContinuousLinearMap.comp
    (liftExtendedChart B N lower a x)

def liftTargetPostcomposeComplex (a : (centeredAtlas N).charts) :
    (B.H N →L[ℂ] liftChartTarget B N lower a) →L[ℂ]
      (B.H N →L[ℂ] liftCommonTarget B N lower) := by
  classical
  exact ContinuousLinearMap.compL ℂ (B.H N) (liftChartTarget B N lower a)
    (liftCommonTarget B N lower)
    (chartTargetEmbedding (fun a => liftChartTarget B N lower a) a).toContinuousLinearMap

def liftTargetPostcompose (a : (centeredAtlas N).charts) :
    (B.H N →L[ℂ] liftChartTarget B N lower a) →L[ℝ]
      (B.H N →L[ℂ] liftCommonTarget B N lower) :=
  (liftTargetPostcomposeComplex B N lower a).restrictScalars ℝ

theorem liftTargetPostcompose_hasFDerivAt (a : (centeredAtlas N).charts)
    (L : B.H N →L[ℂ] liftChartTarget B N lower a) :
    HasFDerivAt (liftTargetPostcompose B N lower a) (liftTargetPostcompose B N lower a) L := by
  have hc : HasFDerivAt (liftTargetPostcomposeComplex B N lower a)
      (liftTargetPostcomposeComplex B N lower a) L :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ)
      (E := B.H N →L[ℂ] liftChartTarget B N lower a)
      (F := B.H N →L[ℂ] liftCommonTarget B N lower)
      (liftTargetPostcomposeComplex B N lower a)
  exact HasFDerivAt.restrictScalars (𝕜' := ℂ)
    (E := B.H N →L[ℂ] liftChartTarget B N lower a)
    (F := B.H N →L[ℂ] liftCommonTarget B N lower) ℝ hc

theorem liftUniformChart_smooth (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n)) (a : (centeredAtlas N).charts) :
    ContDiffOn ℝ ∞ (liftUniformChart B N lower a) (liftOrbitDomain B N a) := by
  have hc : ContDiff ℝ ∞ (liftTargetPostcompose B N lower a) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := B.H N →L[ℂ] liftChartTarget B N lower a)
      (F := B.H N →L[ℂ] liftCommonTarget B N lower) (n := ∞)
      (liftTargetPostcomposeComplex B N lower a)).restrict_scalars ℝ
  exact hc.comp_contDiffOn (liftExtendedChart_smooth B N lower hN ih a)

theorem liftUniformChart_norm (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (u : B.H N) : ‖liftUniformChart B N lower a x u‖ = ‖u‖ := by
  classical
  change ‖chartTargetEmbedding (fun a => liftChartTarget B N lower a) a
    (liftExtendedChart B N lower a x u)‖ = ‖u‖
  rw [(chartTargetEmbedding _ a).norm_map]
  exact liftExtendedChart_norm B N lower ih a hx u

theorem liftUniformChart_inner (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (u v : B.H N) :
    inner ℂ (liftUniformChart B N lower a x u) (liftUniformChart B N lower a x v) = inner ℂ u v :=
  (show B.H N →ₗᵢ[ℂ] liftCommonTarget B N lower from
    ⟨(liftUniformChart B N lower a x).toLinearMap,
      liftUniformChart_norm B N lower ih a hx⟩).inner_map_map u v

theorem liftUniformChart_equivariant (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (π : Equiv.Perm (Fin N)) (u : B.H N) :
    liftUniformChart B N lower a (permuteConfiguration π x) (B.R N π u) =
      liftUniformChart B N lower a x u := by
  classical
  change chartTargetEmbedding _ a (liftExtendedChart B N lower a (permuteConfiguration π x)
    (B.R N π u)) = chartTargetEmbedding _ a (liftExtendedChart B N lower a x u)
  rw [liftExtendedChart_equivariant B N lower ih a hx π u]

theorem liftUniformChart_flat (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (d : Configuration N) (u v : B.H N) :
    inner ℂ (liftUniformChart B N lower a x u)
      (fderiv ℝ (liftUniformChart B N lower a) x d v) = 0 := by
  classical
  have hdiff := ((liftExtendedChart_smooth B N lower hN ih a).contDiffAt
    ((liftOrbitDomain_isOpen B N hN a).mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt (liftUniformChart B N lower a)
      ((liftTargetPostcompose B N lower a).comp (fderiv ℝ (liftExtendedChart B N lower a) x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := Configuration N)
      (F := B.H N →L[ℂ] liftChartTarget B N lower a)
      (G := B.H N →L[ℂ] liftCommonTarget B N lower) x
      (liftTargetPostcompose_hasFDerivAt B N lower a (liftExtendedChart B N lower a x)) hdiff.hasFDerivAt
  rw [hd.fderiv]
  change inner ℂ (chartTargetEmbedding _ a (liftExtendedChart B N lower a x u))
    (chartTargetEmbedding _ a (fderiv ℝ (liftExtendedChart B N lower a) x d v)) = 0
  rw [chartTargetEmbedding_inner (liftChartTarget B N lower) a]
  exact liftExtendedChart_flat B N lower hN ih a hx d u v

theorem liftUniformChart_derivative_fixed (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (hx : x ∈ liftOrbitDomain B N a)
    (d : Configuration N) (u : B.H N) :
    fderiv ℝ (liftUniformChart B N lower a) x d (B.P N u) = 0 := by
  classical
  apply derivative_fixed_on_open (liftOrbitDomain_isOpen B N hN a) hx
    (((liftUniformChart_smooth B N lower hN ih a).contDiffAt
      ((liftOrbitDomain_isOpen B N hN a).mem_nhds hx)).differentiableAt (by simp))
    (B.P N)
    ((chartTargetEmbedding (fun a => liftChartTarget B N lower a) a).toContinuousLinearMap.comp
      (liftLocalFixedOperator B N lower a))
  intro y hy v
  change chartTargetEmbedding _ a (liftExtendedChart B N lower a y (B.P N v)) =
    chartTargetEmbedding _ a (liftLocalFixedOperator B N lower a v)
  rw [liftExtendedChart_fixed B N lower ih a hy v]

abbrev liftStepTarget := GlueTarget (B.H N) (liftCommonTarget B N lower) (centeredAtlas N).charts

/-- The actual N-particle operator, built without assuming a local or global lift. -/
def liftStepOperator (x : Configuration N) : B.H N →L[ℂ] liftStepTarget B N lower :=
  smoothGlue (B.P N) (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => liftUniformChart B N lower a x)

theorem liftStepOperator_smooth (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n)) :
    ContDiffOn ℝ ∞ (liftStepOperator B N lower) (distinctConfigurations N) := by
  apply smoothGlue_contDiffOn_supported (B.P N) (distinctConfigurations_isOpen N)
    (liftOrbitDomain B N) (liftOrbitDomain_isOpen B N hN)
    (centeredAtlas N).configurationWeights (liftUniformChart B N lower)
    ((centeredAtlas N).configurationWeights_smooth hN)
  · intro a
    exact (liftUniformChart_smooth B N lower hN ih a).mono Set.inter_subset_right
  · exact liftWeight_support B N hN

theorem liftStepOperator_norm (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) (u : B.H N) :
    ‖liftStepOperator B N lower x u‖ = ‖u‖ := by
  apply smoothGlue_norm_supported (B.P N)
    (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => liftUniformChart B N lower a x) (fun a => x ∈ liftOrbitDomain B N a)
    (B.projection_orthogonal N) ((centeredAtlas N).configurationWeights_square hN hx)
  · intro a ha
    exact (weight_zero_outside_chart (fun hs => liftWeight_support B N hN a ⟨hs, hx⟩) ha).1
  · intro a ha v
    exact liftUniformChart_norm B N lower ih a ha v

theorem liftStepOperator_equivariant (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (π : Equiv.Perm (Fin N)) {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (u : B.H N) :
    liftStepOperator B N lower (permuteConfiguration π x) (B.R N π u) =
      liftStepOperator B N lower x u := by
  apply smoothGlue_equivariant_supported (B.P N) (B.R N π).toLinearIsometry.toContinuousLinearMap
    (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => (centeredAtlas N).configurationWeights a (permuteConfiguration π x))
    (fun a => liftUniformChart B N lower a x)
    (fun a => liftUniformChart B N lower a (permuteConfiguration π x))
    (fun a => x ∈ liftOrbitDomain B N a)
  · funext a
    exact (centeredAtlas N).configurationWeights_invariant a π x
  · exact B.projection_left N π
  · exact B.projection_right N π
  · intro a ha
    exact (weight_zero_outside_chart (fun hs => liftWeight_support B N hN a ⟨hs, hx⟩) ha).1
  · intro a ha v
    exact liftUniformChart_equivariant B N lower ih a ha π v

theorem liftStepOperator_flat (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (d : Configuration N) (u v : B.H N) :
    inner ℂ (liftStepOperator B N lower x u)
      (fderiv ℝ (liftStepOperator B N lower) x d v) = 0 := by
  apply smoothGlue_operator_flat_supported (B.P N) (liftOrbitDomain B N)
  · intro a
    exact (((centeredAtlas N).configurationWeights_smooth hN a).contDiffAt
      ((distinctConfigurations_isOpen N).mem_nhds hx)).differentiableAt (by simp)
  · intro a hs
    exact liftWeight_support B N hN a ⟨hs, hx⟩
  · intro a ha
    exact ((liftUniformChart_smooth B N lower hN ih a).contDiffAt
      ((liftOrbitDomain_isOpen B N hN a).mem_nhds ha)).differentiableAt (by simp)
  · exact ((liftStepOperator_smooth B N lower hN ih).contDiffAt
      ((distinctConfigurations_isOpen N).mem_nhds hx)).differentiableAt (by simp)
  · exact (centeredAtlas N).configurationWeights_flat hN hx
  · intro a ha w
    exact liftUniformChart_norm B N lower ih a ha w
  · intro d a ha z w
    exact liftUniformChart_flat B N lower hN ih a ha d z w

def liftStepCandidate : LiftCandidate B N where
  target := TensorHilbert.of (liftStepTarget B N lower)
  operator := liftStepOperator B N lower
  fixedOperator := smoothGlue (B.P N) (fun _ : (centeredAtlas N).charts => 0)
    (fun _ => (0 : B.H N →L[ℂ] liftCommonTarget B N lower))

theorem liftStepCandidate_fixed (x : Configuration N) (u : B.H N) :
    (liftStepCandidate B N lower).operator x (B.P N u) =
      (liftStepCandidate B N lower).fixedOperator u := by
  change smoothGlue (B.P N)
    (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => liftUniformChart B N lower a x) (B.P N u) =
    smoothGlue (B.P N) (fun _ : (centeredAtlas N).charts => 0)
      (fun _ => (0 : B.H N →L[ℂ] liftCommonTarget B N lower)) u
  rw [smoothGlue_fixed _ _ _ (B.projection_idempotent N), smoothGlue_apply]
  simp only [glue, Complex.ofReal_zero, zero_smul]
  rfl

theorem liftStepCandidate_properties (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n)) :
    SmoothLiftProperties B N (liftStepCandidate B N lower) where
  smooth := liftStepOperator_smooth B N lower hN ih
  norm := fun _ hx u => liftStepOperator_norm B N lower hN ih hx u
  equivariant := fun π _ hx u => liftStepOperator_equivariant B N lower hN ih π hx u
  fixed := fun x _ u => liftStepCandidate_fixed B N lower x u
  flat := fun _ hx d u v => liftStepOperator_flat B N lower hN ih hx d u v

theorem liftStepTarget_complete : CompleteSpace (liftStepTarget B N lower) := by
  infer_instance

theorem liftStepTarget_separable
    (hK : ∀ n, SeparableSpace (lower n).target) : SeparableSpace (liftStepTarget B N lower) := by
  letI := hK
  haveI (a : (centeredAtlas N).charts) : SeparableSpace (liftChartTarget B N lower a) := by
    letI := blockTensor_separable
      (fun c : PositionClasses (a.val : Configuration N) =>
        (lower (blockSize (a.val : Configuration N) c)).target)
      (coincidenceBlockList (a.val : Configuration N))
    infer_instance
  infer_instance

theorem liftStepTarget_finiteDimensional (hV : FiniteDimensional ℂ V)
    (hK : ∀ n, FiniteDimensional ℂ (lower n).target) :
    FiniteDimensional ℂ (liftStepTarget B N lower) := by
  letI := hV
  letI := hK
  letI := B.finiteDimensional N hV
  haveI (a : (centeredAtlas N).charts) : FiniteDimensional ℂ (liftChartTarget B N lower a) := by
    letI := blockTensor_finiteDimensional
      (fun c : PositionClasses (a.val : Configuration N) =>
        (lower (blockSize (a.val : Configuration N) c)).target)
      (coincidenceBlockList (a.val : Configuration N))
    exact completion_finiteDimensional
  infer_instance

def identityLiftCandidate (n : ℕ) : LiftCandidate B n where
  target := B.H n
  operator := fun _ => ContinuousLinearMap.id ℂ (B.H n)
  fixedOperator := ContinuousLinearMap.id ℂ (B.H n)

theorem identityLiftCandidate_properties (n : ℕ) (hn : n ≤ 1) :
    SmoothLiftProperties B n (identityLiftCandidate B n) where
  smooth := contDiffOn_const
  norm := fun _ _ _ => rfl
  equivariant := by
    intro π x hx u
    change B.R n π u = u
    have h := B.projection_right n π u
    simpa only [B.projection_small n hn, ContinuousLinearMap.id_apply] using h
  fixed := by
    intro x hx u
    simp only [identityLiftCandidate, B.projection_small n hn, ContinuousLinearMap.id_apply]
  flat := by
    intro x hx d u v
    change inner ℂ u
      (fderiv ℝ (fun _ : Configuration n => ContinuousLinearMap.id ℂ (B.H n)) x d v) = 0
    rw [fderiv_const_apply]
    change inner ℂ u 0 = 0
    exact inner_zero_right u

/-- A genuine strong recursion constructs the operators and their Hilbert
targets for every particle number. Only smaller coincidence blocks are used
by the tensor formulas in each nontrivial branch. -/
def recursiveLiftCandidate (n : ℕ) : LiftCandidate B n :=
  Nat.strongRecOn n (fun m ih =>
    if m ≤ 1 then identityLiftCandidate B m else
      liftStepCandidate B m (fun k => if hk : k < m then ih k hk else identityLiftCandidate B k))

theorem recursiveLiftCandidate_eq (n : ℕ) :
    recursiveLiftCandidate B n =
      if n ≤ 1 then identityLiftCandidate B n else
        liftStepCandidate B n (fun k => if k < n then recursiveLiftCandidate B k else identityLiftCandidate B k) := by
  unfold recursiveLiftCandidate Nat.strongRecOn
  rw [WellFounded.fix_eq]
  apply congrArg (fun f : ∀ k, LiftCandidate B k =>
    if n ≤ 1 then identityLiftCandidate B n else liftStepCandidate B n f)
  funext k
  split_ifs <;> rfl

/-- The constructed strong recursion satisfies all qualitative assertions of
the flat symmetric-isometry lemma. No inductive local family is an input. -/
theorem recursiveLiftCandidate_properties (n : ℕ) :
    SmoothLiftProperties B n (recursiveLiftCandidate B n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [recursiveLiftCandidate_eq]
    by_cases hn : n ≤ 1
    · rw [if_pos hn]
      exact identityLiftCandidate_properties B n hn
    · rw [if_neg hn]
      apply liftStepCandidate_properties B n _ (by omega)
      intro k hk
      simpa only [if_pos hk] using ih k hk

theorem recursiveLiftCandidate_complete (n : ℕ) :
    CompleteSpace (recursiveLiftCandidate B n).target := by
  have he := recursiveLiftCandidate_eq B n
  by_cases hn : n ≤ 1
  · rw [if_pos hn] at he
    exact Eq.mpr (congrArg (fun L : LiftCandidate B n => CompleteSpace L.target) he)
      (B.complete n)
  · rw [if_neg hn] at he
    exact Eq.mpr (congrArg (fun L : LiftCandidate B n => CompleteSpace L.target) he)
      (liftStepTarget_complete B n _)

theorem recursiveLiftCandidate_separable (n : ℕ) :
    SeparableSpace (recursiveLiftCandidate B n).target := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have he := recursiveLiftCandidate_eq B n
    by_cases hn : n ≤ 1
    · rw [if_pos hn] at he
      exact Eq.mpr (congrArg (fun L : LiftCandidate B n => SeparableSpace L.target) he)
        (B.separable n)
    · rw [if_neg hn] at he
      refine Eq.mpr (congrArg (fun L : LiftCandidate B n => SeparableSpace L.target) he) ?_
      apply liftStepTarget_separable B n _
      intro k
      by_cases hk : k < n
      · exact Eq.mpr (congrArg (fun L : LiftCandidate B k => SeparableSpace L.target)
          (if_pos hk : (if k < n then recursiveLiftCandidate B k else identityLiftCandidate B k) =
            recursiveLiftCandidate B k)) (ih k hk)
      · exact Eq.mpr (congrArg (fun L : LiftCandidate B k => SeparableSpace L.target)
          (if_neg hk : (if k < n then recursiveLiftCandidate B k else identityLiftCandidate B k) =
            identityLiftCandidate B k)) (B.separable k)

theorem recursiveLiftCandidate_finiteDimensional (hV : FiniteDimensional ℂ V) (n : ℕ) :
    FiniteDimensional ℂ (recursiveLiftCandidate B n).target := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have he := recursiveLiftCandidate_eq B n
    by_cases hn : n ≤ 1
    · rw [if_pos hn] at he
      exact Eq.mpr (congrArg (fun L : LiftCandidate B n => FiniteDimensional ℂ L.target) he)
        (B.finiteDimensional n hV)
    · rw [if_neg hn] at he
      refine Eq.mpr (congrArg (fun L : LiftCandidate B n => FiniteDimensional ℂ L.target) he) ?_
      apply liftStepTarget_finiteDimensional B n _ hV
      intro k
      by_cases hk : k < n
      · exact Eq.mpr (congrArg (fun L : LiftCandidate B k => FiniteDimensional ℂ L.target)
          (if_pos hk : (if k < n then recursiveLiftCandidate B k else identityLiftCandidate B k) =
            recursiveLiftCandidate B k)) (ih k hk)
      · exact Eq.mpr (congrArg (fun L : LiftCandidate B k => FiniteDimensional ℂ L.target)
          (if_neg hk : (if k < n then recursiveLiftCandidate B k else identityLiftCandidate B k) =
            identityLiftCandidate B k)) (B.finiteDimensional k hV)

end GlobalDefinition

end GptLean.SymmetricLift
