import GptLean.SymmetricLift.FullConstruction
import GptLean.SymmetricLift.GluingProperties
import GptLean.SymmetricLift.PermutationMetric
import GptLean.SymmetricLift.RemainderEstimate

/-! Quantitative derivative estimates for the explicitly recursive smooth lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift
open UniformSpace TopologicalSpace
open scoped BigOperators ContDiff NNReal

section CoordinateMetric
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
local instance fullMetricRealK : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K

def operatorCoordinateMetric {N : ℕ} (U : Configuration N → H →L[ℂ] K)
    (x : Configuration N) (u : H) : ℝ :=
  ∑ q : Fin N × Fin 3, ‖fderiv ℝ U x (EuclideanSpace.single q 1) u‖ ^ 2

theorem operatorCoordinateMetric_nonneg {N : ℕ} (U : Configuration N → H →L[ℂ] K)
    (x : Configuration N) (u : H) : 0 ≤ operatorCoordinateMetric U x u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
end CoordinateMetric

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [SeparableSpace V]
variable (B : TensorBackground V)

theorem configurationTensor_permute (t : EuclideanSpace ℝ (Fin 3) → V)
    {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    configurationTensor B t (permuteConfiguration π x) = B.R N π (configurationTensor B t x) := by
  unfold configurationTensor
  simp only [particle_permute]
  exact B.pure_permutation N π (fun i => t (particle x i))

theorem block_pairEnergy_le {N : ℕ} (c : Configuration N) (a : PositionClasses c)
    (x : Configuration N) : pairEnergy (blockConfiguration c a x) ≤ pairEnergy x := by
  let f : Fin (blockSize c a) ↪ Fin N :=
    (blockEnumeration c a).symm.toEmbedding.trans (Function.Embedding.subtype _)
  apply pairEnergy_embedding _ _ f
  intro i
  ext μ
  rfl

variable (N : ℕ) (lower : ∀ n, LiftCandidate B n)

/-- The exact local coordinate metric follows from tensor orthogonality and
the concrete coordinate restriction, with no block-count loss. -/
theorem liftLocalChart_coordinate_metric
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1) :
    operatorCoordinateMetric (liftLocalChart B N lower a) x (configurationTensor B t x) =
      ∑ c : PositionClasses (a.val : Configuration N),
        operatorCoordinateMetric (lower (blockSize (a.val : Configuration N) c)).operator
          (blockConfiguration (a.val : Configuration N) c x)
          (configurationTensor B t (blockConfiguration (a.val : Configuration N) c x)) := by
  let centerPoint : Configuration N := a.val
  let z (c : PositionClasses centerPoint) :=
    configurationTensor B t (blockConfiguration centerPoint c x)
  have hz (c : PositionClasses centerPoint) : ‖z c‖ = 1 :=
    B.pure_unit _ _ (fun _ => ht _)
  have he : B.regroup centerPoint (configurationTensor B t x) =
      (blockTensorVector (fun c : PositionClasses centerPoint => B.H (blockSize centerPoint c)) z
        (coincidenceBlockList centerPoint) : Completion (ChartBlockDomain (fun n => B.H n) centerPoint)) := by
    exact B.regroup_pure centerPoint _
  have hq (q : Fin N × Fin 3) :
      ‖fderiv ℝ (liftLocalChart B N lower a) x (EuclideanSpace.single q 1)
        (configurationTensor B t x)‖ ^ 2 =
      ∑ c : PositionClasses centerPoint,
        ‖fderiv ℝ (lower (blockSize centerPoint c)).operator
          (blockConfiguration centerPoint c x)
          (blockConfiguration centerPoint c (EuclideanSpace.single q 1)) (z c)‖ ^ 2 := by
    change ‖fderiv ℝ
      (recursiveChartFamily (fun n => B.H n) (fun n => (lower n).target)
        (fun n => (lower n).operator) centerPoint (B.regroup centerPoint))
      x (EuclideanSpace.single q 1) (configurationTensor B t x)‖ ^ 2 = _
    have h := recursiveChartFamily_metric (fun n => B.H n) (fun n => (lower n).target)
      (fun n => (lower n).operator) centerPoint a.val.property (B.regroup centerPoint)
      (fun n hn => (ih n hn).smooth) (fun n hn => (ih n hn).norm)
      (fun n hn => (ih n hn).flat) hx z hz (configurationTensor B t x) he
      (EuclideanSpace.single q 1)
    simpa only [coincidenceBlockList, Finset.sum_map_toList] using h
  unfold operatorCoordinateMetric
  simp_rw [hq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  let L := ((ContinuousLinearMap.apply ℂ (lower (blockSize centerPoint c)).target (z c)).restrictScalars ℝ).comp
    (fderiv ℝ (lower (blockSize centerPoint c)).operator (blockConfiguration centerPoint c x))
  exact blockConfiguration_coordinate_metric centerPoint c L

/-- The property quantified in the metric induction. Pair control is available
without a Lipschitz hypothesis, and Lipschitz control gives the second bound. -/
structure LiftMetricProperties (n : ℕ) (L : LiftCandidate B n) (b : ℝ) : Prop where
  nonneg : 0 ≤ b
  pair : ∀ x ∈ distinctConfigurations n, ∀ t : EuclideanSpace ℝ (Fin 3) → V,
    (∀ y, ‖t y‖ = 1) →
    operatorCoordinateMetric L.operator x (configurationTensor B t x) ≤ b * pairEnergy x
  lipschitz : ∀ x ∈ distinctConfigurations n, ∀ t : EuclideanSpace ℝ (Fin 3) → V,
    (∀ y, ‖t y‖ = 1) → ∀ C : ℝ≥0, LipschitzWith C t →
    operatorCoordinateMetric L.operator x (configurationTensor B t x) ≤ b * (C : ℝ) ^ 2

def chartMetricConstant (b : ℕ → ℝ) (a : (centeredAtlas N).charts) : ℝ :=
  ∑ c : PositionClasses (a.val : Configuration N), b (blockSize (a.val : Configuration N) c)

theorem liftLocalChart_pair_bound (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1) :
    operatorCoordinateMetric (liftLocalChart B N lower a) x (configurationTensor B t x) ≤
      chartMetricConstant N b a * pairEnergy x := by
  rw [liftLocalChart_coordinate_metric B N lower ih a hx t ht]
  unfold chartMetricConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  have hc := classBlock_card_lt a.val.property c
  exact ((ihm _ hc).pair _ (blockConfiguration_distinct _ _ hx) t ht).trans
    (mul_le_mul_of_nonneg_left (block_pairEnergy_le _ _ x) (ihm _ hc).nonneg)

theorem liftLocalChart_lipschitz_bound (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ distinctConfigurations N)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    (C : ℝ≥0) (hC : LipschitzWith C t) :
    operatorCoordinateMetric (liftLocalChart B N lower a) x (configurationTensor B t x) ≤
      chartMetricConstant N b a * (C : ℝ) ^ 2 := by
  rw [liftLocalChart_coordinate_metric B N lower ih a hx t ht]
  unfold chartMetricConstant
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun c _ =>
    (ihm _ (classBlock_card_lt a.val.property c)).lipschitz _ (blockConfiguration_distinct _ _ hx) t ht C hC)

theorem liftExtendedChart_metric_branch (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N} (π : Equiv.Perm (Fin N))
    (hπ : permuteConfiguration π⁻¹ x ∈ (centeredAtlas N).chartDomain a)
    (t : EuclideanSpace ℝ (Fin 3) → V) :
    operatorCoordinateMetric (liftExtendedChart B N lower a) x (configurationTensor B t x) =
      operatorCoordinateMetric (liftLocalChart B N lower a) (permuteConfiguration π⁻¹ x)
        (configurationTensor B t (permuteConfiguration π⁻¹ x)) := by
  have hv := ((liftLocalChart_smooth B N lower ih a).contDiffAt
    ((distinctConfigurations_isOpen N).mem_nhds hπ.1)).differentiableAt (by simp)
  have hd := (liftChartRepresentation B N).chartExtension_hasFDerivAt
    ((centeredAtlas N).chartDomain a)
    ((liftChartRepresentation B N).baseStabilizer (a.val : Configuration N))
    (liftLocalChart B N lower a) ((centeredAtlas N).chartDomain_isOpen hN a)
    (liftChart_separated B N a)
    (fun σ hσ y hy u => liftLocalChart_equivariant B N lower ih a σ hσ hy.1 u)
    (g := π) (x := x) hπ hv
  unfold operatorCoordinateMetric
  unfold liftExtendedChart
  rw [hd.fderiv]
  change (∑ q : Fin N × Fin 3,
    ‖fderiv ℝ (liftLocalChart B N lower a) (permuteConfiguration π⁻¹ x)
      (permuteConfiguration π⁻¹ (EuclideanSpace.single q 1))
      (B.R N π⁻¹ (configurationTensor B t x))‖ ^ 2) = _
  rw [← configurationTensor_permute]
  exact permuteConfiguration_coordinate_metric π⁻¹
    (fun d => fderiv ℝ (liftLocalChart B N lower a) (permuteConfiguration π⁻¹ x) d
      (configurationTensor B t (permuteConfiguration π⁻¹ x)))

theorem liftUniformChart_coordinate_metric (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ liftOrbitDomain B N a) (u : B.H N) :
    operatorCoordinateMetric (liftUniformChart B N lower a) x u =
      operatorCoordinateMetric (liftExtendedChart B N lower a) x u := by
  classical
  have hv := ((liftExtendedChart_smooth B N lower hN ih a).contDiffAt
    ((liftOrbitDomain_isOpen B N hN a).mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt (liftUniformChart B N lower a)
      ((liftTargetPostcompose B N lower a).comp (fderiv ℝ (liftExtendedChart B N lower a) x)) x :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := Configuration N)
      (F := B.H N →L[ℂ] liftChartTarget B N lower a)
      (G := B.H N →L[ℂ] liftCommonTarget B N lower) x
      (liftTargetPostcompose_hasFDerivAt B N lower a (liftExtendedChart B N lower a x)) hv.hasFDerivAt
  unfold operatorCoordinateMetric
  rw [hd.fderiv]
  change (∑ q : Fin N × Fin 3,
    ‖chartTargetEmbedding (fun a => liftChartTarget B N lower a) a
      (fderiv ℝ (liftExtendedChart B N lower a) x (EuclideanSpace.single q 1) u)‖ ^ 2) = _
  simp only [LinearIsometry.norm_map]

theorem liftUniformChart_pair_bound (hN : 2 ≤ N) (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ liftOrbitDomain B N a)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1) :
    operatorCoordinateMetric (liftUniformChart B N lower a) x (configurationTensor B t x) ≤
      chartMetricConstant N b a * pairEnergy x := by
  rw [liftUniformChart_coordinate_metric B N lower hN ih a hx]
  obtain ⟨π, hπ⟩ := hx
  change permuteConfiguration π⁻¹ x ∈ (centeredAtlas N).chartDomain a at hπ
  rw [liftExtendedChart_metric_branch B N lower hN ih a π hπ t]
  simpa only [pairEnergy_permute] using liftLocalChart_pair_bound B N lower b ih ihm a hπ.1 t ht

theorem liftUniformChart_lipschitz_bound (hN : 2 ≤ N) (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    (a : (centeredAtlas N).charts) {x : Configuration N}
    (hx : x ∈ liftOrbitDomain B N a)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    (C : ℝ≥0) (hC : LipschitzWith C t) :
    operatorCoordinateMetric (liftUniformChart B N lower a) x (configurationTensor B t x) ≤
      chartMetricConstant N b a * (C : ℝ) ^ 2 := by
  rw [liftUniformChart_coordinate_metric B N lower hN ih a hx]
  obtain ⟨π, hπ⟩ := hx
  change permuteConfiguration π⁻¹ x ∈ (centeredAtlas N).chartDomain a at hπ
  rw [liftExtendedChart_metric_branch B N lower hN ih a π hπ t]
  exact liftLocalChart_lipschitz_bound B N lower b ih ihm a hπ.1 t ht C hC

theorem liftStepOperator_coordinate_metric (hN : 2 ≤ N)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) (u : B.H N) :
    operatorCoordinateMetric (liftStepOperator B N lower) x u =
      (∑ q : Fin N × Fin 3, ∑ a : (centeredAtlas N).charts,
        (fderiv ℝ ((centeredAtlas N).configurationWeights a) x (EuclideanSpace.single q 1)) ^ 2) *
          ‖u - B.P N u‖ ^ 2 +
      ∑ a : (centeredAtlas N).charts, ((centeredAtlas N).configurationWeights a x) ^ 2 *
        operatorCoordinateMetric (liftUniformChart B N lower a) x u := by
  apply smoothGlue_operator_coordinate_metric (B.P N) (fun q => EuclideanSpace.single q 1)
    (liftOrbitDomain B N)
  · intro a
    exact (((centeredAtlas N).configurationWeights_smooth hN a).contDiffAt
      ((distinctConfigurations_isOpen N).mem_nhds hx)).differentiableAt (by simp)
  · intro a ha
    exact liftWeight_support B N hN a ⟨ha, hx⟩
  · intro a ha
    exact ((liftUniformChart_smooth B N lower hN ih a).contDiffAt
      ((liftOrbitDomain_isOpen B N hN a).mem_nhds ha)).differentiableAt (by simp)
  · exact ((liftStepOperator_smooth B N lower hN ih).contDiffAt
      ((distinctConfigurations_isOpen N).mem_nhds hx)).differentiableAt (by simp)
  · intro a ha v
    exact liftUniformChart_norm B N lower ih a ha v
  · intro d a ha v w
    exact liftUniformChart_flat B N lower hN ih a ha d v w
  · intro d a ha v
    exact liftUniformChart_derivative_fixed B N lower hN ih a ha d v

/-- All constants below depend only on the particle count and the chosen
geometric atlas, never on the one-particle Hilbert space or the map t. -/
def partitionMetricConstant : ℝ :=
  ((N : ℝ) * 3) * (4 * (centeredAtlas N).derivativeConstant * ‖center N‖ ^ 2)

theorem partitionMetricConstant_nonneg : 0 ≤ partitionMetricConstant N := by
  unfold partitionMetricConstant
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num))
    (mul_nonneg (mul_nonneg (by norm_num) (centeredAtlas N).derivativeConstant_nonneg) (sq_nonneg _))

theorem configurationWeights_coordinate_bound (hN : 2 ≤ N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (∑ q : Fin N × Fin 3, ∑ a : (centeredAtlas N).charts,
      (fderiv ℝ ((centeredAtlas N).configurationWeights a) x (EuclideanSpace.single q 1)) ^ 2) ≤
      partitionMetricConstant N * (‖center N x‖ ^ 2)⁻¹ := by
  apply (coordinate_partition_bound
    (fun a => fderiv ℝ ((centeredAtlas N).configurationWeights a) x)).trans
  have h := mul_le_mul_of_nonneg_left
    ((centeredAtlas N).configurationWeights_derivative_bound hN hx)
    (show 0 ≤ (N : ℝ) * 3 by positivity)
  simpa only [partitionMetricConstant, div_eq_mul_inv, mul_assoc] using h

def stepMetricConstant (b : ℕ → ℝ) : ℝ :=
  partitionMetricConstant N * max 4 ((N : ℝ) ^ 2) +
    ∑ a : (centeredAtlas N).charts, chartMetricConstant N b a

theorem chartMetricConstant_nonneg (b : ℕ → ℝ) (hb : ∀ n < N, 0 ≤ b n)
    (a : (centeredAtlas N).charts) : 0 ≤ chartMetricConstant N b a :=
  Finset.sum_nonneg (fun c _ => hb _ (classBlock_card_lt a.val.property c))

theorem stepMetricConstant_nonneg (b : ℕ → ℝ) (hb : ∀ n < N, 0 ≤ b n) :
    0 ≤ stepMetricConstant N b := by
  unfold stepMetricConstant
  apply add_nonneg
  · exact mul_nonneg (partitionMetricConstant_nonneg N) (le_trans (by norm_num) (le_max_left _ _))
  · exact Finset.sum_nonneg (fun a _ => chartMetricConstant_nonneg N b hb a)

theorem weighted_active_bound {ι : Type*} [Fintype ι]
    (χ E A : ι → ℝ) (active : ι → Prop) (m : ℝ) (hm : 0 ≤ m)
    (hχ : ∑ a, χ a ^ 2 = 1) (hA : ∀ a, 0 ≤ A a)
    (hzero : ∀ a, ¬ active a → χ a = 0)
    (hE : ∀ a, active a → E a ≤ A a * m) :
    (∑ a, χ a ^ 2 * E a) ≤ (∑ a, A a) * m := by
  calc
    _ ≤ ∑ a, χ a ^ 2 * ((∑ i, A i) * m) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : active a
      · exact mul_le_mul_of_nonneg_left ((hE a ha).trans
          (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ a)) hm)) (sq_nonneg _)
      · simp [hzero a ha]
    _ = _ := by rw [← Finset.sum_mul, hχ, one_mul]

theorem liftStepOperator_pair_bound (hN : 2 ≤ N) (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1) :
    operatorCoordinateMetric (liftStepOperator B N lower) x (configurationTensor B t x) ≤
      stepMetricConstant N b * pairEnergy x := by
  rw [liftStepOperator_coordinate_metric B N lower hN ih hx]
  have hcut := mul_le_mul_of_nonneg_right (configurationWeights_coordinate_bound N hN hx)
    (sq_nonneg (symmetryRemainder B t x))
  have hr := mul_le_mul_of_nonneg_left (symmetryRemainder_pair_bound B t ht hN hx)
    (partitionMetricConstant_nonneg N)
  have hc :
      (∑ q : Fin N × Fin 3, ∑ a : (centeredAtlas N).charts,
        (fderiv ℝ ((centeredAtlas N).configurationWeights a) x (EuclideanSpace.single q 1)) ^ 2) *
          symmetryRemainder B t x ^ 2 ≤
      (partitionMetricConstant N * max 4 ((N : ℝ) ^ 2)) * pairEnergy x := by
    apply hcut.trans
    calc
      _ = partitionMetricConstant N * ((‖center N x‖ ^ 2)⁻¹ * symmetryRemainder B t x ^ 2) := by ring
      _ ≤ partitionMetricConstant N * (4 * pairEnergy x) := hr
      _ ≤ (partitionMetricConstant N * max 4 ((N : ℝ) ^ 2)) * pairEnergy x := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pairEnergy_nonneg x))
          (partitionMetricConstant_nonneg N)
  have hl := weighted_active_bound
    (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => operatorCoordinateMetric (liftUniformChart B N lower a) x (configurationTensor B t x))
    (chartMetricConstant N b) (fun a => x ∈ liftOrbitDomain B N a) (pairEnergy x)
    (pairEnergy_nonneg x) ((centeredAtlas N).configurationWeights_square hN hx)
    (chartMetricConstant_nonneg N b (fun n hn => (ihm n hn).nonneg))
    (fun a ha => (weight_zero_outside_chart (fun hs => liftWeight_support B N hN a ⟨hs, hx⟩) ha).1)
    (fun a ha => liftUniformChart_pair_bound B N lower hN b ih ihm a ha t ht)
  exact (add_le_add hc hl).trans_eq (by unfold stepMetricConstant; ring)

theorem liftStepOperator_lipschitz_bound (hN : 2 ≤ N) (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n))
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    (C : ℝ≥0) (hC : LipschitzWith C t) :
    operatorCoordinateMetric (liftStepOperator B N lower) x (configurationTensor B t x) ≤
      stepMetricConstant N b * (C : ℝ) ^ 2 := by
  rw [liftStepOperator_coordinate_metric B N lower hN ih hx]
  have hcut := mul_le_mul_of_nonneg_right (configurationWeights_coordinate_bound N hN hx)
    (sq_nonneg (symmetryRemainder B t x))
  have hr := mul_le_mul_of_nonneg_left (symmetryRemainder_lipschitz_bound B t ht hC hN hx)
    (partitionMetricConstant_nonneg N)
  have hc :
      (∑ q : Fin N × Fin 3, ∑ a : (centeredAtlas N).charts,
        (fderiv ℝ ((centeredAtlas N).configurationWeights a) x (EuclideanSpace.single q 1)) ^ 2) *
          symmetryRemainder B t x ^ 2 ≤
      (partitionMetricConstant N * max 4 ((N : ℝ) ^ 2)) * (C : ℝ) ^ 2 := by
    apply hcut.trans
    calc
      _ = partitionMetricConstant N * ((‖center N x‖ ^ 2)⁻¹ * symmetryRemainder B t x ^ 2) := by ring
      _ ≤ partitionMetricConstant N * ((N : ℝ) ^ 2 * (C : ℝ) ^ 2) := hr
      _ ≤ (partitionMetricConstant N * max 4 ((N : ℝ) ^ 2)) * (C : ℝ) ^ 2 := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg (C : ℝ)))
          (partitionMetricConstant_nonneg N)
  have hl := weighted_active_bound
    (fun a => (centeredAtlas N).configurationWeights a x)
    (fun a => operatorCoordinateMetric (liftUniformChart B N lower a) x (configurationTensor B t x))
    (chartMetricConstant N b) (fun a => x ∈ liftOrbitDomain B N a) ((C : ℝ) ^ 2)
    (sq_nonneg (C : ℝ)) ((centeredAtlas N).configurationWeights_square hN hx)
    (chartMetricConstant_nonneg N b (fun n hn => (ihm n hn).nonneg))
    (fun a ha => (weight_zero_outside_chart (fun hs => liftWeight_support B N hN a ⟨hs, hx⟩) ha).1)
    (fun a ha => liftUniformChart_lipschitz_bound B N lower hN b ih ihm a ha t ht C hC)
  exact (add_le_add hc hl).trans_eq (by unfold stepMetricConstant; ring)

theorem liftStepCandidate_metric_properties (hN : 2 ≤ N) (b : ℕ → ℝ)
    (ih : ∀ n < N, SmoothLiftProperties B n (lower n))
    (ihm : ∀ n < N, LiftMetricProperties B n (lower n) (b n)) :
    LiftMetricProperties B N (liftStepCandidate B N lower) (stepMetricConstant N b) where
  nonneg := stepMetricConstant_nonneg N b (fun n hn => (ihm n hn).nonneg)
  pair := fun _ hx t ht => liftStepOperator_pair_bound B N lower hN b ih ihm hx t ht
  lipschitz := fun _ hx t ht C hC => liftStepOperator_lipschitz_bound B N lower hN b ih ihm hx t ht C hC

/-- A scalar recursion depending only on particle count. -/
def liftMetricConstant (n : ℕ) : ℝ :=
  Nat.strongRecOn n (fun m ih => if m ≤ 1 then 0 else
    stepMetricConstant m (fun k => if hk : k < m then ih k hk else 0))

theorem liftMetricConstant_eq (n : ℕ) :
    liftMetricConstant n = if n ≤ 1 then 0 else
      stepMetricConstant n (fun k => if k < n then liftMetricConstant k else 0) := by
  unfold liftMetricConstant Nat.strongRecOn
  rw [WellFounded.fix_eq]
  apply congrArg (fun f : ℕ → ℝ => if n ≤ 1 then 0 else stepMetricConstant n f)
  funext k
  split_ifs <;> rfl

theorem identityLiftCandidate_coordinate_metric (n : ℕ) (x : Configuration n) (u : B.H n) :
    operatorCoordinateMetric (identityLiftCandidate B n).operator x u = 0 := by
  unfold operatorCoordinateMetric
  change (∑ q : Fin n × Fin 3,
    ‖fderiv ℝ (fun _ : Configuration n => ContinuousLinearMap.id ℂ (B.H n)) x
      (EuclideanSpace.single q 1) u‖ ^ 2) = 0
  rw [fderiv_const_apply]
  change (∑ _ : Fin n × Fin 3, ‖(0 : B.H n)‖ ^ 2) = 0
  simp

theorem identityLiftCandidate_metric_properties (n : ℕ) :
    LiftMetricProperties B n (identityLiftCandidate B n) 0 where
  nonneg := le_rfl
  pair := by
    intro x hx t ht
    simp only [identityLiftCandidate_coordinate_metric, zero_mul, le_refl]
  lipschitz := by
    intro x hx t ht C hC
    simp only [identityLiftCandidate_coordinate_metric, zero_mul, le_refl]

/-- Both quantitative bounds are proved by strong induction for the actual
constructed operators, with no unproved local metric estimate. -/
theorem recursiveLiftCandidate_metric_properties (n : ℕ) :
    LiftMetricProperties B n (recursiveLiftCandidate B n) (liftMetricConstant n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [recursiveLiftCandidate_eq, liftMetricConstant_eq]
    by_cases hn : n ≤ 1
    · rw [if_pos hn, if_pos hn]
      exact identityLiftCandidate_metric_properties B n
    · rw [if_neg hn, if_neg hn]
      apply liftStepCandidate_metric_properties B n _ (by omega)
      · intro k hk
        simpa only [if_pos hk] using recursiveLiftCandidate_properties B k
      · intro k hk
        simpa only [if_pos hk] using ih k hk

/-- The minimum estimate in the smooth tensor-lift theorem. -/
theorem recursiveLiftCandidate_min_bound (n : ℕ) {x : Configuration n}
    (hx : x ∈ distinctConfigurations n)
    (t : EuclideanSpace ℝ (Fin 3) → V) (ht : ∀ y, ‖t y‖ = 1)
    (C : ℝ≥0) (hC : LipschitzWith C t) :
    operatorCoordinateMetric (recursiveLiftCandidate B n).operator x (configurationTensor B t x) ≤
      liftMetricConstant n * min (pairEnergy x) ((C : ℝ) ^ 2) := by
  have h := recursiveLiftCandidate_metric_properties B n
  rcases le_total (pairEnergy x) ((C : ℝ) ^ 2) with hp | hp
  · simpa only [min_eq_left hp] using h.pair x hx t ht
  · simpa only [min_eq_right hp] using h.lipschitz x hx t ht C hC

end GptLean.SymmetricLift
