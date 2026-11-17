import GptLean.SymmetricLift.TensorBackground

/-! Actual local tensor families constructed from lower-particle operators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift
open UniformSpace TopologicalSpace
open scoped ContDiff BigOperators

section RecursiveCharts
variable (H K : ℕ → Type)
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
  [∀ n, NormedAddCommGroup (K n)] [∀ n, InnerProductSpace ℂ (K n)]
variable (V : ∀ n, Configuration n → H n →L[ℂ] K n)

abbrev ChartBlockTarget {N : ℕ} (x : Configuration N) : TensorHilbert :=
  BlockTensor (fun c : PositionClasses x => K (blockSize x c)) (coincidenceBlockList x)

local instance recursiveChartsRealTarget {N : ℕ} (x : Configuration N) :
    NormedSpace ℝ (Completion (ChartBlockTarget K x)) :=
  NormedSpace.restrictScalars ℝ ℂ _

local instance recursiveChartsRealOperator {N : ℕ} (x : Configuration N) :
    NormedSpace ℝ (H N →L[ℂ] Completion (ChartBlockTarget K x)) :=
  NormedSpace.restrictScalars ℝ ℂ _

local instance recursiveChartsContinuousRealOperator {N : ℕ} (x : Configuration N) :
    ContinuousSMul ℝ (H N →L[ℂ] Completion (ChartBlockTarget K x)) := by
  constructor
  have hc := (Complex.continuous_ofReal.comp
    (continuous_fst : Continuous (Prod.fst :
      ℝ × (H N →L[ℂ] Completion (ChartBlockTarget K x)) → ℝ))).smul continuous_snd
  change Continuous (fun p : ℝ × (H N →L[ℂ] Completion (ChartBlockTarget K x)) =>
    (p.1 : ℂ) • p.2) at hc
  simpa only [Complex.coe_smul] using hc

/-- Actual lower-N chart factors evaluated on the actual block coordinates. -/
def restrictedFamily {N : ℕ} (x : Configuration N) (c : PositionClasses x)
    (y : Configuration N) : H (blockSize x c) →L[ℂ] K (blockSize x c) :=
  V (blockSize x c) (blockConfiguration x c y)

/-- The derivative of each factor includes the coordinate restriction. -/
def restrictedDerivative {N : ℕ} (x : Configuration N) (c : PositionClasses x)
    (y : Configuration N) :
    Configuration N →L[ℝ] (H (blockSize x c) →L[ℂ] K (blockSize x c)) :=
  (fderiv ℝ (V (blockSize x c)) (blockConfiguration x c y)).comp (blockConfiguration x c)

/-- Algebraic tensor product of all lower-N chart factors. -/
def algebraicChartFamily {N : ℕ} (x : Configuration N) (y : Configuration N) :
    ChartBlockDomain H x →L[ℂ] ChartBlockTarget K x :=
  blockTensorFamily (fun c => H (blockSize x c)) (fun c => K (blockSize x c))
    (restrictedFamily H K V x) (coincidenceBlockList x) y

def algebraicChartDerivative {N : ℕ} (x : Configuration N) (y : Configuration N) :
    Configuration N →L[ℝ] (ChartBlockDomain H x →L[ℂ] ChartBlockTarget K x) :=
  blockTensorDerivative (fun c => H (blockSize x c)) (fun c => K (blockSize x c))
    (restrictedFamily H K V x) (restrictedDerivative H K V x) (coincidenceBlockList x) y

/-- The completed local family on the original N-particle Hilbert space. -/
def recursiveChartFamily {N : ℕ} (x : Configuration N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x)) (y : Configuration N) :
    H N →L[ℂ] Completion (ChartBlockTarget K x) :=
  transportCompleteOperator e (algebraicChartFamily H K V x y)

def recursiveChartDerivative {N : ℕ} (x : Configuration N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x)) (y : Configuration N) :
    Configuration N →L[ℝ] (H N →L[ℂ] Completion (ChartBlockTarget K x)) :=
  (transportCompleteOperator e).restrictScalars ℝ |>.comp (algebraicChartDerivative H K V x y)

/-- Smooth local chart maps are derived from the lower-N induction hypotheses. -/
theorem recursiveChartFamily_smooth {N : ℕ} (x : Configuration N)
    (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ContDiffOn ℝ ∞ (V n) (distinctConfigurations n)) :
    ContDiffOn ℝ ∞ (recursiveChartFamily H K V x e) (distinctConfigurations N) := by
  apply transportCompleteOperator_contDiffOn
  apply blockTensorFamily_contDiffOn
  intro c
  exact (hV _ (classBlock_card_lt hx c)).comp
    (blockConfiguration x c).contDiff.contDiffOn
    (fun y hy => blockConfiguration_distinct x c hy)

/-- The local family is an isometry on all vectors, including the completion. -/
theorem recursiveChartFamily_norm {N : ℕ} (x : Configuration N)
    (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ∀ y ∈ distinctConfigurations n, ∀ u, ‖V n y u‖ = ‖u‖)
    {y : Configuration N} (hy : y ∈ distinctConfigurations N) (u : H N) :
    ‖recursiveChartFamily H K V x e y u‖ = ‖u‖ := by
  apply transportCompleteOperator_norm
  apply blockTensorFamily_norm
  intro c z
  exact hV _ (classBlock_card_lt hx c) _ (blockConfiguration_distinct x c hy) z

/-- Product and chain rules give the actual derivative of the local construction. -/
theorem recursiveChartFamily_hasFDerivAt {N : ℕ} (x : Configuration N)
    (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ContDiffOn ℝ ∞ (V n) (distinctConfigurations n))
    {y : Configuration N} (hy : y ∈ distinctConfigurations N) :
    HasFDerivAt (recursiveChartFamily H K V x e)
      (recursiveChartDerivative H K V x e y) y := by
  apply transportCompleteOperator_hasFDerivAt
  apply blockTensorFamily_hasFDerivAt
  intro c
  have hdiff := ((hV _ (classBlock_card_lt hx c)).contDiffAt
    ((distinctConfigurations_isOpen _).mem_nhds (blockConfiguration_distinct x c hy))).differentiableAt
    (by simp)
  exact hdiff.hasFDerivAt.comp y (blockConfiguration x c).hasFDerivAt

/-- Flatness is inherited from the lower-N operators through the actual derivative. -/
theorem recursiveChartFamily_flat {N : ℕ} (x : Configuration N)
    (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ContDiffOn ℝ ∞ (V n) (distinctConfigurations n))
    (hflat : ∀ n < N, ∀ y ∈ distinctConfigurations n, ∀ d u v,
      inner ℂ (V n y u) (fderiv ℝ (V n) y d v) = 0)
    {y : Configuration N} (hy : y ∈ distinctConfigurations N)
    (d : Configuration N) (u v : H N) :
    inner ℂ (recursiveChartFamily H K V x e y u)
      (fderiv ℝ (recursiveChartFamily H K V x e) y d v) = 0 := by
  have hd : fderiv ℝ (recursiveChartFamily H K V x e) y =
      recursiveChartDerivative H K V x e y :=
    HasFDerivAt.fderiv (𝕜 := ℝ) (E := Configuration N)
      (F := H N →L[ℂ] Completion (ChartBlockTarget K x))
      (recursiveChartFamily_hasFDerivAt H K V x hx e hV hy)
  rw [hd]
  apply transportCompleteOperator_flat
  apply blockTensorDerivative_flat
  intro c d z w
  exact hflat _ (classBlock_card_lt hx c) _ (blockConfiguration_distinct x c hy)
    (blockConfiguration x c d) z w

/-- The blockwise tensor permutation, independent of the local chart operators. -/
def algebraicBlockPermutation
    (R : ∀ n, Equiv.Perm (Fin n) → H n →L[ℂ] H n)
    {N : ℕ} (x : Configuration N) (π : Equiv.Perm (Fin N))
    (hπ : permuteConfiguration π x = x) :
    ChartBlockDomain H x →L[ℂ] ChartBlockDomain H x :=
  blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
    (fun c (_ : Configuration N) => R _ (indexedBlockPermutation π x hπ c))
    (coincidenceBlockList x) x

/-- Covariance under the stabilizer is proved from the genuine lower-N action.
The hypothesis `he` is solely the canonical regrouping identity for tensor
permutations and does not mention the constructed operator family. -/
theorem recursiveChartFamily_equivariant
    (R : ∀ n, Equiv.Perm (Fin n) → H n →L[ℂ] H n)
    {N : ℕ} (x : Configuration N) (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ∀ π : Equiv.Perm (Fin n), ∀ y ∈ distinctConfigurations n, ∀ u,
      V n (permuteConfiguration π y) (R n π u) = V n y u)
    (π : Equiv.Perm (Fin N)) (hπ : permuteConfiguration π x = x)
    (he : ∀ u, e (R N π u) = (algebraicBlockPermutation H R x π hπ).completion (e u))
    {y : Configuration N} (hy : y ∈ distinctConfigurations N) (u : H N) :
    recursiveChartFamily H K V x e (permuteConfiguration π y) (R N π u) =
      recursiveChartFamily H K V x e y u := by
  apply transportCompleteOperator_equivariant e _ _ _ _ he
  intro z
  have hlocal (c : PositionClasses x) (w : H (blockSize x c)) :
      restrictedFamily H K V x c (permuteConfiguration π y)
        (R _ (indexedBlockPermutation π x hπ c) w) = restrictedFamily H K V x c y w := by
    change V _ (blockConfiguration x c (permuteConfiguration π y)) _ = _
    rw [blockConfiguration_permute π x hπ c y]
    exact hV _ (classBlock_card_lt hx c) _ _ (blockConfiguration_distinct x c hy) w
  have ht := blockTensorFamily_equivariant
    (fun c : PositionClasses x => H (blockSize x c)) (fun c => K (blockSize x c))
    (restrictedFamily H K V x)
    (fun c => R _ (indexedBlockPermutation π x hπ c))
    y (permuteConfiguration π y) hlocal (coincidenceBlockList x)
  have hc (s : List (PositionClasses x)) :
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
        (fun c (_ : Configuration N) => R _ (indexedBlockPermutation π x hπ c)) s y =
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
        (fun c (_ : Configuration N) => R _ (indexedBlockPermutation π x hπ c)) s x := by
    induction s with
    | nil => rfl
    | cons a s ih => change TensorProduct.mapL _ _ = TensorProduct.mapL _ _; rw [ih]
  rw [hc] at ht
  exact congrArg (fun L => L z) ht

def algebraicBlockProjection (P : ∀ n, H n →L[ℂ] H n)
    {N : ℕ} (x : Configuration N) : ChartBlockDomain H x →L[ℂ] ChartBlockDomain H x :=
  blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
    (fun c (_ : ℝ) => P (blockSize x c)) (coincidenceBlockList x) 0

def algebraicChartConstant (C : ∀ n, H n →L[ℂ] K n)
    {N : ℕ} (x : Configuration N) : ChartBlockDomain H x →L[ℂ] ChartBlockTarget K x :=
  blockTensorFamily (fun c => H (blockSize x c)) (fun c => K (blockSize x c))
    (fun c (_ : ℝ) => C (blockSize x c)) (coincidenceBlockList x) 0

/-- The fully symmetric tensors are fixed independently of the configuration.
`he` expresses only that full symmetry implies symmetry in each block. -/
theorem recursiveChartFamily_fixed (P : ∀ n, H n →L[ℂ] H n)
    (C : ∀ n, H n →L[ℂ] K n)
    {N : ℕ} (x : Configuration N) (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hV : ∀ n < N, ∀ y ∈ distinctConfigurations n, ∀ u, V n y (P n u) = C n u)
    (he : ∀ u, (algebraicBlockProjection H P x).completion (e (P N u)) = e (P N u))
    {y : Configuration N} (hy : y ∈ distinctConfigurations N) (u : H N) :
    recursiveChartFamily H K V x e y (P N u) =
      transportCompleteOperator e (algebraicChartConstant H K C x) (P N u) := by
  apply transportCompleteOperator_fixed e _ _ _ _ he
  intro z
  have hlocal (c : PositionClasses x) (w : H (blockSize x c)) :
      restrictedFamily H K V x c y (P (blockSize x c) w) = C (blockSize x c) w :=
    hV _ (classBlock_card_lt hx c) _ (blockConfiguration_distinct x c hy) w
  have ht := blockTensorFamily_fixed
    (fun c : PositionClasses x => H (blockSize x c)) (fun c => K (blockSize x c))
    (restrictedFamily H K V x) (fun c => P (blockSize x c))
    (fun c => C (blockSize x c)) hlocal (coincidenceBlockList x)
  have hp (s : List (PositionClasses x)) :
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
        (fun c (_ : Configuration N) => P (blockSize x c)) s y =
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => H (blockSize x c))
        (fun c (_ : ℝ) => P (blockSize x c)) s 0 := by
    induction s with
    | nil => rfl
    | cons a s ih => change TensorProduct.mapL _ _ = TensorProduct.mapL _ _; rw [ih]
  have hc (s : List (PositionClasses x)) :
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => K (blockSize x c))
        (fun c (_ : Configuration N) => C (blockSize x c)) s y =
      blockTensorFamily (fun c => H (blockSize x c)) (fun c => K (blockSize x c))
        (fun c (_ : ℝ) => C (blockSize x c)) s 0 := by
    induction s with
    | nil => rfl
    | cons a s ih => change TensorProduct.mapL _ _ = TensorProduct.mapL _ _; rw [ih]
  rw [hp, hc] at ht
  exact congrArg (fun L => L z) ht

/-- Exact local metric from the actual product-rule derivative. The pure-tensor
reindex identity `he` is the only tensor-coordinate input. -/
theorem recursiveChartFamily_metric {N : ℕ} (x : Configuration N)
    (hx : x ∈ centeredSphere N)
    (e : H N ≃ₗᵢ[ℂ] Completion (ChartBlockDomain H x))
    (hsmooth : ∀ n < N, ContDiffOn ℝ ∞ (V n) (distinctConfigurations n))
    (hiso : ∀ n < N, ∀ y ∈ distinctConfigurations n, ∀ u, ‖V n y u‖ = ‖u‖)
    (hflat : ∀ n < N, ∀ y ∈ distinctConfigurations n, ∀ d u v,
      inner ℂ (V n y u) (fderiv ℝ (V n) y d v) = 0)
    {y : Configuration N} (hy : y ∈ distinctConfigurations N)
    (t : ∀ c : PositionClasses x, H (blockSize x c)) (ht : ∀ c, ‖t c‖ = 1)
    (u : H N)
    (he : e u = (blockTensorVector (fun c => H (blockSize x c)) t
      (coincidenceBlockList x) : Completion (ChartBlockDomain H x))) (d : Configuration N) :
    ‖fderiv ℝ (recursiveChartFamily H K V x e) y d u‖ ^ 2 =
      ((coincidenceBlockList x).map (fun c =>
        ‖fderiv ℝ (V (blockSize x c)) (blockConfiguration x c y)
          (blockConfiguration x c d) (t c)‖ ^ 2)).sum := by
  have hd : fderiv ℝ (recursiveChartFamily H K V x e) y =
      recursiveChartDerivative H K V x e y :=
    HasFDerivAt.fderiv (𝕜 := ℝ) (E := Configuration N)
      (F := H N →L[ℂ] Completion (ChartBlockTarget K x))
      (recursiveChartFamily_hasFDerivAt H K V x hx e hsmooth hy)
  rw [hd]
  change ‖transportCompleteOperator e (algebraicChartDerivative H K V x y d) u‖ ^ 2 = _
  rw [transportCompleteOperator_metric e _ u _ he]
  apply blockTensorDerivative_metric
  · intro c z
    exact hiso _ (classBlock_card_lt hx c) _ (blockConfiguration_distinct x c hy) z
  · intro c d z w
    exact hflat _ (classBlock_card_lt hx c) _ (blockConfiguration_distinct x c hy)
      (blockConfiguration x c d) z w
  · exact ht

end RecursiveCharts

end GptLean.SymmetricLift
