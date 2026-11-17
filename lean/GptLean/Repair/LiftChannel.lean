import GptLean.Repair.CovariantProduct

/-!
The actual recursive Sobolev lift supplies the normalized symmetric repair
multipliers. Its connection is the one-particle connection, and its metric
splits into the one-particle derivative and the already constructed flat
lift correction. These are consequences of static tensor multilinearity
and the recursive lift, rather than extra channel hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.SymmetricLift

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology NNReal ContDiff

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [SeparableSpace V]

namespace TensorMultilinearData

variable {B : TensorBackground V} (M : TensorMultilinearData B)
include M

/-- Fixing unit factors except at one position gives a linear isometry.
The inner-product identity needed for the current follows from this map. -/
def insertionIsometry {N : ℕ} (t : Fin N → V) (i : Fin N)
    (ht : ∀ j, j ≠ i → ‖t j‖ = 1) : V →ₗᵢ[ℂ] B.H N where
  toLinearMap := (M.pureMap N).toMultilinearMap.toLinearMap t i
  norm_map' v := by
    change ‖(M.pureMap N) (Function.update t i v)‖ = ‖v‖
    rw [M.pure_eq, M.pure_norm]
    have he : (fun j => ‖Function.update t i v j‖) =
        (fun j => if j = i then ‖v‖ else 1) := by
      funext j
      by_cases hj : j = i
      · simp [hj]
      · simp [ht j hj, hj]
    simp [he]

theorem pure_insertion_inner {N : ℕ} (t : Fin N → V) (i : Fin N)
    (ht : ∀ j, ‖t j‖ = 1) (v : V) :
    inner ℂ (B.pure N t) (B.pure N (Function.update t i v)) = inner ℂ (t i) v := by
  have h := (M.insertionIsometry t i (fun j _ => ht j)).inner_map_map (t i) v
  simpa [insertionIsometry, MultilinearMap.toLinearMap, M.pure_eq] using h

theorem pure_insertion_norm {N : ℕ} (t : Fin N → V) (i : Fin N)
    (ht : ∀ j, ‖t j‖ = 1) (v : V) :
    ‖B.pure N (Function.update t i v)‖ = ‖v‖ := by
  simpa [insertionIsometry, MultilinearMap.toLinearMap, M.pure_eq] using
    (M.insertionIsometry t i (fun j _ => ht j)).norm_map v

end TensorMultilinearData

/-- Normalization of the concrete lift holds outside the collision set,
even when the one-particle unit condition only holds almost everywhere. -/
theorem recursiveLift_unit_ae (B : TensorBackground V) (N : ℕ)
    {t : EuclideanSpace ℝ (Fin 3) → V}
    (ht : ∀ᵐ y ∂volume, ‖t y‖ = 1) :
    ∀ᵐ x ∂volume, ‖recursiveLiftField B N (configurationTensor B t) x‖ = 1 := by
  filter_upwards [ae_distinctConfigurations N, ae_all_particles (N := N) ht] with x hx htx
  exact ((recursiveLiftCandidate_properties B N).norm x hx _).trans
    (B.pure_unit N _ htx)

/-- Symmetry of the actual multiplier field follows from the two
permutation actions. It is not an imposed symmetry of the Kraus vectors. -/
theorem recursiveLift_permutation_ae (B : TensorBackground V) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin 3) → V) (π : Equiv.Perm (Fin N)) :
    ∀ᵐ x ∂volume,
      recursiveLiftField B N (configurationTensor B t) (permuteConfiguration π x) =
        recursiveLiftField B N (configurationTensor B t) x := by
  filter_upwards [ae_distinctConfigurations N] with x hx
  unfold recursiveLiftField
  rw [configurationTensor_permute]
  exact (recursiveLiftCandidate_properties B N).equivariant π x hx _

/-- Flatness removes the derivative of the lift from its connection. -/
theorem recursiveLift_connection (B : TensorBackground V) (M : TensorMultilinearData B)
    (N : ℕ) (q : Fin N × Fin 3)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (ht : ∀ i, ‖t (particle x i)‖ = 1) :
    inner ℂ (recursiveLiftField B N (configurationTensor B t) x)
      (recursiveLiftWeakGradient B N t g q x) =
        inner ℂ (t (particle x q.1)) (g q.2 (particle x q.1)) := by
  let L : B.H N →ₗᵢ[ℂ] (recursiveLiftCandidate B N).target :=
    ⟨((recursiveLiftCandidate B N).operator x).toLinearMap,
      (recursiveLiftCandidate_properties B N).norm x hx⟩
  change inner ℂ (L (configurationTensor B t x))
    (recursiveLiftCorrection B N q (configurationTensor B t) x +
      L (configurationTensorInsertion B q.1 t (g q.2) x)) = _
  rw [inner_add_right]
  have hflat := (recursiveLiftCandidate_properties B N).flat x hx
    (EuclideanSpace.single q 1) (configurationTensor B t x) (configurationTensor B t x)
  change inner ℂ (L (configurationTensor B t x))
    (recursiveLiftCorrection B N q (configurationTensor B t) x) = 0 at hflat
  rw [hflat, zero_add, L.inner_map_map]
  exact M.pure_insertion_inner _ q.1 ht _

/-- The connection identity applies to the weak gradient produced by the
H1 continuation theorem, without a smoothness hypothesis on the source. -/
theorem recursiveLift_connection_ae (B : TensorBackground V) (M : TensorMultilinearData B)
    (N : ℕ) (q : Fin N × Fin 3)
    {t : EuclideanSpace ℝ (Fin 3) → V} (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (ht : ∀ᵐ y ∂volume, ‖t y‖ = 1) :
    ∀ᵐ x ∂volume,
      inner ℂ (recursiveLiftField B N (configurationTensor B t) x)
        (recursiveLiftWeakGradient B N t g q x) =
          inner ℂ (t (particle x q.1)) (g q.2 (particle x q.1)) := by
  filter_upwards [ae_distinctConfigurations N, ae_all_particles (N := N) ht] with x hx htx
  exact recursiveLift_connection B M N q t g hx htx

/-- The exact derivative metric retains the one-particle kinetic term. -/
theorem recursiveLift_gradient_norm_sq (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ) (q : Fin N × Fin 3)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (ht : ∀ i, ‖t (particle x i)‖ = 1) :
    ‖recursiveLiftWeakGradient B N t g q x‖ ^ 2 =
      ‖g q.2 (particle x q.1)‖ ^ 2 +
        ‖recursiveLiftCorrection B N q (configurationTensor B t) x‖ ^ 2 := by
  rw [recursiveLiftWeakGradient, recursiveLiftWeakDerivative_norm_sq B N q _ _ hx]
  rw [show ‖configurationTensorInsertion B q.1 t (g q.2) x‖ =
    ‖g q.2 (particle x q.1)‖ from M.pure_insertion_norm _ q.1 ht _]

/-- Summing the exact split gives the full metric used in current repair. -/
theorem recursiveLift_metric_eq (B : TensorBackground V) (M : TensorMultilinearData B)
    (N : ℕ) (t : EuclideanSpace ℝ (Fin 3) → V)
    (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N)
    (ht : ∀ i, ‖t (particle x i)‖ = 1) :
    (∑ q, ‖recursiveLiftWeakGradient B N t g q x‖ ^ 2) =
      (∑ q : Fin N × Fin 3, ‖g q.2 (particle x q.1)‖ ^ 2) +
        operatorCoordinateMetric (recursiveLiftCandidate B N).operator x
          (configurationTensor B t x) := by
  simp_rw [recursiveLift_gradient_norm_sq B M N _ t g hx ht]
  rw [Finset.sum_add_distrib]
  rfl

/-- The full weak-gradient bound now follows from the constructed lift's
pair estimate. The source derivatives are arbitrary representatives. -/
theorem recursiveLift_metric_le_pair (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (ht : ∀ y, ‖t y‖ = 1) {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (∑ q, ‖recursiveLiftWeakGradient B N t g q x‖ ^ 2) ≤
      (∑ q : Fin N × Fin 3, ‖g q.2 (particle x q.1)‖ ^ 2) +
        liftMetricConstant N * pairEnergy x := by
  rw [recursiveLift_metric_eq B M N t g hx (fun i => ht _)]
  exact add_le_add le_rfl ((recursiveLiftCandidate_metric_properties B N).pair x hx t ht)

/-- For Lipschitz source tags the singular metric is bounded by the
minimum of the pair energy and the squared Lipschitz constant. -/
theorem recursiveLift_metric_le_min (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (ht : ∀ y, ‖t y‖ = 1) (C : ℝ≥0) (hC : LipschitzWith C t)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) :
    (∑ q, ‖recursiveLiftWeakGradient B N t g q x‖ ^ 2) ≤
      (∑ q : Fin N × Fin 3, ‖g q.2 (particle x q.1)‖ ^ 2) +
        liftMetricConstant N * min (pairEnergy x) ((C : ℝ) ^ 2) := by
  rw [recursiveLift_metric_eq B M N t g hx (fun i => ht _)]
  exact add_le_add le_rfl
    ((recursiveLiftCandidate_full_properties B N).min_bound hx t ht C hC)

/-- A uniform bound on the full one-particle gradient gives the uniform
many-particle metric needed for bounded local repair multipliers. -/
theorem recursiveLift_metric_uniform_ae (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ)
    (t : EuclideanSpace ℝ (Fin 3) → V) (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (ht : ∀ y, ‖t y‖ = 1) (C : ℝ≥0) (hC : LipschitzWith C t)
    (hg : ∀ᵐ y ∂volume, (∑ μ, ‖g μ y‖ ^ 2) ≤ (C : ℝ) ^ 2) :
    ∀ᵐ x ∂volume, (∑ q, ‖recursiveLiftWeakGradient B N t g q x‖ ^ 2) ≤
      ((N : ℝ) + liftMetricConstant N) * (C : ℝ) ^ 2 := by
  filter_upwards [ae_distinctConfigurations N, ae_all_particles (N := N) hg] with x hx hgx
  have hs : (∑ q : Fin N × Fin 3, ‖g q.2 (particle x q.1)‖ ^ 2) ≤
      (N : ℝ) * (C : ℝ) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simpa using (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hgx i))
  have hm := recursiveLift_metric_le_min B M N t g ht C hC hx
  have hc := mul_le_mul_of_nonneg_left (min_le_right (pairEnergy x) ((C : ℝ) ^ 2))
    (liftMetricConstant_nonneg N)
  nlinarith

end GptLean.SymmetricLift

namespace GptLean.Repair

open MeasureTheory Filter TopologicalSpace GptLean.SymmetricLift
open scoped ENNReal Topology NNReal ContDiff

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [SeparableSpace V] [CompleteSpace V]
  {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [CompleteSpace V] in
/-- The actual Sobolev lift gives a normalized family of coordinates.
An arbitrary basis index allows finite-dimensional repair targets too. -/
theorem lifted_coordinate_normalization (B : TensorBackground V) (N : ℕ)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target)
    {t : EuclideanSpace ℝ (Fin 3) → V} (ht : ∀ᵐ y ∂volume, ‖t y‖ = 1) :
    ∀ᵐ x ∂volume, HasSum
      (fun a => ‖coordinate b (recursiveLiftField B N (configurationTensor B t) x) a‖ ^ 2) 1 :=
  (recursiveLift_unit_ae B N ht).mono (fun _ hx => coordinate_normalization b hx)

omit [CompleteSpace V] in
/-- The prescribed one-particle connection is transported through the
constructed lift and Parseval to the scalar repair coordinates. -/
theorem lifted_coordinate_connection (B : TensorBackground V) (M : TensorMultilinearData B)
    (N : ℕ) (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target)
    {t : EuclideanSpace ℝ (Fin 3) → V} (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V)
    (s : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ)
    (ht : ∀ᵐ y ∂volume, ‖t y‖ = 1)
    (hs : ∀ μ, ∀ᵐ y ∂volume, inner ℂ (t y) (g μ y) = Complex.I * s μ y)
    (q : Fin N × Fin 3) :
    ∀ᵐ x ∂volume, HasSum
      (fun a => starRingEnd ℂ (coordinate b
        (recursiveLiftField B N (configurationTensor B t) x) a) *
        coordinate b (recursiveLiftWeakGradient B N t g q x) a)
      (Complex.I * s q.2 (particle x q.1)) := by
  filter_upwards [recursiveLift_connection_ae B M N q g ht,
    ae_all_particles (N := N) (hs q.2)] with x hx hsx
  exact coordinate_connection b (hx.trans (hsx q.1))

omit [CompleteSpace V] in
/-- Each scalar repair multiplier preserves the source's permutation
character. In particular the sign character gives fermionic vectors. -/
theorem lifted_coordinate_preserves_permutation (B : TensorBackground V) (N : ℕ)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target)
    (t : EuclideanSpace ℝ (Fin 3) → V) (π : Equiv.Perm (Fin N))
    {ψ : Configuration N → H} {c : ℂ}
    (hψ : ∀ᵐ x ∂volume, ψ (permuteConfiguration π x) = c • ψ x) (a : ι) :
    ∀ᵐ x ∂volume,
      coordinate b (recursiveLiftField B N (configurationTensor B t)
        (permuteConfiguration π x)) a • ψ (permuteConfiguration π x) =
      c • (coordinate b (recursiveLiftField B N (configurationTensor B t) x) a • ψ x) := by
  filter_upwards [recursiveLift_permutation_ae B N t π, hψ] with x hx hpx
  rw [hx, hpx, smul_comm]

/-- Coordinate weak derivatives of the actual recursive lift are obtained
from ordinary one-particle H1 data. -/
theorem lifted_coordinate_hasWeakH1Local (B : TensorBackground V)
    (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (ht : HasWeakH1Local t g) (hunit : ∀ᵐ y ∂volume, ‖t y‖ = 1) (a : ι) :
    HasWeakH1Local
      (fun x => coordinate b (recursiveLiftField B N (configurationTensor B t) x) a)
      (fun q x => coordinate b (recursiveLiftWeakGradient B N t g q x) a) := by
  let := recursiveLiftCandidate_complete B N
  exact weakH1Local_map ((innerSL ℂ (b a)).restrictScalars ℝ)
    (recursiveLift_hasWeakH1Local_of_ae_bound B M N ht (hunit.mono (fun _ h => h.le)))

/-- The constructed Sobolev multiplier acts on a smooth source core with
the proved weak product derivative. Collision diagonals require no extra
source-side identity or separately chosen approximation. -/
theorem lifted_coordinate_product_hasWeakH1Local [CompleteSpace H]
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ι ℂ (recursiveLiftCandidate B N).target)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (ht : HasWeakH1Local t g) (hunit : ∀ᵐ y ∂volume, ‖t y‖ = 1)
    {ψ : Configuration N → H} (hψ : ContDiff ℝ ∞ ψ) (a : ι) :
    HasWeakH1Local
      (fun x => coordinate b (recursiveLiftField B N (configurationTensor B t) x) a • ψ x)
      (fun q x => coordinate b (recursiveLiftWeakGradient B N t g q x) a • ψ x +
        coordinate b (recursiveLiftField B N (configurationTensor B t) x) a •
          fderiv ℝ ψ x (EuclideanSpace.single q 1)) := by
  exact weakH1Local_complex_smul_smooth
    (lifted_coordinate_hasWeakH1Local B M N b ht hunit a) hψ

/-- The covariant derivative used in the energy and current series is
identified with the actual weak derivative for the constructed lift on a
smooth source core. Physical unbounded form-domain closure remains separate. -/
theorem lifted_channel_covariant_source_core [CompleteSpace H]
    (B : TensorBackground V) (M : TensorMultilinearData B) (N : ℕ)
    (b : HilbertBasis ℕ ℂ (recursiveLiftCandidate B N).target)
    {t : EuclideanSpace ℝ (Fin 3) → V} {g : Fin 3 → EuclideanSpace ℝ (Fin 3) → V}
    (ht : HasWeakH1Local t g) (hunit : ∀ᵐ y ∂volume, ‖t y‖ = 1)
    {ψ : Configuration N → H} (hψ : ContDiff ℝ ∞ ψ)
    (A : (Fin N × Fin 3) → Configuration N → H →ₗ[ℂ] H) (a : ℕ) :
    ∃ dψa : (Fin N × Fin 3) → Configuration N → H,
      HasWeakH1Local (channelValue b (recursiveLiftField B N (configurationTensor B t)) ψ a)
        dψa ∧
      ∀ q x, -Complex.I • dψa q x -
        A q x (channelValue b (recursiveLiftField B N (configurationTensor B t)) ψ a x) =
        channelDerivative b (recursiveLiftField B N (configurationTensor B t))
          (recursiveLiftWeakGradient B N t g q)
          (fun y => -Complex.I • fderiv ℝ ψ y (EuclideanSpace.single q 1) - A q y (ψ y))
          ψ a x := by
  let := recursiveLiftCandidate_complete B N
  exact channel_covariant_derivative_smooth_source b
    (recursiveLift_hasWeakH1Local_of_ae_bound B M N ht (hunit.mono (fun _ h => h.le))) hψ A a

end GptLean.Repair
