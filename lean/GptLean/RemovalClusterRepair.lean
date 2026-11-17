import GptLean.RemovalClusterFields
import GptLean.RemovalRepair

/-! The concrete cluster residual supplies the six-component repair tag.
The coordinate conversion is differentiated explicitly, and its Frobenius
bound is derived from the Euclidean operator norm. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalGeometry

open Finset MeasureTheory GptLean.Repair GptLean.SymmetricLift GptLean.Multipliers
open scoped ContDiff

variable {N : ℕ}

def piCoordinateField (v : ClusterSpace → ClusterSpace) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  WithLp.ofLp (v (WithLp.toLp 2 x))

theorem piCoordinateField_differentiable {v : ClusterSpace → ClusterSpace}
    (hv : Differentiable ℝ v) : Differentiable ℝ (piCoordinateField v) := by
  intro x
  exact (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (v (WithLp.toLp 2 x))).differentiableAt.comp x
    ((hv _).comp x (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 x).differentiableAt)

theorem piCoordinateField_fderiv {v : ClusterSpace → ClusterSpace}
    (hv : Differentiable ℝ v) (x : Fin 3 → ℝ) (i j : Fin 3) :
    fderiv ℝ (piCoordinateField v) x (Pi.single j (1 : ℝ)) i =
      fderiv ℝ v (WithLp.toLp 2 x) (EuclideanSpace.single j (1 : ℝ)) i := by
  have h := (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (v (WithLp.toLp 2 x))).comp x
    ((hv _).hasFDerivAt.comp x (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 x))
  change HasFDerivAt (piCoordinateField v) _ x at h
  rw [h.fderiv]
  rfl

theorem euclidean_matrix_entry_le_opNorm (A : ClusterSpace →L[ℝ] ClusterSpace)
    (i j : Fin 3) : |A (EuclideanSpace.single j (1 : ℝ)) i| ≤ ‖A‖ := by
  have h := (PiLp.norm_apply_le (A (EuclideanSpace.single j (1 : ℝ))) i).trans
    (A.le_opNorm (EuclideanSpace.single j (1 : ℝ)))
  simpa only [Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one] using h

theorem piCoordinateField_frobenius_le {v : ClusterSpace → ClusterSpace}
    (hv : Differentiable ℝ v) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ x, ‖fderiv ℝ v x‖ ≤ D) (x : Fin 3 → ℝ) :
    (∑ i, ∑ j, (fderiv ℝ (piCoordinateField v) x (Pi.single j (1 : ℝ)) i) ^ 2) ≤
      (3 * D) ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, D ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [piCoordinateField_fderiv hv]
      have h := (euclidean_matrix_entry_le_opNorm (fderiv ℝ v (WithLp.toLp 2 x)) i j).trans
        (hbound _)
      simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) h 2)
    _ = (3 * D) ^ 2 := by simp; ring

def clusterVelocityBound (N : ℕ) (R e Z : ℝ) : ℝ := e * clusterRadius N R * Z

def clusterJacobianBound (N : ℕ) (e Z : ℝ) : ℝ :=
  3 * (e * ((N : ℝ) * clusterBumpDerivativeConstant * (6 + 12 * (N : ℝ)) + 1) * Z)

theorem clusterVelocityBound_nonneg (N : ℕ) {R e Z : ℝ}
    (hR : 0 ≤ R) (he : 0 ≤ e) (hZ : 0 ≤ Z) : 0 ≤ clusterVelocityBound N R e Z := by
  unfold clusterVelocityBound clusterRadius
  positivity

theorem clusterJacobianBound_nonneg (N : ℕ) {e Z : ℝ}
    (he : 0 ≤ e) (hZ : 0 ≤ Z) : 0 ≤ clusterJacobianBound N e Z := by
  have := clusterBumpDerivativeConstant_pos
  unfold clusterJacobianBound
  positivity

theorem clusterResidual_pi_bounds (c : Fin N → ClusterSpace) {R e Z : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hZ : 0 ≤ Z) {a : ClusterSpace → ClusterSpace}
    (ha : ContDiff ℝ ∞ a)
    (ha' : ∀ s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ a y‖ ≤ Z) :
    Differentiable ℝ (piCoordinateField (clusterResidual c R e a)) ∧
    (∀ x j, |piCoordinateField (clusterResidual c R e a) x j| ≤
      clusterVelocityBound N R e Z) ∧
    (∀ x, (∑ i, ∑ j,
      (fderiv ℝ (piCoordinateField (clusterResidual c R e a)) x (Pi.single j (1 : ℝ)) i) ^ 2) ≤
        clusterJacobianBound N e Z ^ 2) := by
  have hv := (clusterResidual_contDiff c R e ha).differentiable (by simp)
  refine ⟨piCoordinateField_differentiable hv, ?_, ?_⟩
  · intro x j
    have h := (PiLp.norm_apply_le (clusterResidual c R e a (WithLp.toLp 2 x)) j).trans
      (norm_clusterResidual_le c hR he hZ (ha.differentiable (by simp)) ha' _)
    simpa only [piCoordinateField, Real.norm_eq_abs, clusterVelocityBound] using h
  · intro x
    apply piCoordinateField_frobenius_le hv
    · have := clusterBumpDerivativeConstant_pos
      positivity
    · exact norm_fderiv_clusterResidual_le c hR he hZ (ha.differentiable (by simp)) ha'

/-- The actual cluster field gives all hypotheses of the repair lift
metric theorem. Its tag and its weak lift derivative are explicit. -/
theorem cluster_repairLift_metric (B : TensorBackground SixTag) (T : TensorMultilinearData B)
    (c : Fin N → ClusterSpace) {R e Z : ℝ} (hR : 0 < R) (he : 0 ≤ e) (hZ : 0 ≤ Z)
    {a : ClusterSpace → ClusterSpace} (ha : ContDiff ℝ ∞ a)
    (ha' : ∀ s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ a y‖ ≤ Z) :
    let V := clusterVelocityBound N R e Z
    let M := clusterJacobianBound N e Z
    let v := piCoordinateField (clusterResidual c R e a)
    ∀ᵐ x ∂volume, (∑ q, ‖recursiveLiftWeakGradient B N (repairTag V M v)
      (repairTagGradient V M v) q x‖ ^ 2) ≤
        9 * ((N : ℝ) + liftMetricConstant N) * (36 * V ^ 2 + 2 * M) := by
  obtain ⟨hv, hV, hM⟩ := clusterResidual_pi_bounds c hR he hZ ha ha'
  exact repairLift_metric B T N (clusterVelocityBound_nonneg N hR.le he hZ)
    (clusterJacobianBound_nonneg N he hZ) hv hV hM

def clusterRepairMetricConstant (N : ℕ) : ℝ :=
  9 * ((N : ℝ) + liftMetricConstant N) *
    (18 * (6 + 12 * (N : ℝ)) ^ 2 +
      3 * ((N : ℝ) * clusterBumpDerivativeConstant * (6 + 12 * (N : ℝ)) + 1))

theorem clusterRepairMetricConstant_nonneg (N : ℕ) : 0 ≤ clusterRepairMetricConstant N := by
  have := liftMetricConstant_nonneg N
  have := clusterBumpDerivativeConstant_pos
  unfold clusterRepairMetricConstant
  positivity

theorem cluster_repairLift_metric_paper (B : TensorBackground SixTag) (T : TensorMultilinearData B)
    (c : Fin N → ClusterSpace) {R e Z : ℝ} (hR : 0 < R) (he : 0 ≤ e) (hZ : 0 ≤ Z)
    {a : ClusterSpace → ClusterSpace} (ha : ContDiff ℝ ∞ a)
    (ha' : ∀ s, ∀ y ∈ Metric.ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ a y‖ ≤ Z) :
    let V := clusterVelocityBound N R e Z
    let M := clusterJacobianBound N e Z
    let v := piCoordinateField (clusterResidual c R e a)
    ∀ᵐ x ∂volume, (∑ q, ‖recursiveLiftWeakGradient B N (repairTag V M v)
      (repairTagGradient V M v) q x‖ ^ 2) ≤
        2 * clusterRepairMetricConstant N * (e ^ 2 * R ^ 2 * Z ^ 2 + e * Z) := by
  filter_upwards [cluster_repairLift_metric B T c hR he hZ ha ha'] with x hx
  apply hx.trans
  let D : ℝ := 6 + 12 * (N : ℝ)
  let K : ℝ := (N : ℝ) * clusterBumpDerivativeConstant * D + 1
  let A : ℝ := 9 * ((N : ℝ) + liftMetricConstant N)
  have hA : 0 ≤ A := by
    have := liftMetricConstant_nonneg N
    dsimp [A]
    positivity
  have hK : 0 ≤ K := by
    have := clusterBumpDerivativeConstant_pos
    dsimp [K, D]
    positivity
  have hX : 0 ≤ e ^ 2 * R ^ 2 * Z ^ 2 := by positivity
  have hY : 0 ≤ e * Z := mul_nonneg he hZ
  have hb : 36 * D ^ 2 * (e ^ 2 * R ^ 2 * Z ^ 2) + 6 * K * (e * Z) ≤
      (36 * D ^ 2 + 6 * K) * (e ^ 2 * R ^ 2 * Z ^ 2 + e * Z) := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36) (sq_nonneg D)) hY,
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hK) hX]
  calc
    _ = A * (36 * D ^ 2 * (e ^ 2 * R ^ 2 * Z ^ 2) + 6 * K * (e * Z)) := by
      dsimp [A, D, K, clusterVelocityBound, clusterRadius, clusterJacobianBound]
      ring
    _ ≤ A * ((36 * D ^ 2 + 6 * K) * (e ^ 2 * R ^ 2 * Z ^ 2 + e * Z)) :=
      mul_le_mul_of_nonneg_left hb hA
    _ = _ := by dsimp [A, D, K, clusterRepairMetricConstant]; ring

end GptLean.RemovalGeometry
