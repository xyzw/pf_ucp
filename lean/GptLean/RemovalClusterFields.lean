import GptLean.RemovalClusters
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Concrete cluster cutoffs, gauge phases and residual fields. The single
unit-scale bump is fixed once. Every scale and centre uses its translate
and dilation, so all derivative constants are independent of the labels
and the localization scale. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalGeometry

open Finset Metric Filter GptLean.ElectronicLocalization
open scoped ContDiff Topology InnerProductSpace

variable {N : ℕ}

local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _
local instance (G : SimpleGraph (Fin N)) : Fintype G.ConnectedComponent := Fintype.ofFinite _

def clusterUnitBump : ContDiffBump (0 : ClusterSpace) where
  rIn := 5
  rOut := 6
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem clusterUnitBump_exists_derivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ clusterUnitBump x‖ ≤ C := by
  have hc : Continuous (fderiv ℝ clusterUnitBump) :=
    (clusterUnitBump.contDiff : ContDiff ℝ ∞ _).continuous_fderiv (by simp)
  have hs := clusterUnitBump.hasCompactSupport.fderiv ℝ
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ clusterUnitBump)
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact (zero_le_one.trans (le_max_right _ _))

def clusterBumpDerivativeConstant : ℝ :=
  Classical.choose clusterUnitBump_exists_derivative_bound

theorem clusterBumpDerivativeConstant_pos : 0 < clusterBumpDerivativeConstant :=
  (Classical.choose_spec clusterUnitBump_exists_derivative_bound).1

theorem clusterBumpDerivativeConstant_bound (x : ClusterSpace) :
    ‖fderiv ℝ clusterUnitBump x‖ ≤ clusterBumpDerivativeConstant :=
  (Classical.choose_spec clusterUnitBump_exists_derivative_bound).2 x

def centreCutoff (R : ℝ) (c x : ClusterSpace) : ℝ :=
  clusterUnitBump (R⁻¹ • (x - c))

theorem centreCutoff_bounds (R : ℝ) (c x : ClusterSpace) :
    0 ≤ centreCutoff R c x ∧ centreCutoff R c x ≤ 1 :=
  ⟨clusterUnitBump.nonneg, clusterUnitBump.le_one⟩

theorem centreCutoff_contDiff (R : ℝ) (c : ClusterSpace) :
    ContDiff ℝ ∞ (centreCutoff R c) := by
  have h : ContDiff ℝ ∞ (fun x : ClusterSpace => R⁻¹ • (x - c)) :=
    ContDiff.const_smul R⁻¹ (contDiff_id.sub contDiff_const)
  exact clusterUnitBump.contDiff.comp h

theorem centreCutoff_one {R : ℝ} (hR : 0 < R) (c x : ClusterSpace)
    (hx : dist x c ≤ 4 * R) : centreCutoff R c x = 1 := by
  apply clusterUnitBump.one_of_mem_closedBall
  change dist (R⁻¹ • (x - c)) 0 ≤ 5
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  have hn : ‖x - c‖ ≤ 4 * R := by simpa only [dist_eq_norm] using hx
  have h : R⁻¹ * ‖x - c‖ ≤ 4 := by
    rw [← div_eq_inv_mul, div_le_iff₀ hR]
    exact hn
  linarith

theorem centreCutoff_support {R : ℝ} (hR : 0 < R) (c x : ClusterSpace)
    (hx : centreCutoff R c x ≠ 0) : x ∈ ball c (6 * R) := by
  have h : R⁻¹ • (x - c) ∈ Function.support clusterUnitBump := hx
  rw [clusterUnitBump.support_eq] at h
  change dist (R⁻¹ • (x - c)) 0 < 6 at h
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
    ← div_eq_inv_mul, div_lt_iff₀ hR] at h
  exact Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using h)

theorem centreCutoff_derivative_bound {R : ℝ} (hR : 0 < R) (c x : ClusterSpace) :
    ‖fderiv ℝ (centreCutoff R c) x‖ ≤ clusterBumpDerivativeConstant / R := by
  have hd := ((clusterUnitBump.contDiff : ContDiff ℝ ∞ _).differentiable (by simp)
    (R⁻¹ • (x - c))).hasFDerivAt.comp x
    (((hasFDerivAt_id x).sub_const c).const_smul R⁻¹)
  change HasFDerivAt (centreCutoff R c) _ x at hd
  rw [hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
    ContinuousLinearMap.norm_id, mul_one]
  exact mul_le_mul_of_nonneg_right (clusterBumpDerivativeConstant_bound _) (inv_nonneg.mpr hR.le)

def clusterGraph (c : Fin N → ClusterSpace) (R : ℝ) : SimpleGraph (Fin N) :=
  centreGraph c (2 * (6 * R))

def physicalClusterCutoff (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) : ClusterSpace → ℝ :=
  componentCutoff (clusterGraph c R) (fun i => centreCutoff R (c i)) s

def physicalClusterCentre (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) : ClusterSpace :=
  c (clusterAnchor (clusterGraph c R) s)

def clusterRadius (N : ℕ) (R : ℝ) : ℝ := (6 + 12 * (N : ℝ)) * R

theorem physicalClusterCutoff_bounds (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace) :
    0 ≤ physicalClusterCutoff c R s x ∧ physicalClusterCutoff c R s x ≤ 1 :=
  componentCutoff_bounds _ _ (fun i x => centreCutoff_bounds R (c i) x) s x

theorem physicalClusterCutoff_contDiff (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) :
    ContDiff ℝ ∞ (physicalClusterCutoff c R s) :=
  componentCutoff_contDiff _ _ (fun i => centreCutoff_contDiff R (c i)) s

theorem physicalClusterCutoff_one (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R)
    (i : Fin N) (x : ClusterSpace) (hx : dist x (c i) ≤ 4 * R) :
    physicalClusterCutoff c R ((clusterGraph c R).connectedComponentMk i) x = 1 :=
  componentCutoff_one _ _ i x (centreCutoff_one hR (c i) x hx)

theorem physicalClusterCutoff_disjoint (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R)
    (x : ClusterSpace) (s t : (clusterGraph c R).ConnectedComponent)
    (hne : s ≠ t) (hs : physicalClusterCutoff c R s x ≠ 0) :
    physicalClusterCutoff c R t x = 0 :=
  componentCutoff_disjoint c _ (fun i x hx => centreCutoff_support hR (c i) x hx)
    x s t hne hs

theorem physicalClusterCutoff_derivative_zero (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace)
    (hx : physicalClusterCutoff c R s x = 0) :
    fderiv ℝ (physicalClusterCutoff c R s) x = 0 :=
  componentCutoff_derivative_zero _ _ (fun i x => centreCutoff_bounds R (c i) x) s x hx

theorem physicalClusterCutoff_derivative_one (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace)
    (hx : physicalClusterCutoff c R s x = 1) :
    fderiv ℝ (physicalClusterCutoff c R s) x = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  exact Eventually.of_forall fun y => by
    rw [hx]
    exact (physicalClusterCutoff_bounds c R s y).2

theorem physicalClusterCutoff_support (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R)
    (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace)
    (hx : physicalClusterCutoff c R s x ≠ 0) :
    x ∈ ball (physicalClusterCentre c R s) (clusterRadius N R) := by
  have h := componentCutoff_support c (r := 6 * R) (by positivity) _
    (fun i x hi => centreCutoff_support hR (c i) x hi) s x hx
  change dist x (physicalClusterCentre c R s) < 6 * R + ((N : ℝ) - 1) * (2 * (6 * R)) at h
  change dist x (physicalClusterCentre c R s) < (6 + 12 * (N : ℝ)) * R
  linarith

theorem physicalClusterCutoff_active_derivative (c : Fin N → ClusterSpace) (R : ℝ)
    (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace)
    (hx : physicalClusterCutoff c R s x ≠ 0 ∨
      fderiv ℝ (physicalClusterCutoff c R s) x ≠ 0) :
    physicalClusterCutoff c R s x ≠ 0 := by
  rcases hx with hx | hx
  · exact hx
  · exact fun h => hx (physicalClusterCutoff_derivative_zero c R s x h)

theorem physicalClusterCutoff_derivative_bound (c : Fin N → ClusterSpace) {R : ℝ}
    (hR : 0 < R) (s : (clusterGraph c R).ConnectedComponent) (x : ClusterSpace) :
    ‖fderiv ℝ (physicalClusterCutoff c R s) x‖ ≤
      (N : ℝ) * (clusterBumpDerivativeConstant / R) :=
  componentCutoff_derivative_bound _ _ (fun i x => centreCutoff_bounds R (c i) x)
    (fun i => (centreCutoff_contDiff R (c i)).differentiable (by simp))
    (div_nonneg clusterBumpDerivativeConstant_pos.le hR.le)
    (fun i x => centreCutoff_derivative_bound hR (c i) x) s x

def clusterPhase (c : Fin N → ClusterSpace) (R e : ℝ) (a : ClusterSpace → ClusterSpace) :
    ClusterSpace → ℝ :=
  phase e (physicalClusterCutoff c R) (physicalClusterCentre c R) a

def clusterResidual (c : Fin N → ClusterSpace) (R e : ℝ) (a : ClusterSpace → ClusterSpace) :
    ClusterSpace → ClusterSpace :=
  residualVelocity e (physicalClusterCutoff c R) (physicalClusterCentre c R) a

theorem clusterPhase_contDiff (c : Fin N → ClusterSpace) (R e : ℝ)
    (a : ClusterSpace → ClusterSpace) : ContDiff ℝ ∞ (clusterPhase c R e a) := by
  unfold clusterPhase phase
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro s _
  exact (physicalClusterCutoff_contDiff c R s).mul
    ((innerSL ℝ (a (physicalClusterCentre c R s))).contDiff.comp
      (contDiff_id.sub contDiff_const))

theorem clusterResidual_contDiff (c : Fin N → ClusterSpace) (R e : ℝ)
    {a : ClusterSpace → ClusterSpace} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (clusterResidual c R e a) := by
  unfold clusterResidual residualVelocity
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro s _
  exact (physicalClusterCutoff_contDiff c R s).smul (ha.sub contDiff_const)

/-- On every localization support, exactly one cutoff is one and all
cutoff derivatives vanish. This proves the actual phase cancellation. -/
theorem clusterPhase_cancellation (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R)
    (e : ℝ) (a : ClusterSpace → ClusterSpace) (i : Fin N) (x : ClusterSpace)
    (hx : dist x (c i) ≤ 4 * R) :
    HasFDerivAt (clusterPhase c R e a)
      ((-e) • innerSL ℝ (a (physicalClusterCentre c R
        ((clusterGraph c R).connectedComponentMk i)))) x ∧
    (-e) • a (physicalClusterCentre c R ((clusterGraph c R).connectedComponentMk i)) +
      clusterResidual c R e a x = (-e) • a x := by
  let s₀ := (clusterGraph c R).connectedComponentMk i
  have h1 : physicalClusterCutoff c R s₀ x = 1 := physicalClusterCutoff_one c hR i x hx
  have h0 (s) (hs : s ≠ s₀) : physicalClusterCutoff c R s x = 0 :=
    physicalClusterCutoff_disjoint c hR x s₀ s hs.symm (by rw [h1]; norm_num)
  have hd (s) : HasFDerivAt (physicalClusterCutoff c R s) (0 : ClusterSpace →L[ℝ] ℝ) x := by
    have h := ((physicalClusterCutoff_contDiff c R s).differentiable (by simp) x).hasFDerivAt
    by_cases hs : s = s₀
    · subst s
      rwa [physicalClusterCutoff_derivative_one c R s₀ x h1] at h
    · rwa [physicalClusterCutoff_derivative_zero c R s x (h0 s hs)] at h
  exact ⟨hasFDerivAt_phase e _ _ a x s₀ hd h1 h0,
    gradient_phase_add_residualVelocity e _ _ a x s₀ h1 h0⟩

theorem lattice_clusterPhase_cancellation (α : Fin N → GptLean.LatticePartition.Lattice)
    {R : ℝ} (hR : 0 < R) (e : ℝ) (a : ClusterSpace → ClusterSpace)
    (i : Fin N) (x : ClusterSpace)
    (hx : x ∈ tsupport (GptLean.LatticePartition.multiplier R (α i))) :
    let c := fun j => GptLean.LatticePartition.centre R (α j)
    HasFDerivAt (clusterPhase c R e a)
      ((-e) • innerSL ℝ (a (physicalClusterCentre c R
        ((clusterGraph c R).connectedComponentMk i)))) x ∧
    (-e) • a (physicalClusterCentre c R ((clusterGraph c R).connectedComponentMk i)) +
      clusterResidual c R e a x = (-e) • a x :=
  clusterPhase_cancellation _ hR e a i x
    (GptLean.LatticePartition.multiplier_tsupport_subset_closedBall R hR (α i) hx)

theorem norm_clusterResidual_le (c : Fin N → ClusterSpace) {R e Z : ℝ} (hR : 0 < R)
    (he : 0 ≤ e) (hZ : 0 ≤ Z) {a : ClusterSpace → ClusterSpace}
    (ha : Differentiable ℝ a)
    (ha' : ∀ s, ∀ y ∈ ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ a y‖ ≤ Z) (x : ClusterSpace) :
    ‖clusterResidual c R e a x‖ ≤ e * clusterRadius N R * Z :=
  norm_residualVelocity_le e _ _ a (fderiv ℝ a) (ρ₀ := clusterRadius N R)
    he (by unfold clusterRadius; positivity) hZ
    (physicalClusterCutoff_bounds c R) (physicalClusterCutoff_disjoint c hR)
    (physicalClusterCutoff_support c hR)
    (fun _ y _ => (ha y).hasFDerivAt.hasFDerivWithinAt) ha' x

theorem norm_fderiv_clusterResidual_le (c : Fin N → ClusterSpace) {R e Z : ℝ}
    (hR : 0 < R) (he : 0 ≤ e) (hZ : 0 ≤ Z) {a : ClusterSpace → ClusterSpace}
    (ha : Differentiable ℝ a)
    (ha' : ∀ s, ∀ y ∈ ball (physicalClusterCentre c R s) (clusterRadius N R),
      ‖fderiv ℝ a y‖ ≤ Z) (x : ClusterSpace) :
    ‖fderiv ℝ (clusterResidual c R e a) x‖ ≤
      e * ((N : ℝ) * clusterBumpDerivativeConstant * (6 + 12 * (N : ℝ)) + 1) * Z := by
  have hg : 0 ≤ (N : ℝ) * (clusterBumpDerivativeConstant / R) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg clusterBumpDerivativeConstant_pos.le hR.le)
  have hd := norm_fderiv_residualVelocity_le e (physicalClusterCutoff c R)
    (fun s => fderiv ℝ (physicalClusterCutoff c R s)) (physicalClusterCentre c R)
    a (fderiv ℝ a) (ρ₀ := clusterRadius N R)
    (g := (N : ℝ) * (clusterBumpDerivativeConstant / R))
    he (by unfold clusterRadius; positivity) hZ hg
    (physicalClusterCutoff_bounds c R)
    (fun s x => ((physicalClusterCutoff_contDiff c R s).differentiable (by simp) x).hasFDerivAt)
    (physicalClusterCutoff_derivative_bound c hR)
    (fun x s t hst hs => by
      have ht := physicalClusterCutoff_disjoint c hR x s t hst
        (physicalClusterCutoff_active_derivative c R s x hs)
      exact ⟨ht, physicalClusterCutoff_derivative_zero c R t x ht⟩)
    (fun s x hs => physicalClusterCutoff_support c hR s x
      (physicalClusterCutoff_active_derivative c R s x hs))
    (fun y => (ha y).hasFDerivAt) ha' x
  change HasFDerivAt (clusterResidual c R e a) _ x ∧ _ at hd
  rw [hd.1.fderiv]
  convert hd.2 using 1 <;> unfold clusterRadius <;> field_simp [hR.ne'] <;> ring

end GptLean.RemovalGeometry
