import GptLean.RemovalClusterMeasured
import GptLean.SymmetricLift.PermutationMetric

/-! The actual many-particle cluster phase. Compact support of the fixed
one-particle phase gives a finite global gradient bound at each measured
field, and the coordinate chain rule transfers the plateau cancellation. -/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalGeometry

open Finset Metric MeasureTheory GptLean.SymmetricLift
open scoped ContDiff

variable {N : ℕ} {Q : Type*} [MeasurableSpace Q]

local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _
local instance (G : SimpleGraph (Fin N)) : Fintype G.ConnectedComponent := Fintype.ofFinite _

theorem physicalClusterCutoff_hasCompactSupport (c : Fin N → ClusterSpace)
    {R : ℝ} (hR : 0 < R) (s : (clusterGraph c R).ConnectedComponent) :
    HasCompactSupport (physicalClusterCutoff c R s) := by
  change IsCompact (tsupport (physicalClusterCutoff c R s))
  apply (isCompact_closedBall (physicalClusterCentre c R s) (clusterRadius N R)).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  exact (Metric.mem_ball.mp (physicalClusterCutoff_support c hR s x hx)).le

theorem clusterPhase_hasCompactSupport (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R)
    (e : ℝ) (a : ClusterSpace → ClusterSpace) : HasCompactSupport (clusterPhase c R e a) := by
  let f : (clusterGraph c R).ConnectedComponent → ClusterSpace → ℝ := fun s x =>
    physicalClusterCutoff c R s x * inner ℝ (a (physicalClusterCentre c R s))
      (x - physicalClusterCentre c R s)
  have hs : HasCompactSupport (∑ s, f s) :=
    HasCompactSupport.finset_sum (fun s _ => (physicalClusterCutoff_hasCompactSupport c hR s).mul_right)
  have h : HasCompactSupport ((fun _ : ClusterSpace => -e) * ∑ s, f s) := hs.mul_left
  convert h using 1
  ext x
  simp [clusterPhase, phase, f]

theorem clusterPhase_exists_derivative_bound (c : Fin N → ClusterSpace) {R : ℝ}
    (hR : 0 < R) (e : ℝ) (a : ClusterSpace → ClusterSpace) :
    ∃ P : ℝ, 0 < P ∧ ∀ x, ‖fderiv ℝ (clusterPhase c R e a) x‖ ≤ P := by
  have hc : Continuous (fderiv ℝ (clusterPhase c R e a)) :=
    (clusterPhase_contDiff c R e a).continuous_fderiv (by simp)
  have hs := (clusterPhase_hasCompactSupport c hR e a).fderiv ℝ
  obtain ⟨P, hP⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max P 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ (clusterPhase c R e a))
  · exact (hP x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

def configurationClusterPhase (c : Fin N → ClusterSpace) (R e : ℝ)
    (a : ClusterSpace → ClusterSpace) (x : Configuration N) : ℝ :=
  ∑ i, clusterPhase c R e a (particle x i)

theorem configurationClusterPhase_contDiff (c : Fin N → ClusterSpace) (R e : ℝ)
    (a : ClusterSpace → ClusterSpace) : ContDiff ℝ ∞ (configurationClusterPhase c R e a) := by
  apply ContDiff.sum
  intro i _
  exact (clusterPhase_contDiff c R e a).comp (particleLinear i).toContinuousLinearMap.contDiff

theorem configurationClusterPhase_permute (c : Fin N → ClusterSpace) (R e : ℝ)
    (a : ClusterSpace → ClusterSpace) (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    configurationClusterPhase c R e a (permuteConfiguration π x) =
      configurationClusterPhase c R e a x := by
  unfold configurationClusterPhase
  simp_rw [particle_permute]
  exact Equiv.sum_comp π.symm (fun i => clusterPhase c R e a (particle x i))

theorem configurationClusterPhase_jointly_stronglyMeasurable
    (c : Fin N → ClusterSpace) (R e : ℝ) {a : Q → ClusterSpace → ClusterSpace}
    (ha : StronglyMeasurable (Function.uncurry a)) :
    StronglyMeasurable (Function.uncurry (fun q => configurationClusterPhase c R e (a q))) := by
  have hc : StronglyMeasurable (fun p : Q × ClusterSpace => clusterPhase c R e (a p.1) p.2) :=
    clusterPhase_jointly_stronglyMeasurable c R e (a := a) ha
  have hf (i : Fin N) : StronglyMeasurable
      (fun p : Q × Configuration N => clusterPhase c R e (a p.1) (particle p.2 i)) := by
    have hp : Measurable (fun p : Q × Configuration N => (p.1, particle p.2 i)) :=
      measurable_fst.prodMk
        ((particleLinear i).toContinuousLinearMap.continuous.measurable.comp measurable_snd)
    exact hc.comp_measurable (g := fun p : Q × Configuration N => (p.1, particle p.2 i)) hp
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ => hf i)

theorem configurationClusterPhase_fderiv_single (c : Fin N → ClusterSpace) (R e : ℝ)
    (a : ClusterSpace → ClusterSpace) (x : Configuration N) (j : Fin N × Fin 3) :
    fderiv ℝ (configurationClusterPhase c R e a) x (EuclideanSpace.single j 1) =
      fderiv ℝ (clusterPhase c R e a) (particle x j.1) (EuclideanSpace.single j.2 1) := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun i y => clusterPhase c R e a (particle y i))
    (A' := fun i => (fderiv ℝ (clusterPhase c R e a) (particle x i)).comp
      (particleLinear i).toContinuousLinearMap)
    (fun i _ => ((clusterPhase_contDiff c R e a).differentiable (by simp) _).hasFDerivAt.comp x
      (particleLinear i).toContinuousLinearMap.hasFDerivAt)
  change HasFDerivAt (configurationClusterPhase c R e a) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, fderiv ℝ (clusterPhase c R e a) (particle x i)
    (particle (EuclideanSpace.single j 1) i)) = _
  rw [Finset.sum_eq_single j.1]
  · rw [particle_single_same]
  · intro i _ hi
    rw [particle_single_ne j.1 j.2 hi, map_zero]
  · simp

theorem configurationClusterPhase_exists_derivative_bound
    (c : Fin N → ClusterSpace) {R : ℝ} (hR : 0 < R) (e : ℝ)
    (a : ClusterSpace → ClusterSpace) :
    ∃ P : ℝ, 0 < P ∧ ∀ j x,
      |fderiv ℝ (configurationClusterPhase c R e a) x (EuclideanSpace.single j 1)| ≤ P := by
  obtain ⟨P, hP, hb⟩ := clusterPhase_exists_derivative_bound c hR e a
  refine ⟨P, hP, fun j x => ?_⟩
  rw [configurationClusterPhase_fderiv_single]
  have h := (fderiv ℝ (clusterPhase c R e a) (particle x j.1)).le_opNorm
    (EuclideanSpace.single j.2 (1 : ℝ))
  have h' : |fderiv ℝ (clusterPhase c R e a) (particle x j.1)
      (EuclideanSpace.single j.2 1)| ≤ ‖fderiv ℝ (clusterPhase c R e a) (particle x j.1)‖ := by
    simpa only [Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one, mul_one] using h
  exact h'.trans (hb _)

theorem configurationClusterPhase_cancellation (c : Fin N → ClusterSpace)
    {R : ℝ} (hR : 0 < R) (e : ℝ) (a : ClusterSpace → ClusterSpace)
    (x : Configuration N) (j : Fin N × Fin 3)
    (hx : ∃ i, dist (particle x j.1) (c i) ≤ 4 * R) :
    fderiv ℝ (configurationClusterPhase c R e a) x (EuclideanSpace.single j 1) +
      clusterResidual c R e a (particle x j.1) j.2 = -e * a (particle x j.1) j.2 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨hφ, hv⟩ := clusterPhase_cancellation c hR e a i (particle x j.1) hi
  rw [configurationClusterPhase_fderiv_single, hφ.fderiv]
  have h := congrArg (fun u : ClusterSpace => u j.2) hv
  simpa only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    EuclideanSpace.inner_single_right, conj_trivial, mul_one, one_mul, PiLp.add_apply,
    PiLp.smul_apply] using h

theorem symmetricLocalization_tsupport_near_centre
    (α : Fin N → GptLean.LatticePartition.Lattice) {R : ℝ} (hR : 0 < R)
    (x : Configuration N)
    (hx : x ∈ tsupport (fun y : Configuration N =>
      GptLean.ElectronicLocalization.symmetricMultiplier (GptLean.LatticePartition.multiplier R)
        α (fun i => particle y i))) (j : Fin N) :
    ∃ i, dist (particle x j) (GptLean.LatticePartition.centre R (α i)) ≤ 4 * R := by
  have hc : IsClosed (⋃ i : Fin N, {y : Configuration N |
      dist (particle y j) (GptLean.LatticePartition.centre R (α i)) ≤ 4 * R}) := by
    apply isClosed_iUnion_of_finite
    intro i
    exact isClosed_le
      ((particleLinear j).toContinuousLinearMap.continuous.dist continuous_const) continuous_const
  have hs : tsupport (fun y : Configuration N =>
      GptLean.ElectronicLocalization.symmetricMultiplier (GptLean.LatticePartition.multiplier R)
        α (fun i => particle y i)) ⊆
      ⋃ i : Fin N, {y : Configuration N |
        dist (particle y j) (GptLean.LatticePartition.centre R (α i)) ≤ 4 * R} := by
    apply closure_minimal _ hc
    intro y hy
    obtain ⟨π, hπ⟩ := GptLean.LatticePartition.symmetric_spatial_support R hR α
      (fun i => particle y i) hy
    apply Set.mem_iUnion.mpr
    refine ⟨π.symm j, ?_⟩
    change dist (particle y j) _ ≤ _
    simpa only [π.apply_symm_apply] using (hπ (π.symm j)).le
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
  exact ⟨i, hi⟩

theorem configurationClusterPhase_cancellation_on_localization
    (α : Fin N → GptLean.LatticePartition.Lattice) {R : ℝ} (hR : 0 < R)
    (e : ℝ) (a : ClusterSpace → ClusterSpace) (x : Configuration N)
    (hx : x ∈ tsupport (fun y : Configuration N =>
      GptLean.ElectronicLocalization.symmetricMultiplier (GptLean.LatticePartition.multiplier R)
        α (fun i => particle y i))) (j : Fin N × Fin 3) :
    let c := fun i => GptLean.LatticePartition.centre R (α i)
    fderiv ℝ (configurationClusterPhase c R e a) x (EuclideanSpace.single j 1) +
      clusterResidual c R e a (particle x j.1) j.2 = -e * a (particle x j.1) j.2 :=
  configurationClusterPhase_cancellation _ hR e a x j
    (symmetricLocalization_tsupport_near_centre α hR x hx j.1)

end GptLean.RemovalGeometry
