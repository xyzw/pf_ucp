import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! Concrete centered configurations and the compact sphere in Step 1. -/

noncomputable section
namespace GptLean.SymmetricLift

open WithLp
open scoped BigOperators ContDiff

abbrev Configuration (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin 3)

def meanCoordinate {N : ℕ} (x : Configuration N) (μ : Fin 3) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, x (i, μ)

def centerLinear (N : ℕ) : Configuration N →ₗ[ℝ] Configuration N where
  toFun x := toLp 2 (fun i => x i - meanCoordinate x i.2)
  map_add' x y := by
    ext i
    simp [meanCoordinate, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c x := by
    ext i
    simp [meanCoordinate, ← Finset.mul_sum]
    ring

def center (N : ℕ) : Configuration N →L[ℝ] Configuration N :=
  (centerLinear N).toContinuousLinearMap

theorem center_apply {N : ℕ} (x : Configuration N) (i : Fin N × Fin 3) :
    center N x i = x i - meanCoordinate x i.2 := rfl

theorem sum_center {N : ℕ} (hN : 0 < N) (x : Configuration N) (μ : Fin 3) :
    ∑ i, center N x (i, μ) = 0 := by
  have h : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [center_apply, meanCoordinate, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem mean_center {N : ℕ} (hN : 0 < N) (x : Configuration N) (μ : Fin 3) :
    meanCoordinate (center N x) μ = 0 := by simp [meanCoordinate, sum_center hN]

theorem center_idempotent {N : ℕ} (hN : 0 < N) (x : Configuration N) :
    center N (center N x) = center N x := by
  ext i
  simp [center_apply, mean_center hN]

def distinctConfigurations (N : ℕ) : Set (Configuration N) :=
  {x | ∀ i j : Fin N, i ≠ j → ∃ μ : Fin 3, x (i, μ) ≠ x (j, μ)}

theorem center_ne_zero_of_distinct {N : ℕ} (hN : 2 ≤ N)
    {x : Configuration N} (hx : x ∈ distinctConfigurations N) : center N x ≠ 0 := by
  intro hzero
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  obtain ⟨μ, hμ⟩ := hx i j hij
  have hi := congrArg (fun y : Configuration N => y (i, μ)) hzero
  have hj := congrArg (fun y : Configuration N => y (j, μ)) hzero
  simp only [center_apply, PiLp.zero_apply] at hi hj
  exact hμ (by linarith)

def centeredSphere (N : ℕ) : Set (Configuration N) :=
  {x | center N x = x ∧ ‖x‖ = 1}

theorem centeredSphere_compact (N : ℕ) : IsCompact (centeredSphere N) := by
  have hc : IsClosed {x : Configuration N | center N x = x} :=
    isClosed_eq (center N).continuous continuous_id
  have hs : IsCompact {x : Configuration N | ‖x‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using
      (isCompact_sphere (0 : Configuration N) 1)
  change IsCompact ({x | center N x = x} ∩ {x | ‖x‖ = 1})
  exact hs.inter_left hc

def normalizedCenter (N : ℕ) (x : Configuration N) : Configuration N :=
  ‖center N x‖⁻¹ • center N x

theorem normalizedCenter_mem_sphere {N : ℕ} (hN : 0 < N)
    {x : Configuration N} (hx : center N x ≠ 0) :
    normalizedCenter N x ∈ centeredSphere N := by
  have hn : ‖center N x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  constructor
  · simp only [normalizedCenter, map_smul, center_idempotent hN]
  · simp [normalizedCenter, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn]

theorem normalizedCenter_smooth (N : ℕ) :
    ContDiffOn ℝ ∞ (normalizedCenter N) {x | center N x ≠ 0} := by
  have hnorm : ContDiffOn ℝ ∞ (fun x => ‖center N x‖) {x | center N x ≠ 0} :=
    (center N).contDiff.contDiffOn.norm ℝ (fun _ hx => hx)
  exact (hnorm.inv (fun x hx => norm_ne_zero_iff.mpr hx)).smul
    (center N).contDiff.contDiffOn

theorem normalizedCenter_smooth_distinct {N : ℕ} (hN : 2 ≤ N) :
    ContDiffOn ℝ ∞ (normalizedCenter N) (distinctConfigurations N) :=
  (normalizedCenter_smooth N).mono (fun _ hx => center_ne_zero_of_distinct hN hx)

/-- A centered unit configuration cannot have only one coincidence block. -/
theorem sphere_has_distinct_points {N : ℕ} {x : Configuration N}
    (hx : x ∈ centeredSphere N) :
    ∃ i j : Fin N, ∃ μ : Fin 3, x (i, μ) ≠ x (j, μ) := by
  by_contra h
  push_neg at h
  have hzero : x = 0 := by
    ext i
    have hsame : ∑ j : Fin N, x (j, i.2) = N * x i := by
      calc
        _ = ∑ _j : Fin N, x i := Finset.sum_congr rfl (fun j _ => h j i.1 i.2)
        _ = _ := by simp
    have hN : (N : ℝ) ≠ 0 := by
      have hNnat : N ≠ 0 := by have := i.1.isLt; omega
      exact_mod_cast hNnat
    have hi := congrArg (fun y : Configuration N => y i) hx.1
    simp only [center_apply, meanCoordinate, hsame] at hi
    have hi0 : x i = 0 := by field_simp at hi; nlinarith
    simpa using hi0
  have := hx.2
  rw [hzero, norm_zero] at this
  norm_num at this

end GptLean.SymmetricLift
