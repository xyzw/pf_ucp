import GptLean.ElectronicLocalizationPartition
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Algebra.Order.Floor.Ring

/-!
A concrete smooth square partition on the integer lattice. Every integer
translate of one fixed bump is divided by the square root of the locally
finite sum of its squared translates. The floor of the spatial coordinate
always supplies a bump equal to one, so the denominator never vanishes.
-/

noncomputable section

namespace GptLean.LatticePartition

open Finset Filter Metric
open scoped Topology ContDiff

def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def raw (z : ℤ) (x : ℝ) : ℝ := bump (x - (z : ℝ))

theorem raw_nonneg (z : ℤ) (x : ℝ) : 0 ≤ raw z x := bump.nonneg

theorem raw_contDiff (z : ℤ) : ContDiff ℝ ∞ (raw z) :=
  bump.contDiff.comp (contDiff_id.sub contDiff_const)

theorem raw_support (z : ℤ) (x : ℝ) (hx : raw z x ≠ 0) :
    |x - (z : ℝ)| < 2 := by
  have h : x - (z : ℝ) ∈ Function.support bump := hx
  rw [bump.support_eq] at h
  simpa only [mem_ball, Real.dist_eq, sub_zero, bump] using h

theorem raw_locallyFinite : LocallyFinite (fun z => Function.support (raw z)) := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩
  apply (Set.finite_Icc (⌊x - 3⌋ : ℤ) ⌈x + 3⌉).subset
  rintro z ⟨y, hy, hyx⟩
  have hz := abs_lt.mp (raw_support z y hy)
  have hxy := abs_lt.mp (show |y - x| < 1 by simpa only [mem_ball, Real.dist_eq] using hyx)
  constructor
  · exact_mod_cast (show (⌊x - 3⌋ : ℝ) ≤ (z : ℝ) from
      (Int.floor_le (x - 3)).trans (by linarith))
  · exact_mod_cast (show (z : ℝ) ≤ (⌈x + 3⌉ : ℝ) from
      (show (z : ℝ) ≤ x + 3 by linarith).trans (Int.le_ceil (x + 3)))

theorem raw_floor (x : ℝ) : raw ⌊x⌋ x = 1 := by
  apply bump.one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  change |x - (⌊x⌋ : ℝ)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
  linarith [Int.lt_floor_add_one x]

def squareMass (x : ℝ) : ℝ := ∑' z : ℤ, raw z x ^ 2

theorem raw_sq_summable (x : ℝ) : Summable (fun z : ℤ => raw z x ^ 2) := by
  apply summable_of_hasFiniteSupport
  apply (raw_locallyFinite.point_finite x).subset
  intro z hz hzero
  exact hz (by simp [hzero])

theorem one_le_squareMass (x : ℝ) : 1 ≤ squareMass x := by
  have h := (raw_sq_summable x).le_tsum ⌊x⌋ (fun z _ => sq_nonneg (raw z x))
  simpa only [raw_floor, one_pow, squareMass] using h

theorem squareMass_pos (x : ℝ) : 0 < squareMass x :=
  lt_of_lt_of_le zero_lt_one (one_le_squareMass x)

theorem squareMass_contDiff : ContDiff ℝ ∞ squareMass := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨s, hs⟩ := ElectronicLocalization.exists_local_active_finset raw raw_locallyFinite x
  have heq : squareMass =ᶠ[𝓝 x] fun y => ∑ z ∈ s, raw z y ^ 2 := by
    filter_upwards [hs] with y hy
    exact tsum_eq_sum fun z hz => by simp [hy z hz]
  exact (ContDiff.sum (fun z (_ : z ∈ s) => (raw_contDiff z).pow 2)).contDiffAt
    |>.congr_of_eventuallyEq heq

def eta (z : ℤ) (x : ℝ) : ℝ := raw z x / Real.sqrt (squareMass x)

theorem eta_nonneg (z : ℤ) (x : ℝ) : 0 ≤ eta z x :=
  div_nonneg (raw_nonneg z x) (Real.sqrt_nonneg _)

theorem eta_contDiff (z : ℤ) : ContDiff ℝ ∞ (eta z) :=
  (raw_contDiff z).div
    (squareMass_contDiff.sqrt (fun x => ne_of_gt (squareMass_pos x)))
    (fun x => ne_of_gt (Real.sqrt_pos.mpr (squareMass_pos x)))

theorem eta_locallyFinite : LocallyFinite (fun z => Function.support (eta z)) :=
  raw_locallyFinite.subset fun z x hx hzero => hx (by simp [eta, hzero])

theorem eta_hasSum_sq (x : ℝ) : HasSum (fun z : ℤ => eta z x ^ 2) 1 := by
  have h := (raw_sq_summable x).hasSum.div_const (squareMass x)
  change HasSum (fun z : ℤ => raw z x ^ 2 / squareMass x)
    (squareMass x / squareMass x) at h
  rw [div_self (ne_of_gt (squareMass_pos x))] at h
  simpa only [eta, div_pow, Real.sq_sqrt (le_of_lt (squareMass_pos x))] using h

theorem eta_support (z : ℤ) (x : ℝ) (hx : eta z x ≠ 0) :
    |x - (z : ℝ)| < 2 :=
  raw_support z x (fun hzero => hx (by simp [eta, hzero]))

theorem raw_translate (z k : ℤ) (x : ℝ) :
    raw z (x + (k : ℝ)) = raw (z - k) x := by
  unfold raw
  congr 1
  push_cast
  ring

theorem squareMass_translate (k : ℤ) (x : ℝ) :
    squareMass (x + (k : ℝ)) = squareMass x := by
  unfold squareMass
  simp_rw [raw_translate]
  simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
    (Equiv.addRight (-k)).tsum_eq (fun z : ℤ => raw z x ^ 2)

theorem eta_translate (z k : ℤ) (x : ℝ) :
    eta z (x + (k : ℝ)) = eta (z - k) x := by
  simp only [eta, raw_translate, squareMass_translate]

end GptLean.LatticePartition
