import GptLean.RemovalGeometry
import GptLean.LatticePartition

/-!
Finite clusters of localization centres and their actual smooth union
cutoffs. Connected components determine the cluster labels. Cutoff
disjointness, plateau, support diameter and derivative bounds are derived
from one-centre bumps, including the derivative support at their zeros.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace GptLean.RemovalGeometry

open Finset Metric GptLean.ElectronicLocalization
open scoped ContDiff

variable {N : ℕ}

local instance (G : SimpleGraph (Fin N)) : DecidableEq G.ConnectedComponent := Classical.decEq _

abbrev ClusterSpace := EuclideanSpace ℝ (Fin 3)

def centreGraph (c : Fin N → ClusterSpace) (δ : ℝ) : SimpleGraph (Fin N) where
  Adj i j := i ≠ j ∧ dist (c i) (c j) ≤ δ
  symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa [dist_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def clusterAnchor (G : SimpleGraph (Fin N)) (s : G.ConnectedComponent) : Fin N :=
  Classical.choose s.exists_rep

theorem clusterAnchor_mem (G : SimpleGraph (Fin N)) (s : G.ConnectedComponent) :
    G.connectedComponentMk (clusterAnchor G s) = s :=
  Classical.choose_spec s.exists_rep

def componentCutoff (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (s : G.ConnectedComponent) (x : ClusterSpace) : ℝ := by
  classical
  exact clusterCutoff (fun i : {i // G.connectedComponentMk i = s} => θ i) x

theorem componentCutoff_formula (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (s : G.ConnectedComponent) (x : ClusterSpace) :
    componentCutoff G θ s x = 1 - ∏ i : {i // G.connectedComponentMk i = s}, (1 - θ i x) := by
  rfl

theorem componentCutoff_bounds (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (hθ : ∀ i x, 0 ≤ θ i x ∧ θ i x ≤ 1)
    (s : G.ConnectedComponent) (x : ClusterSpace) :
    0 ≤ componentCutoff G θ s x ∧ componentCutoff G θ s x ≤ 1 := by
  classical
  exact clusterCutoff_mem_Icc (fun i : {i // G.connectedComponentMk i = s} => θ i) x
    (fun i => hθ i x)

theorem componentCutoff_one (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (i : Fin N) (x : ClusterSpace) (h : θ i x = 1) :
    componentCutoff G θ (G.connectedComponentMk i) x = 1 := by
  classical
  exact clusterCutoff_eq_one (fun j : {j // G.connectedComponentMk j = G.connectedComponentMk i}
    => θ j) x (a := ⟨i, rfl⟩) h

theorem componentCutoff_nonzero (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (s : G.ConnectedComponent) (x : ClusterSpace)
    (h : componentCutoff G θ s x ≠ 0) :
    ∃ i, G.connectedComponentMk i = s ∧ θ i x ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  exact clusterCutoff_eq_zero (fun i : {i // G.connectedComponentMk i = s} => θ i) x
    (fun i => hn i i.property)

theorem componentCutoff_contDiff (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (hθ : ∀ i, ContDiff ℝ ∞ (θ i))
    (s : G.ConnectedComponent) : ContDiff ℝ ∞ (componentCutoff G θ s) := by
  classical
  change ContDiff ℝ ∞ (fun x => 1 - ∏ i : {i // G.connectedComponentMk i = s}, (1 - θ i x))
  exact contDiff_const.sub (contDiff_prod (fun i _ => contDiff_const.sub (hθ i)))

/-- Distinct clusters have disjoint active bumps when the graph threshold
is twice the support radius. -/
theorem componentCutoff_disjoint (c : Fin N → ClusterSpace) {r : ℝ}
    (θ : Fin N → ClusterSpace → ℝ)
    (hsupp : ∀ i x, θ i x ≠ 0 → x ∈ ball (c i) r)
    (x : ClusterSpace) (s t : (centreGraph c (2 * r)).ConnectedComponent)
    (hne : s ≠ t) (hs : componentCutoff (centreGraph c (2 * r)) θ s x ≠ 0) :
    componentCutoff (centreGraph c (2 * r)) θ t x = 0 := by
  classical
  by_contra ht
  obtain ⟨i, hi, hix⟩ := componentCutoff_nonzero _ θ s x hs
  obtain ⟨j, hj, hjx⟩ := componentCutoff_nonzero _ θ t x ht
  have hij : i ≠ j := by intro he; subst j; exact hne (hi.symm.trans hj)
  have hd : dist (c i) (c j) ≤ 2 * r := by
    have h1 := Metric.mem_ball.mp (hsupp i x hix)
    have h2 := Metric.mem_ball.mp (hsupp j x hjx)
    have htri := dist_triangle (c i) x (c j)
    rw [dist_comm (c i) x] at htri
    linarith
  exact hne (hi.symm.trans
    ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := centreGraph c (2 * r)) ⟨hij, hd⟩).trans hj))

/-- Every active point lies in the ball about the selected cluster anchor
with radius controlled only by the number of particles and the scale. -/
theorem componentCutoff_support (c : Fin N → ClusterSpace) {r : ℝ} (hr : 0 ≤ r)
    (θ : Fin N → ClusterSpace → ℝ)
    (hsupp : ∀ i x, θ i x ≠ 0 → x ∈ ball (c i) r)
    (s : (centreGraph c (2 * r)).ConnectedComponent) (x : ClusterSpace)
    (hx : componentCutoff (centreGraph c (2 * r)) θ s x ≠ 0) :
    x ∈ ball (c (clusterAnchor (centreGraph c (2 * r)) s))
      (r + ((N : ℝ) - 1) * (2 * r)) := by
  obtain ⟨i, hi, hix⟩ := componentCutoff_nonzero _ θ s x hx
  have hpath : (centreGraph c (2 * r)).Reachable i
      (clusterAnchor (centreGraph c (2 * r)) s) :=
    SimpleGraph.ConnectedComponent.exact (hi.trans (clusterAnchor_mem _ s).symm)
  have hd := dist_le_of_reachable (centreGraph c (2 * r)) c (by positivity)
    (fun _ _ h => h.2) hpath
  simp only [Fintype.card_fin] at hd
  have hp := Metric.mem_ball.mp (hsupp i x hix)
  exact Metric.mem_ball.mpr (lt_of_le_of_lt
    (dist_triangle x (c i) _) (add_lt_add_of_lt_of_le hp hd))

/-- Nonnegative smooth cutoffs have zero derivative at every zero. Thus
the disjoint active-support assertion also includes derivative support. -/
theorem componentCutoff_derivative_zero (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ) (hθ : ∀ i x, 0 ≤ θ i x ∧ θ i x ≤ 1)
    (s : G.ConnectedComponent) (x : ClusterSpace)
    (hx : componentCutoff G θ s x = 0) : fderiv ℝ (componentCutoff G θ s) x = 0 :=
  fderiv_eq_zero_of_nonneg (fun y => (componentCutoff_bounds G θ hθ s y).1) hx

theorem componentCutoff_derivative_bound (G : SimpleGraph (Fin N))
    (θ : Fin N → ClusterSpace → ℝ)
    (hθ : ∀ i x, 0 ≤ θ i x ∧ θ i x ≤ 1)
    (hd : ∀ i, Differentiable ℝ (θ i)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i x, ‖fderiv ℝ (θ i) x‖ ≤ B)
    (s : G.ConnectedComponent) (x : ClusterSpace) :
    ‖fderiv ℝ (componentCutoff G θ s) x‖ ≤ (N : ℝ) * B := by
  classical
  have he := hasFDerivAt_clusterCutoff
    (fun i : {i // G.connectedComponentMk i = s} => θ i)
    (fun i => fderiv ℝ (θ i) x) x (fun i => (hd i x).hasFDerivAt)
  change HasFDerivAt (componentCutoff G θ s) _ x at he
  rw [he.fderiv]
  refine (norm_fderiv_clusterCutoff_le
    (fun i : {i // G.connectedComponentMk i = s} => θ i)
    (fun i : {i // G.connectedComponentMk i = s} => fderiv ℝ (θ i) x)
    x (fun i => hθ i x)).trans ?_
  calc
    _ ≤ ∑ _i : {i // G.connectedComponentMk i = s}, B :=
      Finset.sum_le_sum (fun i _ => hbound i x)
    _ = (Fintype.card {i // G.connectedComponentMk i = s} : ℝ) * B := by simp
    _ ≤ (N : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      have hc : Fintype.card {i // G.connectedComponentMk i = s} ≤ N := by
        simpa only [Fintype.card_fin] using
          (Fintype.card_subtype_le (fun i => G.connectedComponentMk i = s))
      exact_mod_cast hc

end GptLean.RemovalGeometry
