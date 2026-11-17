import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith

/-!
Finite-orbit separation in Step 1 of the symmetric-tensor appendix.

The compact centered sphere and its smooth structure are not implemented
here. For any compact metric configuration space with a finite family of
isometric symmetries, the elementary finite-orbit radius and finite-cover
steps below supply the geometric part of the proposed atlas. Smooth bump
functions and their radial derivative estimates remain analytic inputs.
-/

namespace GptLean.SymmetricLift

open scoped BigOperators

/-- Finitely many positive scales have a common positive lower bound. -/
theorem finite_positive_scale {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ a, 0 < f a) : ∃ r : ℝ, 0 < r ∧ ∀ a, r ≤ f a := by
  classical
  have haux (s : Finset ι) : ∃ r : ℝ, 0 < r ∧ ∀ a ∈ s, r ≤ f a := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨r, hr, hbound⟩ := ih
      refine ⟨min r (f a), lt_min hr (hf a), ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound b hb)
  obtain ⟨r, hr, hbound⟩ := haux Finset.univ
  exact ⟨r, hr, fun a => hbound a (Finset.mem_univ a)⟩

/-- Balls around a finite set of orbit points can be made equal or disjoint. -/
theorem finite_orbit_balls {ι X : Type*} [Fintype ι] [MetricSpace X] (c : ι → X) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j,
      c i = c j ∨ Disjoint (Metric.ball (c i) r) (Metric.ball (c j) r) := by
  classical
  let f : ι × ι → ℝ := fun ij => if c ij.1 = c ij.2 then 1 else dist (c ij.1) (c ij.2) / 2
  have hf (ij : ι × ι) : 0 < f ij := by
    dsimp [f]
    split_ifs with h
    · norm_num
    · exact half_pos (dist_pos.mpr h)
  obtain ⟨r, hr, hbound⟩ := finite_positive_scale f hf
  refine ⟨r, hr, ?_⟩
  intro i j
  by_cases h : c i = c j
  · exact Or.inl h
  · right
    have hb := hbound (i, j)
    simp only [f, h, ite_false] at hb
    apply Metric.ball_disjoint_ball
    linarith

/-- Stabilizers leave the chosen ball invariant. -/
theorem stabilizer_ball_invariant {X : Type*} [MetricSpace X]
    (g : X ≃ᵢ X) (x : X) (r : ℝ) (hfix : g x = x) :
    g '' Metric.ball x r = Metric.ball x r := by
  rw [g.image_ball, hfix]

/-- The translates of a small ball under finite isometries are equal or disjoint. -/
theorem finite_isometric_translates {ι X : Type*} [Fintype ι] [MetricSpace X]
    (symmetry : ι → X ≃ᵢ X) (x : X) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j,
      symmetry i '' Metric.ball x r = symmetry j '' Metric.ball x r ∨
      Disjoint (symmetry i '' Metric.ball x r) (symmetry j '' Metric.ball x r) := by
  obtain ⟨r, hr, hballs⟩ := finite_orbit_balls (fun i => symmetry i x)
  refine ⟨r, hr, ?_⟩
  intro i j
  rw [(symmetry i).image_ball, (symmetry j).image_ball]
  rcases hballs i j with h | h
  · exact Or.inl (congrArg (fun y => Metric.ball y r) h)
  · exact Or.inr h

/-- The orbit-separating balls have a finite subcover on any compact set. -/
theorem finite_orbit_atlas {ι X : Type*} [Fintype ι] [MetricSpace X]
    (action : ι → X → X) (s : Set X) (hs : IsCompact s) :
    ∃ r : X → ℝ,
      (∀ x, 0 < r x) ∧
      (∀ x i j, action i x = action j x ∨
        Disjoint (Metric.ball (action i x) (r x)) (Metric.ball (action j x) (r x))) ∧
      ∃ centers : Finset X, s ⊆ ⋃ x ∈ centers, Metric.ball x (r x) := by
  classical
  choose r hr hballs using fun x => finite_orbit_balls (fun i => action i x)
  refine ⟨r, hr, hballs, ?_⟩
  apply hs.elim_finite_subcover (fun x => Metric.ball x (r x))
  · intro x
    exact Metric.isOpen_ball
  · intro x _
    exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hr x)⟩

end GptLean.SymmetricLift
