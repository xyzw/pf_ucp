import PfHk.PhysicalOpenUCPCoefficients
import PfHk.PhysicalFermionicCoefficients

/-! One-body coefficient regularity on an open set, without any Lp control
near its excluded set. Compact-subset bounds express the ordinary local
Lp hypotheses. Distributional divergence uses tests supported in the set. -/

noncomputable section
namespace PfHk.PhysicalOpenUCPCoefficients

open MeasureTheory GptLean GptLean.PhysicalPairDuality GptLean.SymmetricLift
  GptLean.PhysicalSourceCoordinates PfHk.FriedrichsDivergenceBackground
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

structure RegularityOn (A : VectorPotential) (v : ScalarPotential)
    (Ω : Set Position) where
  exponent : ℝ
  exponent_gt_two : 2 < exponent
  divergence : Position → ℝ
  vector_local : ∀ j (K : Set Position), IsCompact K → K ⊆ Ω →
    MemLp (fun x => A.val x j) 6 (volume.restrict K)
  scalar_local : ∀ (K : Set Position), IsCompact K → K ⊆ Ω →
    MemLp (v.val : Position → ℝ) (ENNReal.ofReal exponent) (volume.restrict K)
  divergence_local : ∀ (K : Set Position), IsCompact K → K ⊆ Ω →
    MemLp divergence (ENNReal.ofReal exponent) (volume.restrict K)
  weak_divergence : WeakDivergenceOn Ω (fun j x => A.val x j) divergence

private theorem common_radius {J : Type*} [Fintype J]
    (r : J → ℝ) (hr : ∀ j, 0 < r j) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ j, ρ ≤ r j := by
  classical
  have hfinite : ∀ s : Finset J, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ j ∈ s, ρ ≤ r j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨R, hR, le_rfl, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨ρ, hρ, hρR, hρr⟩ := ih
      refine ⟨min ρ (r j), lt_min hρ (hr j), (min_le_left _ _).trans hρR, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hρr k hk)
  obtain ⟨ρ, hρ, hρR, hρr⟩ := hfinite Finset.univ
  exact ⟨ρ, hρ, hρR, fun j => hρr j (Finset.mem_univ j)⟩

private theorem closed_ball_inside {Ω : Set Position} (hΩ : IsOpen Ω)
    {o : Position} (ho : o ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall o r ⊆ Ω := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hΩ o ho
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx
  apply hball
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))

variable {N : ℕ} {A : VectorPotential} {v : ScalarPotential} {Ω : Set Position}
  {U : Set (GptLean.SymmetricLift.Configuration N)}

private theorem RegularityOn.local_bounds (h : RegularityOn A v Ω)
    (hΩ : IsOpen Ω) {X : GptLean.SymmetricLift.Configuration N}
    (hcoords : ∀ n, (split n X).1 ∈ Ω) (hcoll : X ∈ distinctConfigurations N)
    (c : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ LocalBounds
      (PhysicalCommonFormDomain.vectorCoefficient A) (fun _ => h.divergence)
      (fun _ => (v.val : Position → ℝ))
      (fun Y => c * PhysicalCoulombH1.potential N Y) h.exponent h.exponent X ρ := by
  have hballs : ∀ n : Fin N, ∃ r : ℝ, 0 < r ∧ Metric.closedBall (split n X).1 r ⊆ Ω :=
    fun n => closed_ball_inside hΩ (hcoords n)
  choose r hr hball using hballs
  obtain ⟨R, hR, hB⟩ := PhysicalCoulombLocalBound.scaled_potential_local_memLp c hcoll
  obtain ⟨ρ, hρ, hρR, hρr⟩ := common_radius r hr hR
  have hsub (n : Fin N) : Metric.ball (split n X).1 ρ ⊆ Metric.closedBall (split n X).1 (r n) :=
    (Metric.ball_subset_ball (hρr n)).trans Metric.ball_subset_closedBall
  refine ⟨ρ, hρ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n j
    exact (h.vector_local j _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · intro n
    exact (h.divergence_local _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · intro n
    exact (h.scalar_local _ (isCompact_closedBall _ _) (hball n)).mono_measure
      (Measure.restrict_mono (hsub n) le_rfl)
  · exact hB.mono_measure (Measure.restrict_mono (Metric.ball_subset_ball hρR) le_rfl)
  · intro n φ hφ hφs hφsub
    exact h.weak_divergence φ hφ hφs (hφsub.trans ((hsub n).trans (hball n)))

def RegularityOn.data (h : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ X ∈ U, ∀ n, (split n X).1 ∈ Ω)
    (hcoll : U ⊆ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c) : Data N U where
  vectorCoefficient := PhysicalCommonFormDomain.vectorCoefficient A
  divergenceCoefficient := fun _ => h.divergence
  scalarCoefficient := fun _ => (v.val : Position → ℝ)
  boundedCoefficient := fun X => c * PhysicalCoulombH1.potential N X
  divergenceExponent := h.exponent
  scalarExponent := h.exponent
  divergenceExponent_gt_two := h.exponent_gt_two
  scalarExponent_gt_two := h.exponent_gt_two
  scalar_in_sum := fun _ => ⟨v, Filter.EventuallyEq.rfl⟩
  bounded_measurable :=
    (PhysicalCoulombLocalBound.scaled_potential_measurable c).aestronglyMeasurable
  bounded_nonneg := Filter.Eventually.of_forall
    (PhysicalCoulombLocalBound.scaled_potential_nonneg c hc)
  local_coefficients := fun X hX => h.local_bounds hΩ (hcoords X hX) (hcoll hX) c

@[simp] theorem RegularityOn.data_vector (h : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ X ∈ U, ∀ n, (split n X).1 ∈ Ω)
    (hcoll : U ⊆ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c) :
    (h.data hΩ hcoords hcoll c hc).vector = PhysicalCommonFormDomain.vector A := rfl

@[simp] theorem RegularityOn.data_scalar (h : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ X ∈ U, ∀ n, (split n X).1 ∈ Ω)
    (hcoll : U ⊆ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c) :
    (h.data hΩ hcoords hcoll c hc).scalar = PhysicalCommonFormDomain.scalar v c := rfl

@[simp] theorem RegularityOn.data_positive (h : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ X ∈ U, ∀ n, (split n X).1 ∈ Ω)
    (hcoll : U ⊆ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c) :
    (h.data hΩ hcoords hcoll c hc).positive = PhysicalCommonFormDomain.positive v c := rfl

@[simp] theorem RegularityOn.data_negative (h : RegularityOn A v Ω) (hΩ : IsOpen Ω)
    (hcoords : ∀ X ∈ U, ∀ n, (split n X).1 ∈ Ω)
    (hcoll : U ⊆ distinctConfigurations N) (c : ℝ) (hc : 0 ≤ c) :
    (h.data hΩ hcoords hcoll c hc).negative = PhysicalCommonFormDomain.negative v c := rfl

end PfHk.PhysicalOpenUCPCoefficients
