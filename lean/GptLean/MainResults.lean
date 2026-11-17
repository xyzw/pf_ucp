import GptLean.DFT
import GptLean.SoftPurification
import GptLean.Closure

/-!
Assembly of the main functional results for the current manuscript.

Every analytic interface is a theorem parameter. In particular this is a
conditional verification and not an instantiation by continuum PF states.
The removal and tag error formulas imply recovery rather than assuming it.
Mixed closedness is derived using `Closure.search_lowerSemicontinuous`.
Fenchel–Moreau and the density-matrix mixture operation are allowed background.
-/

namespace GptLean.MainResults

open Filter Topology
open scoped ENNReal

variable {P M D V : Type*}

/-- The two physical constructions entering soft purification. The displayed
cost and exact-constraint fields are residual analytic proof obligations.
Only finite-energy states belong to the abstract state types. -/
structure SoftPhotonInputs (A : DFT.StateModel P D) (B : DFT.StateModel M D) where
  remove : M → ℕ → M
  tag : M → ℕ → P
  softEnergy : M → ℕ → ℝ
  k : ℕ → ℝ
  a : ℕ → ℝ
  b : ℕ → ℝ
  C : ℝ
  e : ℝ
  N : ℝ
  C_nonneg : 0 ≤ C
  e_nonneg : 0 ≤ e
  k_nonneg : ∀ n, 0 ≤ k n
  k_zero : Tendsto k atTop (𝓝 0)
  a_zero : Tendsto a atTop (𝓝 0)
  b_zero : Tendsto b atTop (𝓝 0)
  soft_bounds : ∀ m n, 0 ≤ softEnergy m n ∧ softEnergy m n ≤ B.energy m
  remove_pair : ∀ m n, B.density (remove m n) = B.density m
  tag_pair : ∀ m n, A.density (tag m n) = B.density (remove m n)
  remove_cost : ∀ m n, B.energy (remove m n) ≤ B.energy m - softEnergy m n +
    C * SoftPurification.removalError e (k n) (a n) (b n) (softEnergy m n)
  tag_cost : ∀ m n, A.energy (tag m n) ≤ B.energy (remove m n) +
    k n + N * e ^ 2 * b n ^ 2

theorem exactRecovery (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (I : SoftPhotonInputs A B) : DFT.ExactRecovery A B :=
  SoftPurification.pure_approximation B.energy A.energy B.density A.density
    I.remove I.tag I.softEnergy I.k I.a I.b I.C I.e I.N I.C_nonneg I.e_nonneg
    I.k_nonneg I.k_zero I.a_zero I.b_zero I.soft_bounds I.remove_pair I.tag_pair
    I.remove_cost I.tag_cost

/-- Current `many-electron-pure-ensemble-equality`, before convex duality. -/
theorem pure_mixed_equality (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (emb : DFT.PureEmbedding A B) (I : SoftPhotonInputs A B) :
    ∀ d, DFT.search A d = DFT.search B d :=
  DFT.pure_eq_mixed A B emb (exactRecovery A B I)

/-- The main equalities, convexity, closedness, exact representability and
rank-one attainment criterion assembled without assuming any target equality.

`hminimizer` is the attained-search plus quantitative number estimate, to be
supplied using the attainment module and the optimizer layer-cake bound.
`hclosed` is the varying-constraint photon-loss interface. These remain
paper-specific obligations. `fm` is the permitted standard duality theorem.
-/
theorem functional_identification
    [AddCommGroup D] [Module ℝ D] [TopologicalSpace D] [FirstCountableTopology D]
    (A : DFT.StateModel P D) (B : DFT.StateModel M D)
    (emb : DFT.PureEmbedding A B) (I : SoftPhotonInputs A B)
    (number : M → ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C)
    (hpositive : ∀ m, 0 ≤ B.energy m) (m₀ : M)
    (hmix : DFT.MixtureClosed B)
    (hminimizer : ∀ d, DFT.search B d < ⊤ →
      ∃ m, B.density m = d ∧ (B.energy m : EReal) = DFT.search B d ∧
        number m ≤ ENNReal.ofReal (C * (1 + B.energy m)))
    (hclosed : Closure.BoundedConstraintClosure B number)
    (pair : V → D → ℝ) (fm : DFT.FenchelMoreau pair) :
    (∀ d, DFT.search A d = DFT.search B d ∧ DFT.search A d = DFT.lieb A pair d) ∧
    DFT.ConvexEpigraph (DFT.search A) ∧ LowerSemicontinuous (DFT.search A) ∧
    Set.range A.density = Set.range B.density ∧
    Convex ℝ (Set.range A.density) ∧
    (∀ d, DFT.Attained A d ↔ ∃ m, m ∈ Set.range emb.toMixed ∧
      B.density m = d ∧ (B.energy m : EReal) = DFT.search B d) := by
  have recovery := exactRecovery A B I
  have hlsc := Closure.search_lowerSemicontinuous B number C hC hpositive hminimizer hclosed
  have hconvex := DFT.mixed_search_convex B hmix
  refine ⟨fun d => ⟨DFT.pure_eq_mixed A B emb recovery d,
    DFT.pure_eq_lieb A B emb recovery pair fm 0 hpositive m₀ hconvex hlsc d⟩,
    DFT.pure_search_convex A B emb recovery hmix,
    DFT.pure_search_lowerSemicontinuous A B emb recovery hlsc,
    DFT.pure_mixed_representability A B emb recovery,
    DFT.pure_range_convex A B emb recovery hmix,
    DFT.pure_attained_iff_rank_one A B emb recovery⟩

/-- Zero-coupling relaxation from nonnegative radiation, partial trace,
and arbitrarily inexpensive soft tags. The reduction is not an energy-
preserving embedding because a general total state has positive radiation. -/
theorem zero_coupling_equality {Electronic : Type*}
    (total : DFT.StateModel P D) (electronic : DFT.StateModel Electronic D)
    (partialTrace : P → Electronic) (radiation : P → ℝ)
    (hpair : ∀ p, electronic.density (partialTrace p) = total.density p)
    (hsplit : ∀ p, total.energy p = electronic.energy (partialTrace p) + radiation p)
    (hpositive : ∀ p, 0 ≤ radiation p)
    (softTags : DFT.ExactRecovery total electronic) (d : D) :
    DFT.search total d = DFT.search electronic d := by
  apply le_antisymm
  · refine le_iInf₂ fun m hm => DFT.ereal_le_of_epsilon fun ε hε => ?_
    obtain ⟨p, hp, he⟩ := softTags m ε hε
    exact (DFT.search_le total (hp.trans hm)).trans (EReal.coe_le_coe he)
  · refine le_iInf₂ fun p hp => ?_
    have he : electronic.energy (partialTrace p) ≤ total.energy p := by
      rw [hsplit]
      exact le_add_of_nonneg_right (hpositive p)
    exact (DFT.search_le electronic ((hpair p).trans hp)).trans (EReal.coe_le_coe he)

end GptLean.MainResults
