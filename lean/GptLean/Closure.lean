import GptLean.DFT
import Mathlib.Topology.Sequences
import Mathlib.Data.ENNReal.Real

/-!
The norm lower-semicontinuity step in `thm-unrestricted-attainment`.
It is derived from attained searches with a photon-number estimate and
closedness of bounded state families under converging constraints. The
latter is an explicit consequence required of the paper's photon-loss
lemma, not assumed to be a standard compactness theorem for PF states.
-/

namespace GptLean.Closure

open Filter Topology
open scoped ENNReal

variable {State Pair : Type*} [TopologicalSpace Pair]

/-- Retained-state compactness with varying constraints and fixed energy and
number caps. This does not claim compactness of the original total states. -/
def BoundedConstraintClosure (A : DFT.StateModel State Pair)
    (number : State → ℝ≥0∞) : Prop :=
  ∀ (s : ℕ → State) (d : Pair) (E M : ℝ),
    Tendsto (fun n => A.density (s n)) atTop (𝓝 d) →
    (∀ n, A.energy (s n) ≤ E) →
    (∀ n, number (s n) ≤ ENNReal.ofReal M) →
    ∃ state, A.density state = d ∧ A.energy state ≤ E

/-- The result uses extended-real values, including empty fibers. It proves
closedness of every sublevel rather than assuming lower semicontinuity. -/
theorem search_lowerSemicontinuous [FirstCountableTopology Pair]
    (A : DFT.StateModel State Pair) (number : State → ℝ≥0∞)
    (C : ℝ) (hC : 0 ≤ C) (hpositive : ∀ s, 0 ≤ A.energy s)
    (hminimizer : ∀ d, DFT.search A d < ⊤ →
      ∃ s, A.density s = d ∧ (A.energy s : EReal) = DFT.search A d ∧
        number s ≤ ENNReal.ofReal (C * (1 + A.energy s)))
    (hclosed : BoundedConstraintClosure A number) :
    LowerSemicontinuous (DFT.search A) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro bound
  induction bound with
  | bot =>
    have hempty : DFT.search A ⁻¹' Set.Iic ⊥ = ∅ := by
      ext d
      simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false, iff_false]
      exact DFT.search_ne_bot A 0 hpositive d
    rw [hempty]
    exact isClosed_empty
  | top => simp
  | coe E =>
    apply IsSeqClosed.isClosed
    intro x d hx hxd
    have hex : ∀ n, ∃ s, A.density s = x n ∧ A.energy s ≤ E ∧
        number s ≤ ENNReal.ofReal (C * (1 + E)) := by
      intro n
      have hxn : DFT.search A (x n) ≤ (E : EReal) := hx n
      obtain ⟨s, hs, he, hn⟩ := hminimizer (x n)
        (hxn.trans_lt (EReal.coe_lt_top E))
      have hE : A.energy s ≤ E := EReal.coe_le_coe_iff.mp (he.trans_le hxn)
      refine ⟨s, hs, hE, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hE) hC
    choose s hs he hn using hex
    have hden : Tendsto (fun n => A.density (s n)) atTop (𝓝 d) := by
      simpa only [hs] using hxd
    obtain ⟨state, hd, hE⟩ := hclosed s d E (C * (1 + E)) hden he hn
    exact (DFT.search_le A hd).trans (EReal.coe_le_coe hE)

end GptLean.Closure
