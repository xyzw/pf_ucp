import GptLean.ElectronicH1Core
import GptLean.PhysicalPairDerivativeBounds
import GptLean.PhysicalPairRealization

/-!
The three-dimensional Hilbert-valued Sobolev embedding on the actual weak
H1 graph. Smooth-core density and the coordinate derivative estimate are
proved constructions, so the L6 conclusion has no core or derivative-bound
premise. Combining it with Holder constructs density-current pairs in the
article space from an H1 source and L2 covariant derivative vectors.
-/

noncomputable section

namespace GptLean.PhysicalPairH1Sobolev

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open MeasureTheory Filter ElectronicH1Space ElectronicH1Core PhysicalPairDerivativeBounds
open PhysicalPairSpace
open scoped ENNReal NNReal ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The full derivative is controlled by the actual weak-coordinate graph norm. -/
theorem smooth_derivative_bound (f : Position → H)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    eLpNorm (fderiv ℝ f) 2 volume ≤ 3 * ENNReal.ofReal ‖ofSmoothCompact f hf hs‖ := by
  have hcoord (i : Fin 3) :
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) =ᵐ[volume]
        derivative i (ofSmoothCompact f hf hs) := by
    exact (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single i 1))).coeFn_toLp.symm
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    eLpNorm_le_card_mul (fun i => derivative i (ofSmoothCompact f hf hs)) hcoord
      (fun i => norm_derivative_le (ofSmoothCompact f hf hs) i)

def smoothRepresentative (u : H1 H (Fin 3)) : Position → H := by
  classical
  exact if h : u ∈ smoothCore H 3 then h.choose else 0

theorem smoothRepresentative_spec (u : H1 H (Fin 3)) (h : u ∈ smoothCore H 3) :
    ∃ (hf : ContDiff ℝ ∞ (smoothRepresentative u))
      (hs : HasCompactSupport (smoothRepresentative u)),
      u = ofSmoothCompact (smoothRepresentative u) hf hs := by
  classical
  simpa only [smoothRepresentative, dite_eq_left h] using h.choose_spec

/-- Every member of the constructed H1 graph has an L6 source representative. -/
theorem value_memLp_six (u : H1 H (Fin 3)) : MemLp (value u) 6 volume := by
  have hrep : ∀ q ∈ smoothCore H 3,
      smoothRepresentative q =ᵐ[volume] value q := by
    intro q hq
    obtain ⟨hf, hs, heq⟩ := smoothRepresentative_spec q hq
    calc
      smoothRepresentative q =ᵐ[volume]
          (value (ofSmoothCompact (smoothRepresentative q) hf hs) : Position → H) :=
        (hf.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp.symm
      _ =ᵐ[volume] value q := EventuallyEq.of_eq
        (congrArg (fun v : H1 H (Fin 3) => (value v : Position → H)) heq.symm)
  have hsmooth : ∀ q ∈ smoothCore H 3,
      ContDiff ℝ 1 (smoothRepresentative q) := by
    intro q hq
    obtain ⟨hf, _, _⟩ := smoothRepresentative_spec q hq
    exact hf.of_le (by simp)
  have hcompact : ∀ q ∈ smoothCore H 3,
      HasCompactSupport (smoothRepresentative q) := by
    intro q hq
    obtain ⟨_, hs, _⟩ := smoothRepresentative_spec q hq
    exact hs
  have hderivative : ∀ q ∈ smoothCore H 3,
      eLpNorm (fderiv ℝ (smoothRepresentative q)) 2 volume ≤
        (3 : ℝ≥0∞) * ENNReal.ofReal ‖q‖ := by
    intro q hq
    obtain ⟨hf, hs, heq⟩ := smoothRepresentative_spec q hq
    simpa only [← heq, ENNReal.coe_ofNat] using
      smooth_derivative_bound (smoothRepresentative q) hf hs
  exact PhysicalPairSobolev.memLp_six_of_dense_core
    (H := H) (Q := H1 H (Fin 3)) value (smoothCore H 3)
    dense_smoothCore smoothRepresentative hrep hsmooth hcompact 3 hderivative u

section ComplexSource

variable [InnerProductSpace ℂ H]

/-- The article pair of an actual H1 source. The only derivative inputs
are L2 vectors, which the physical form must identify as covariant derivatives. -/
def ofH1Source (N : ℕ) (u : H1 H (Fin 3))
    (d : Fin 3 → Lp H 2 (volume : Measure Position)) : Pair :=
  PhysicalPairRealization.ofSource N (value u) (fun i => d i)
    (Lp.memLp _) (value_memLp_six u) (fun i => Lp.memLp (d i))

end ComplexSource

end GptLean.PhysicalPairH1Sobolev
