import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sequences
import Mathlib.Tactic.NormNum

/-!
The Hilbert-valued three-dimensional Sobolev estimate used for physical
particle marginals. The smooth-core estimate comes from Mathlib's Sobolev
inequality. Its full-domain membership conclusion follows from density
in the reference norm and lower semicontinuity under convergence in measure.
The source core and its ordinary derivative bound are explicit graph data.
-/

noncomputable section

namespace GptLean.PhysicalPairSobolev

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

abbrev Position := EuclideanSpace ℝ (Fin 3)

def sobolevConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Position) 2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Sobolev constant is independent of the Hilbert fiber, including
infinite-dimensional photon and spectral-ensemble fibers. -/
theorem smooth_sobolev_bound {u : Position → H}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm u 6 volume ≤ sobolevConstant * eLpNorm (fderiv ℝ u) 2 volume := by
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Position)
    hu hc (p := 2) (p' := 6) (by norm_num)
    (by norm_num [Position]) (by norm_num [Position])
  simpa only [sobolevConstant, ENNReal.coe_ofNat, NNReal.coe_ofNat] using h

section DenseCore

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  (inclusion : Q →L[ℝ] Lp H 2 (volume : Measure Position))
  (core : Set Q) (hdense : Dense core)
  (representative : Q → Position → H)
  (hrep : ∀ q ∈ core, representative q =ᵐ[volume] inclusion q)
  (hsmooth : ∀ q ∈ core, ContDiff ℝ 1 (representative q))
  (hcompact : ∀ q ∈ core, HasCompactSupport (representative q))
  (C : ℝ≥0)
  (hderivative : ∀ q ∈ core,
    eLpNorm (fderiv ℝ (representative q)) 2 volume ≤ C * ENNReal.ofReal ‖q‖)

include hdense hrep hsmooth hcompact hderivative

/-- A reference-form core with its ordinary derivative estimate supplies
L6 membership on the whole reference domain. The proof constructs a core
approximation and passes the Sobolev bound through its actual L2 limit. -/
theorem memLp_six_of_dense_core (q : Q) : MemLp (inclusion q) 6 volume := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense q)
  have hmeasure := tendstoInMeasure_of_tendsto_Lp ((inclusion.continuous.tendsto q).comp hlim)
  have hbounded : ∀ᶠ n in atTop, ‖v n‖ ≤ ‖q‖ + 1 :=
    (hlim.norm.eventually (eventually_lt_nhds (by linarith : ‖q‖ < ‖q‖ + 1))).mono
      (fun _ h => h.le)
  have hnorm : eLpNorm (inclusion q) 6 volume ≤
      sobolevConstant * C * ENNReal.ofReal (‖q‖ + 1) := by
    apply eLpNorm_le_of_tendstoInMeasure _ hmeasure
      (fun n => Lp.aestronglyMeasurable (inclusion (v n)))
    filter_upwards [hbounded] with n hn
    change eLpNorm (inclusion (v n)) 6 volume ≤ _
    rw [← eLpNorm_congr_ae (p := 6) (hrep (v n) (hv n))]
    calc
      eLpNorm (representative (v n)) 6 volume ≤
          sobolevConstant * eLpNorm (fderiv ℝ (representative (v n))) 2 volume :=
        smooth_sobolev_bound (hsmooth (v n) (hv n)) (hcompact (v n) (hv n))
      _ ≤ sobolevConstant * (C * ENNReal.ofReal ‖v n‖) :=
        mul_le_mul' le_rfl (hderivative (v n) (hv n))
      _ ≤ sobolevConstant * C * ENNReal.ofReal (‖q‖ + 1) := by
        rw [mul_assoc]
        gcongr
  exact ⟨Lp.aestronglyMeasurable _, hnorm.trans_lt (by finiteness)⟩

end DenseCore

end GptLean.PhysicalPairSobolev
