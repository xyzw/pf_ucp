import PfHk.PhysicalLocalEnergyBallCutoff
import PfHk.SmoothCutoffBounds

/-! Construction of the scalar ball cutoffs from the fixed smooth bump
already used for photon localization. The derivative constant is uniform
in the electronic center and radius. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean
open GptLean.ElectronicH1Multiplier GptLean.PhotonLocalizationKernelCutoffs

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem exists_ballCutoff_constant :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x₀ : EuclideanSpace ℝ I) (r : ℝ), 0 < r → Nonempty (BallCutoff x₀ r L) := by
  obtain ⟨L, _B₂, hL, _hB₂, hfamily⟩ := SmoothCutoffBounds.exists_retained_twice I
  refine ⟨L, hL, fun x₀ r hr => ?_⟩
  obtain ⟨a, ha, hfirst, _hsecond⟩ := hfamily x₀ r hr
  refine ⟨{
    multiplier := a.scalar
    nonneg := ?_
    le_one := ?_
    eq_one := ?_
    eq_zero := ?_
    gradient_bound := hfirst }⟩
  · intro x
    exact (congrFun ha x).symm ▸ retained_nonneg r (x - x₀)
  · intro x
    exact (congrFun ha x).symm ▸ retained_le_one r (x - x₀)
  · intro x hx
    exact (congrFun ha x).trans (retained_eq_one hr
      (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le))
  · intro x hx
    have hdist : 2 * r ≤ dist x x₀ := not_lt.mp hx
    exact (congrFun ha x).trans (retained_eq_zero hr
      (by simpa only [dist_eq_norm] using hdist))

def ballCutoffConstant : ℝ := Classical.choose (exists_ballCutoff_constant (I := I))

theorem ballCutoffConstant_nonneg : 0 ≤ ballCutoffConstant (I := I) :=
  (Classical.choose_spec (exists_ballCutoff_constant (I := I))).1

def ballCutoff (x₀ : EuclideanSpace ℝ I) (r : ℝ) (hr : 0 < r) :
    BallCutoff x₀ r (ballCutoffConstant (I := I)) :=
  Classical.choice ((Classical.choose_spec (exists_ballCutoff_constant (I := I))).2 x₀ r hr)

end PfHk.PhysicalLocalEnergy
