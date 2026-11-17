import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.Abel

/-! Differentiation through an arbitrary closed operator graph, proved by
integrating its graph-valued derivative. This allows the ordinary sphere
gradient to commute with time differentiation without assuming angular
second derivatives of a physical gauge. -/

noncomputable section
namespace PfHk.ClosedGraphDifferentiation

open MeasureTheory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_snd (G : Submodule ℝ (H × E)) (hclosed : IsClosed (G : Set (H × E)))
    (huniq : ∀ v ∈ G, v.1 = 0 → v.2 = 0)
    {z dz : ℝ → H} {p dp : ℝ → E}
    (hz : ∀ t, HasDerivAt z (dz t) t) (hdz : Continuous dz) (hdp : Continuous dp)
    (hpair : ∀ t, (z t, p t) ∈ G) (hderivativePair : ∀ t, (dz t, dp t) ∈ G) (t : ℝ) :
    HasDerivAt p (dp t) t := by
  letI : CompleteSpace G := hclosed.completeSpace_coe
  let D : ℝ → G := fun s => ⟨(dz s, dp s), hderivativePair s⟩
  have hD : Continuous D := (hdz.prodMk hdp).subtype_mk _
  let L₁ : G →L[ℝ] H := (ContinuousLinearMap.fst ℝ H E).comp G.subtypeL
  let L₂ : G →L[ℝ] E := (ContinuousLinearMap.snd ℝ H E).comp G.subtypeL
  have hrepr (s : ℝ) : p s = p 0 + ∫ v in (0 : ℝ)..s, dp v := by
    let v : G := ∫ w in (0 : ℝ)..s, D w
    have h₁ : L₁ v = z s - z 0 := by
      rw [show L₁ v = ∫ w in (0 : ℝ)..s, dz w from
        (L₁.intervalIntegral_comp_comm (hD.intervalIntegrable 0 s)).symm]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hz w)
        (hdz.intervalIntegrable 0 s)
    have h₂ : L₂ v = ∫ w in (0 : ℝ)..s, dp w :=
      (L₂.intervalIntegral_comp_comm (hD.intervalIntegrable 0 s)).symm
    have hsub := G.sub_mem (G.sub_mem (hpair s) (hpair 0)) v.property
    have hzero : ((z s, p s) - (z 0, p 0) - (v : H × E)).1 = 0 := by
      change z s - z 0 - L₁ v = 0
      rw [h₁, sub_self]
    have hout := huniq _ hsub hzero
    change p s - p 0 - L₂ v = 0 at hout
    rw [h₂] at hout
    have he := sub_eq_zero.mp hout
    exact eq_add_of_sub_eq' he
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hdp.intervalIntegrable 0 t) hdp.stronglyMeasurable.stronglyMeasurableAtFilter hdp.continuousAt
  have h := hi.const_add (p 0)
  convert h using 1
  exact funext hrepr

end PfHk.ClosedGraphDifferentiation
