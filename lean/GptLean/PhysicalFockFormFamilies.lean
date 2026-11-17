import GptLean.PhysicalFockFormCalculus

/-!
Concrete one-photon form families for number and bounded operator squares.
The frame comes from a countable Hilbert basis of the actual one-photon
L2 space. No completeness or Parseval identity is supplied as a premise.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhysicalL2HilbertSum PhotonLocalizationFormBounds
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false

section Frame
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def frameKernel (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (i : ℕ) : H :=
  ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i).comp U.toContinuousLinearMap).adjoint 1

theorem frameKernel_inner (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (i : ℕ) (u : H) :
    ⟪frameKernel U i, u⟫_ℂ = U u i := by
  rw [frameKernel, ContinuousLinearMap.adjoint_inner_left]
  change ⟪(1 : ℂ), U u i⟫_ℂ = _
  simp only [RCLike.inner_apply, map_one, mul_one]

theorem frameKernel_mass (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (u : H) :
    (∑' i, ENNReal.ofReal (‖⟪frameKernel U i, u⟫_ℂ‖ ^ 2)) = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hs := coordinate_mass_hasSum (fun _ : ℕ => ℂ) (U u)
  calc
    _ = ∑' i, ENNReal.ofReal (‖U u i‖ ^ 2) :=
      tsum_congr (fun i => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)) (frameKernel_inner U i u))
    _ = ENNReal.ofReal (‖U u‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable).symm.trans
        (congrArg ENNReal.ofReal hs.tsum_eq)
    _ = _ := congrArg (fun r : ℝ => ENNReal.ofReal (r ^ 2)) (U.norm_map u)

end Frame

def onePhotonAnalysis : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (padding (H := ℂ) (spatialIndexEmbedding photonMeasure)).comp
    (spatialBasis photonMeasure).repr.toLinearIsometry

def numberFamily : OnePhotonFormFamily := frameKernel onePhotonAnalysis

theorem numberFamily_value (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue numberFamily u = ENNReal.ofReal (‖u‖ ^ 2) :=
  frameKernel_mass onePhotonAnalysis u

def boundedSquareFamily (A : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure) :
    OnePhotonFormFamily := fun i => A.adjoint (numberFamily i)

theorem boundedSquareFamily_value
    (A : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure) (u : Lp ℂ 2 photonMeasure) :
    onePhotonFamilyValue (boundedSquareFamily A) u = ENNReal.ofReal (‖A u‖ ^ 2) := by
  have h : onePhotonFamilyValue (boundedSquareFamily A) u = onePhotonFamilyValue numberFamily (A u) :=
    tsum_congr (fun i => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))
      (A.adjoint_inner_left u (numberFamily i)))
  exact h.trans (numberFamily_value (A u))

section Normal
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {R : Gaussian.RankOneData PhotonFock T}
  (normal : PhotonLocalizationChannel.NormalTraceData R)
  (F : PhotonLocalizationChannel.NormalFunctionalData R)

theorem numberObservable_rankOne (u : PhotonFock) :
    (familyObservable normal F numberFamily).expectation (R.rankOne u) =
      photonNumberForm photonMeasure u := by
  have h := familyObservable_slices normal F numberFamily u
  exact h.trans ((congrArg (fun v => fockForm v (fockSlices u)) (funext numberFamily_value)).trans
    (fockSlices_number u))

end Normal
end GptLean.PhysicalFock
