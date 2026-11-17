import GptLean.ElectronicH1Momentum
import GptLean.PhysicalPFFieldTests

/-! The tested physical current has a symmetric first-order graph action. -/

noncomputable section

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private def subtractScaled {Q W : Type*} [TopologicalSpace Q] [AddCommGroup Q] [Module ℂ Q]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f g : Q →L[ℂ] W) (e : ℝ) : Q →L[ℂ] W := f - (e : ℂ) • g

private theorem subtract_pair {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v pu pv fu fv : H) (e : ℝ)
    (hp : ⟪u, pv⟫_ℂ = ⟪pu, v⟫_ℂ) (hf : ⟪u, fv⟫_ℂ = ⟪fu, v⟫_ℂ) :
    ⟪u, pv - (e : ℂ) • fv⟫_ℂ = ⟪pu - (e : ℂ) • fu, v⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hp, hf]

private theorem subtract_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u p d f : H) (a : H →L[ℂ] H) (e : ℝ)
    (hp : (⟪u, p⟫_ℂ).re = (⟪u, a d⟫_ℂ).re) :
    (⟪u, p - (e : ℂ) • a f⟫_ℂ).re = (⟪u, a (d - (e : ℂ) • f)⟫_ℂ).re := by
  simp only [map_sub, map_smul, inner_sub_right, Complex.sub_re, hp]

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (e : ℝ) (a : SmoothMultiplier I) (i : I)

local instance referenceModule : Module ℂ (Reference I V) :=
  (referenceNormedSpace I V).toModule

local instance referenceSMul : SMul ℂ (Reference I V) :=
  (referenceModule I V).toSMul

def testedCurrent : Reference I V →L[ℂ] WaveSpace I :=
  subtractScaled (Q := Reference I V) (W := WaveSpace I)
    ((a.momentum i).comp (electronic I V))
    (a.multiplier.comp (field I V C κ hκ M hbound i)) e

theorem testedCurrent_symmetric (u v : Reference I V) :
    ⟪inclusion I V u, testedCurrent I V C κ hκ M hbound e a i v⟫_ℂ =
      ⟪testedCurrent I V C κ hκ M hbound e a i u, inclusion I V v⟫_ℂ := by
  have hm := a.momentum_symmetric i (electronic I V u) (electronic I V v)
  have hf := weighted_field_symmetric I V C κ hκ M hbound i a.weight
    a.smooth.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u v
  exact subtract_pair (inclusion I V u) (inclusion I V v)
    (a.momentum i (electronic I V u)) (a.momentum i (electronic I V v))
    (a.multiplier (field I V C κ hκ M hbound i u))
    (a.multiplier (field I V C κ hκ M hbound i v)) e hm hf

theorem testedCurrent_diagonal (u : Reference I V) :
    (⟪inclusion I V u, testedCurrent I V C κ hκ M hbound e a i u⟫_ℂ).re =
      (⟪inclusion I V u, a.multiplier (covariant I V C κ hκ M hbound e i u)⟫_ℂ).re := by
  have hm := a.momentum_diagonal i (electronic I V u)
  exact subtract_diagonal (inclusion I V u) (a.momentum i (electronic I V u))
    ((-Complex.I) • ordinary I V i u) (field I V C κ hκ M hbound i u) a.multiplier e hm

end GptLean.PhysicalPFReference
