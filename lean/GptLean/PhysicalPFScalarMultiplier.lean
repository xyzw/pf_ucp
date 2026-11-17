import GptLean.ElectronicH1DifferentiableMultiplier
import GptLean.PhysicalBoundedScalar
import GptLean.PhysicalPFReference

/-! Bounded differentiable electronic scalars act on the actual common
PF domain. The radiation and potential coordinates are multiplied by
the same scalar and the covariant derivative has the exact product rule. -/

noncomputable section

namespace GptLean.PhysicalPFScalarMultiplier

open MeasureTheory PhysicalFock PhysicalPFReference ElectronicH1Multiplier
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 100000
set_option Elab.async false

variable {I : Type*} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (a : DifferentiableMultiplier I)

def electronicMultiply (u : ElectronicGraph I) : ElectronicGraph I :=
  let q := a.multiply (H := PhotonFock)
    (⟨u.val, u.property⟩ : ElectronicH1Space.H1 PhotonFock I)
  ⟨q.val, q.property⟩

theorem electronic_value (u : ElectronicGraph I) :
    ElectronicH1Complex.value (electronicMultiply a u) =
      a.multiplier (ElectronicH1Complex.value u) :=
  a.value_multiply (⟨u.val, u.property⟩ : ElectronicH1Space.H1 PhotonFock I)

theorem electronic_derivative (u : ElectronicGraph I) (i : I) :
    ElectronicH1Complex.derivative i (electronicMultiply a u) =
      a.multiplier (ElectronicH1Complex.derivative i u) +
        a.derivativeMultiplier i (ElectronicH1Complex.value u) :=
  a.derivative_multiply i (⟨u.val, u.property⟩ : ElectronicH1Space.H1 PhotonFock I)

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

def radiationMultiply : RadiationGraph I →L[ℂ] RadiationGraph I :=
  PhysicalBoundedScalar.multiplier (X := Position I) (H := RadiationGraphSpace) volume a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)

private theorem wave_multiplier_eq (u : WaveSpace I) :
    PhysicalBoundedScalar.multiplier (H := PhotonFock) volume a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u =
        a.multiplier u :=
  congrArg (fun L : WaveSpace I →L[ℂ] WaveSpace I => L u)
    (PhysicalBoundedScalar.multiplier_eq_realL2 (F := PhotonFock) volume a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded))

theorem radiation_value (u : RadiationGraph I) :
    spatialRadiationInclusion volume (radiationMultiply a u) =
      a.multiplier (spatialRadiationInclusion volume u) :=
  (PhysicalBoundedScalar.multiplier_compLpL (H := RadiationGraphSpace) (K := PhotonFock) volume a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
    radiationGraphInclusion u).trans (wave_multiplier_eq a _)

theorem radiation_output (u : RadiationGraph I) :
    spatialRadiationDerivative volume (radiationMultiply a u) =
      a.multiplier (spatialRadiationDerivative volume u) :=
  (PhysicalBoundedScalar.multiplier_compLpL (H := RadiationGraphSpace) (K := PhotonFock) volume a.weight
    a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
    radiationGraphDerivative u).trans (wave_multiplier_eq a _)

def potentialMultiply (u : PotentialGraph I V) : PotentialGraph I V :=
  ⟨(a.multiplier u.val.1, a.multiplier u.val.2), by
    filter_upwards [u.property,
      PhotonLocalization.realL2Multiplier_apply a.weight
        a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u.val.1,
      PhotonLocalization.realL2Multiplier_apply a.weight
        a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) u.val.2]
      with x hx h₁ h₂
    change a.multiplier u.val.2 x = (Real.sqrt (V x) : ℂ) • a.multiplier u.val.1 x
    change u.val.2 x = (Real.sqrt (V x) : ℂ) • u.val.1 x at hx
    exact h₂.trans ((congrArg (fun z : PhotonFock => a.weight x • z) hx).trans
      ((smul_comm (a.weight x) (Real.sqrt (V x) : ℂ) (u.val.1 x)).trans
        (congrArg (fun z : PhotonFock => (Real.sqrt (V x) : ℂ) • z) h₁.symm)))⟩

theorem potential_value (u : PotentialGraph I V) :
    PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _ (potentialMultiply V a u) =
      a.multiplier (PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _ u) := rfl

theorem potential_output (u : PotentialGraph I V) :
    PhysicalMultiplicationGraph.output (H := PhotonFock) volume _ (potentialMultiply V a u) =
      a.multiplier (PhysicalMultiplicationGraph.output (H := PhotonFock) volume _ u) := rfl

def multiply (u : Reference I V) : Reference I V :=
  ⟨(electronicMultiply a (electronic I V u),
      radiationMultiply a (radiationSource I V u), potentialMultiply V a (potentialSource I V u)), by
    change (ElectronicH1Complex.value (electronicMultiply a (electronic I V u)) -
        spatialRadiationInclusion volume (radiationMultiply a (radiationSource I V u)),
      ElectronicH1Complex.value (electronicMultiply a (electronic I V u)) -
        PhysicalMultiplicationGraph.inclusion (H := PhotonFock) volume _
          (potentialMultiply V a (potentialSource I V u))) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((electronic_value a _).trans
        ((congrArg a.multiplier (radiation_matches I V u).symm).trans
          (radiation_value a _).symm))
    · exact sub_eq_zero.mpr ((electronic_value a _).trans
        ((congrArg a.multiplier (potential_matches I V u).symm).trans
          (potential_value V a _).symm))⟩

theorem value_multiply (u : Reference I V) :
    inclusion I V (multiply V a u) = a.multiplier (inclusion I V u) :=
  electronic_value a _

theorem ordinary_multiply (u : Reference I V) (i : I) :
    ordinary I V i (multiply V a u) = a.multiplier (ordinary I V i u) +
      a.derivativeMultiplier i (inclusion I V u) := electronic_derivative a _ i

theorem radiation_multiply (u : Reference I V) :
    radiation I V (multiply V a u) = a.multiplier (radiation I V u) :=
  radiation_output a _

theorem potential_multiply (u : Reference I V) :
    potential I V (multiply V a u) = a.multiplier (potential I V u) := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

theorem field_multiply (u : Reference I V) (i : I) :
    field I V C κ hκ M hbound i (multiply V a u) =
      a.multiplier (field I V C κ hκ M hbound i u) := by
  apply Lp.ext
  filter_upwards [spatialField_ae volume C (κ i) (hκ i) M (hbound i)
      (radiationMultiply a (radiationSource I V u)),
    PhysicalBoundedScalar.multiplier_ae (H := RadiationGraphSpace) volume a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
      (radiationSource I V u),
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded)
      (field I V C κ hκ M hbound i u),
    spatialField_ae volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u)]
    with x h₁ h₂ h₃ h₄
  change spatialField volume C (κ i) (hκ i) M (hbound i)
      (radiationMultiply a (radiationSource I V u)) x = _
  exact h₁.trans ((congrArg (kernelField C (κ i x)) h₂).trans
    (((kernelField C (κ i x)).map_smul (a.weight x : ℂ) (radiationSource I V u x)).trans
      ((congrArg (fun z : PhotonFock => (a.weight x : ℂ) • z) h₄.symm).trans
        (by simpa only [Complex.coe_smul, field, ContinuousLinearMap.comp_apply,
          DifferentiableMultiplier.multiplier] using h₃.symm))))

private theorem covariant_algebra {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : H →L[ℂ] H) (d f b : H) (e : ℂ) :
    (-Complex.I) • (L d + b) - e • L f =
      L ((-Complex.I) • d - e • f) + (-Complex.I) • b := by
  rw [map_sub, map_smul, map_smul, smul_add]
  abel

theorem covariant_multiply (e : ℝ) (u : Reference I V) (i : I) :
    covariant I V C κ hκ M hbound e i (multiply V a u) =
      a.multiplier (covariant I V C κ hκ M hbound e i u) +
        (-Complex.I) • a.derivativeMultiplier i (inclusion I V u) := by
  exact (covariant_apply I V C κ hκ M hbound e i (multiply V a u)).trans
    ((congrArg₂ (· - ·)
      (congrArg (fun z : WaveSpace I => (-Complex.I) • z) (ordinary_multiply V a u i))
      (congrArg (fun z : WaveSpace I => (e : ℂ) • z)
        (field_multiply V a C κ hκ M hbound u i))).trans
      ((covariant_algebra a.multiplier (ordinary I V i u) (field I V C κ hκ M hbound i u)
        (a.derivativeMultiplier i (inclusion I V u)) (e : ℂ)).trans
          (congrArg (fun z : WaveSpace I => a.multiplier z +
            (-Complex.I) • a.derivativeMultiplier i (inclusion I V u))
            (covariant_apply I V C κ hκ M hbound e i u).symm)))

end GptLean.PhysicalPFScalarMultiplier
