import PfHk.CommonScalarDomain
import GptLean.PhysicalFockSeparable

/-! The common electronic/radiation form domain is contained in the actual
external multiplier domain for all admissible identical-particle coefficients.
No external domain or multiplier condition is assumed. -/

noncomputable section
namespace PfHk.PhysicalCommonFormDomain

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.PhysicalPairDuality PfHk.PhysicalLocalEnergy

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable {N : ℕ}

local instance commonPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

theorem scalar_coordinate_integrable (v : ScalarPotential) (n : Fin N)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (fun X => |CoordinateSobolev.coordinateCoefficient n
      (v.val : PhysicalSourceCoordinates.Position → ℝ) X| *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2) volume := by
  let q := ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
    (electronic (Fin N × Fin 3) (fun _ => 0) u)
  have hval : ElectronicH1Space.value q = inclusion (Fin N × Fin 3) (fun _ => 0) u := rfl
  exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) => Integrable
    (fun X => |CoordinateSobolev.coordinateCoefficient n
      (v.val : PhysicalSourceCoordinates.Position → ℝ) X| * ‖ψ X‖ ^ 2) volume) hval).mp
    (LpSumCoordinateDomain.scalar_density v n q)

theorem externalDomain (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    ExternalDomain (fun _ => 0) (vector A) (positive v c) (negative v c) u := by
  let q := ElectronicH1Complex.realEquiv (E := PhotonFock) (I := Fin N × Fin 3)
    (electronic (Fin N × Fin 3) (fun _ => 0) u)
  have hval : ElectronicH1Space.value q = inclusion (Fin N × Fin 3) (fun _ => 0) u := rfl
  constructor
  · intro i
    have h := LpSumCoordinateDomain.vector_multiplier A i.1 i.2 q
    exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
      MemLp (fun X => vector A i X • ψ X) 2 volume) hval).mp h
  · have h := positive_multiplier v c hc q
    exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
      MemLp (fun X => positive v c X • ψ X) 2 volume) hval).mp h
  · have h := negative_multiplier v c hc q
    exact (congrArg (fun ψ : WaveSpace (Fin N × Fin 3) =>
      MemLp (fun X => negative v c X • ψ X) 2 volume) hval).mp h

end PfHk.PhysicalCommonFormDomain
