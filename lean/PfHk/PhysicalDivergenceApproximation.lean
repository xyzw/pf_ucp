import PfHk.PhysicalExternalOperator
import PfHk.CoordinateDivergenceApproximation
import PfHk.CoordinateComparisonSpectral

/-! Ordinary Friedrichs coefficient convergence yields the actual scalar
L2 approximation required by the physical weak operator expansion. -/

noncomputable section
namespace PfHk.PhysicalExternalOperator

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy PfHk.CoordinateSobolev
open PfHk.PhysicalOperatorDomain PfHk.FriedrichsDivergenceBackground
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option maxHeartbeats 60000

attribute [local irreducible] PhysicalPFReference.inclusion roughMultiply
  PhysicalPFReference.referenceSubspace HasMultiplier IsComparisonPair

variable {N : ℕ}

def divergenceApproximation_of_friedrichs (S : CoordinateSobolev.Data PhotonFock N)
    (spectral : ComparisonSpectralCalculus (I := Fin N × Fin 3))
    (joint : CoordinateComparisonSpectral.Data spectral)
    (A : Fin N → Fin 3 → GptLean.PhysicalSourceCoordinates.Position → ℝ)
    (d : Fin N → GptLean.PhysicalSourceCoordinates.Position → ℝ) (q : ℝ) (hq : 2 < q)
    (a : Approximation A d q)
    (u v : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : ∃ L, IsComparisonPair (fun _ => 0) u L)
    (hau : ∀ i : Fin N × Fin 3, HasMultiplier (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hav : ∀ i : Fin N × Fin 3, HasMultiplier (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) v))
    (hd : HasMultiplier (I := Fin N × Fin 3) (configurationDivergence d) (inclusion (Fin N × Fin 3) (fun _ => 0) u)) :
    DivergenceApproximation (fun _ => 0) (configurationVector A) (configurationDivergence d) u v
      (fun i => roughMultiply (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hau i))
      (fun i => roughMultiply (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hav i))
      (roughMultiply (I := Fin N × Fin 3) (configurationDivergence d) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hd) := by
  have hBu (n : Fin N) : ∃ w : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (1 / 2) (inclusion (Fin N × Fin 3) (fun _ => 0) u) w := by
    have hex := joint.form_value n (1 / 2) (by norm_num) (by norm_num) u
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have hBv (n : Fin N) : ∃ w : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (1 / 2) (inclusion (Fin N × Fin 3) (fun _ => 0) v) w := by
    have hex := joint.form_value n (1 / 2) (by norm_num) (by norm_num) v
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  have hq0 : 0 < q := by linarith only [hq]
  have hs : 0 ≤ 3 / q := by positivity
  have hs2 : 3 / q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith only [hq])
  have hBd (n : Fin N) : ∃ w : WaveSpace (Fin N × Fin 3),
      BesselPair (H := PhotonFock) n (3 / q) (inclusion (Fin N × Fin 3) (fun _ => 0) u) w := by
    have hex := joint.value n (3 / q) (3 / q) hs le_rfl hs2 u hu
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  exact CoordinateDivergenceApproximation.from_coordinates S A d q hq a
    (inclusion (Fin N × Fin 3) (fun _ => 0) u) (inclusion (Fin N × Fin 3) (fun _ => 0) v)
    (fun i => roughMultiply (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hau i))
    (fun i => roughMultiply (I := Fin N × Fin 3) (configurationVector A i) (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hav i))
    (roughMultiply (I := Fin N × Fin 3) (configurationDivergence d) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hd)
    (fun i => roughMultiply_ae (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) (hau i))
    (fun i => roughMultiply_ae (configurationVector A i)
      (inclusion (Fin N × Fin 3) (fun _ => 0) v) (hav i))
    (roughMultiply_ae (configurationDivergence d)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) hd) hBu hBv hBd

end PfHk.PhysicalExternalOperator
