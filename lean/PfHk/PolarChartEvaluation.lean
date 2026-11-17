import PfHk.OrdinaryPolarSobolevChart

/-! Plain evaluation functions for the ordinary bounded chart maps.
These fix the actual reference and L2 instances before a physical core
vector is substituted. -/

noncomputable section
namespace PfHk.OrdinaryPolarSobolevChart
open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 20000

variable {N : ℕ} {c l r : ℝ} (P : SobolevChart N c l r)

def valueAt (u : Reference (Fin N × Fin 3) (fun _ => 0)) : PhotonSlab N l r := P.value u
def timeAt (u : Reference (Fin N × Fin 3) (fun _ => 0)) : PhotonSlab N l r := P.time u
def gradientAt (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : PhotonSlab N l r := P.gradient j u
def radiationAt (u : Reference (Fin N × Fin 3) (fun _ => 0)) : RadiationSlab N l r := P.radiation u

theorem valueAt_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N l r) (valueAt P u) (valueFunction N c u) := P.value_ae u
theorem timeAt_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N l r) (timeAt P u) (timeFunction N c u) := P.time_ae u
theorem gradientAt_ae (j : Fin N × Fin 3) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N l r) (gradientAt P j u) (gradientFunction N c j u) := P.gradient_ae j u
theorem radiationAt_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    LpRepresents (slabMeasure N l r) (radiationAt P u) (radiationFunction N c u) := P.radiation_ae u

end PfHk.OrdinaryPolarSobolevChart
