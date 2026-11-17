import GptLean.PhysicalCoulombReferenceCore

/-! Radiation-finite Coulomb reference vectors are dense in the full electronic H1 domain. -/

noncomputable section

namespace GptLean.PhysicalCoulombReferenceCore

open PhysicalFock Filter Topology ElectronicH1Complex

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

variable (N : ℕ) (c : ℝ) (hc : 0 ≤ c)

def h1Approximation (v : ComplexH1 PhotonFock (Index N)) (k : ℕ) : Reference N c :=
  attach N c hc (PhysicalFreeReferenceCore.fromGraphH1 (Index N)
    (ElectronicH1Map.map (radiationEnergyCutoff k) v))

theorem electronic_h1Approximation (v : ComplexH1 PhotonFock (Index N)) (k : ℕ) :
    PhysicalPFReference.electronic (Index N) (fun x => c * PhysicalCoulombH1.potential N x)
      (h1Approximation N c hc v k) = ElectronicH1Map.map (energyCutoff k) v := by
  have h : radiationGraphInclusion.comp (radiationEnergyCutoff k) = energyCutoff k := by
    ext u
    rfl
  exact (ElectronicH1Map.map_comp (I := Index N) (E := PhotonFock)
    (F := RadiationGraphSpace) (G := PhotonFock)
    radiationGraphInclusion (radiationEnergyCutoff k) v).trans
      (congrArg (fun L : PhotonFock →L[ℂ] PhotonFock => ElectronicH1Map.map L v) h)

theorem h1Approximation_tendsto (v : ComplexH1 PhotonFock (Index N)) :
    Tendsto (fun k => PhysicalPFReference.electronic (Index N)
      (fun x => c * PhysicalCoulombH1.potential N x) (h1Approximation N c hc v k))
      atTop (𝓝 v) := by
  simpa only [electronic_h1Approximation] using
    ElectronicH1Map.map_tendsto energyCutoff energyCutoff_norm_le energyCutoff_tendsto v

include hc in
theorem electronic_denseRange : DenseRange (PhysicalPFReference.electronic (Index N)
    (fun x => c * PhysicalCoulombH1.potential N x)) := by
  intro v
  apply mem_closure_of_tendsto (h1Approximation_tendsto N c hc v)
  exact Eventually.of_forall fun k => ⟨h1Approximation N c hc v k, rfl⟩

end GptLean.PhysicalCoulombReferenceCore
