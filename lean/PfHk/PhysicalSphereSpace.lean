import PfHk.PolarCalculus
import GptLean.PhysicalFockSpatialField

/-! The physical photon and radiation-graph L2 spaces on the actual
configuration-space unit sphere and its surface measure. -/

noncomputable section
namespace PfHk.SphereAngularField

open GptLean.PhysicalFock PfHk.PolarCalculus

abbrev Sphere (N : ℕ) := UnitSphere (Fin N × Fin 3)
abbrev SphereRadiation (N : ℕ) := SpatialRadiationGraph (sphereMeasure (Fin N × Fin 3))
abbrev SpherePhoton (N : ℕ) := SphereHilbert (Fin N × Fin 3) PhotonFock

end PfHk.SphereAngularField
