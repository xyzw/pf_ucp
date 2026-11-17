import PfHk.SphereCoreGeometry
import PfHk.PolarSobolevChartAlgebra
import GptLean.PhysicalPFReference

/-! The ordinary Sobolev chart between a compact Euclidean annulus and a
finite logarithmic cylinder. The named standard input records only the
ordinary H1 change of coordinates and the spectator radiation graph.
It contains no field profile, Weyl transformation or operator equation. -/

noncomputable section
namespace PfHk.OrdinaryPolarSobolevChart

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PolarCalculus PfHk.SphereAngularField PfHk.SphereCoreGeometry

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.ordinary
  PhysicalPFReference.radiationSource PhysicalPFReference.referenceSubspace
  radiationGraphInclusion radiationGraphDerivative LpRepresents

variable (N : ℕ)

abbrev Slab := ℝ × Sphere N

def slabMeasure (a b : ℝ) : Measure (Slab N) :=
  ((volume : Measure ℝ).restrict (Set.Icc a b)).prod (sphereMeasure (Fin N × Fin 3))

abbrev PhotonSlab (a b : ℝ) := Lp PhotonFock 2 (slabMeasure N a b)
abbrev RadiationSlab (a b : ℝ) := Lp RadiationGraphSpace 2 (slabMeasure N a b)

def chartPoint (p : Slab N) : PhysicalPFReference.Position (Fin N × Fin 3) :=
  Real.exp (-p.1) • (p.2 : PhysicalPFReference.Position (Fin N × Fin 3))

def radialOrdinary (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  ∑ j, (p.2.val j) • ordinary (Fin N × Fin 3) (fun _ => 0) j u (chartPoint N p)

def valueFunction (c : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  Real.exp (-c * p.1) • inclusion (Fin N × Fin 3) (fun _ => 0) u (chartPoint N p)

def timeFunction (c : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  Real.exp (-c * p.1) •
    ((-c) • inclusion (Fin N × Fin 3) (fun _ => 0) u (chartPoint N p) -
      Real.exp (-p.1) • radialOrdinary N u p)

def gradientFunction (c : ℝ) (j : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (p : Slab N) : PhotonFock :=
  (Real.exp (-c * p.1) * Real.exp (-p.1)) •
    (ordinary (Fin N × Fin 3) (fun _ => 0) j u (chartPoint N p) -
      (p.2.val j) • radialOrdinary N u p)

def radiationFunction (c : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (p : Slab N) : RadiationGraphSpace :=
  Real.exp (-c * p.1) • radiationSource (Fin N × Fin 3) (fun _ => 0) u (chartPoint N p)

def annulus (a b : ℝ) : Set (PhysicalPFReference.Position (Fin N × Fin 3)) :=
  {x | Real.exp (-b) < ‖x‖ ∧ ‖x‖ < Real.exp (-a)}

attribute [local irreducible] valueFunction timeFunction gradientFunction radiationFunction
  radialOrdinary chartPoint slabMeasure

def testCondition (a b : ℝ) (v : CoreVector N × (ℝ → ℝ)) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) v.2 ∧ HasCompactSupport v.2 ∧ tsupport v.2 ⊆ Set.Ioo a b

def compactlySupported (a b : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : Prop :=
  ∃ K, IsCompact K ∧ K ⊆ annulus N a b ∧
    ∀ᵐ x ∂volume, x ∉ K → inclusion (Fin N × Fin 3) (fun _ => 0) u x = 0

def testValue (v : CoreVector N × (ℝ → ℝ)) (p : Slab N) : PhotonFock :=
  v.2 p.1 • v.1.ambient p.2

def testTime (v : CoreVector N × (ℝ → ℝ)) (p : Slab N) : PhotonFock :=
  deriv v.2 p.1 • v.1.ambient p.2

def testGradient (j : Fin N × Fin 3) (v : CoreVector N × (ℝ → ℝ)) (p : Slab N) : PhotonFock :=
  v.2 p.1 • v.1.gradient j p.2

def testRadiation (v : CoreVector N × (ℝ → ℝ)) (p : Slab N) : RadiationGraphSpace :=
  v.2 p.1 • v.1.radiation p.2

/-- The standard ordinary H1/radiation chart on one finite slab. Its
bounded maps give the graph-continuity needed for core approximation. -/
abbrev SobolevChart (c a b : ℝ) :=
  ChartData (slabMeasure N a b) (valueFunction N c) (timeFunction N c)
    (gradientFunction N c) (radiationFunction N c)
    (testCondition N a b) (compactlySupported N a b)
    (testValue N) (testTime N) (testGradient N) (testRadiation N)

/-- Universal ordinary polar Sobolev coordinates, separate from every
physical coefficient and every weak operator equation. -/
abbrev StandardPolarSobolevCharts :=
  ChartFamily (SobolevChart N) (fun a b =>
    Measure.QuasiMeasurePreserving (chartPoint N) (slabMeasure N a b)
      (volume : Measure (PhysicalPFReference.Position (Fin N × Fin 3))))

variable {N}

def StandardPolarSobolevCharts.chart (P : StandardPolarSobolevCharts N) (c a b : ℝ) :
    SobolevChart N c a b := ChartFamily.chart P c a b

theorem StandardPolarSobolevCharts.quasiMeasurePreserving
    (P : StandardPolarSobolevCharts N) (a b : ℝ) :
    Measure.QuasiMeasurePreserving (chartPoint N) (slabMeasure N a b)
      (volume : Measure (PhysicalPFReference.Position (Fin N × Fin 3))) :=
  ChartFamily.quasiMeasurePreserving P a b

theorem SobolevChart.lift_core {c a b : ℝ} (P : SobolevChart N c a b)
    (v : CoreVector N) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcompact : HasCompactSupport η) (hsupport : tsupport η ⊆ Set.Ioo a b) :
    ∃ u : Reference (Fin N × Fin 3) (fun _ => 0), compactlySupported N a b u ∧
      LpRepresents (slabMeasure N a b) (P.value u) (fun p => η p.1 • v.ambient p.2) ∧
      LpRepresents (slabMeasure N a b) (P.time u) (fun p => deriv η p.1 • v.ambient p.2) ∧
      (∀ j : Fin N × Fin 3, LpRepresents (slabMeasure N a b) (P.gradient j u)
        (fun p => η p.1 • v.gradient j p.2)) ∧
      LpRepresents (slabMeasure N a b) (P.radiation u) (fun p => η p.1 • v.radiation p.2) :=
  P.lift (v, η) ⟨hη, hcompact, hsupport⟩

theorem SobolevChart.value_memLp {c a b : ℝ} (P : SobolevChart N c a b)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    MemLp (valueFunction N c u) 2 (slabMeasure N a b) :=
  (P.value_ae u).memLp

theorem SobolevChart.time_memLp {c a b : ℝ} (P : SobolevChart N c a b)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    MemLp (timeFunction N c u) 2 (slabMeasure N a b) :=
  (P.time_ae u).memLp

theorem SobolevChart.gradient_memLp {c a b : ℝ} (P : SobolevChart N c a b)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (j : Fin N × Fin 3) :
    MemLp (gradientFunction N c j u) 2 (slabMeasure N a b) :=
  (P.gradient_ae j u).memLp

theorem SobolevChart.radiation_memLp {c a b : ℝ} (P : SobolevChart N c a b)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    MemLp (radiationFunction N c u) 2 (slabMeasure N a b) :=
  (P.radiation_ae u).memLp

end PfHk.OrdinaryPolarSobolevChart
