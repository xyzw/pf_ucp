import GptLean.RemovalOriginalPF

/-! Primitive original operator graphs packaged for exact removal. The
conditional PF source is derived by closed-core slicing and Fubini. -/

noncomputable section

namespace GptLean.RemovalSource

open MeasureTheory SymmetricLift RemovalEnergy

variable {Q Ho H Hr F : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] {N : ℕ}
  [NormedAddCommGroup Ho] [InnerProductSpace ℂ Ho]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [MeasurableSpace F] [BorelSpace F]

structure LatticePFCoreData (src : LatticeSourceData N μ Ho H Hr F Ho)
    (rad : H →ₗ.[ℂ] H) (hard : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H)
    (rest : Configuration N → H →ₗ.[ℂ] F) (e : ℝ)
    (soft : (Fin N × Fin 3) → Q × Configuration N → ℝ) where
  curried : SpatialL2 N Ho ≃ₗᵢ[ℂ] Lp (SpatialL2 N H) 2 μ
  curriedRest : SpatialL2 N Hr ≃ₗᵢ[ℂ] Lp (SpatialL2 N F) 2 μ
  representative : ∀ v, ∀ᵐ q ∂μ, (fun x => curried v q x) =ᵐ[volume]
    (fun x => src.U v (q, x))
  representativeRest : ∀ v, ∀ᵐ q ∂μ, (fun x => curriedRest v q x) =ᵐ[volume]
    (fun x => src.Ur v (q, x))
  core : PFCoreDescription curried curriedRest rad hard rest e soft
  derivative : ℕ → (Fin N × Fin 3) → SpatialL2 N Ho
  radiation : ℕ → SpatialL2 N Ho
  hardField : ℕ → (Fin N × Fin 3) → SpatialL2 N Ho
  derivative_graph : ∀ n j, (src.ψ n, derivative n j) ∈ (core.derivative j).operator.graph
  radiation_graph : ∀ n, (src.ψ n, radiation n) ∈ core.radiation.operator.graph
  hard_graph : ∀ n j, (src.ψ n, hardField n j) ∈ (core.hard j).operator.graph
  rest_graph : ∀ n, (src.ψ n, src.rest n) ∈ core.rest.operator.graph
  covariant_graph : ∀ n j, (src.ψ n, src.dψ n j) ∈ (core.covariant j).operator.graph

def LatticePFCoreData.toPFData
    {src : LatticeSourceData N μ Ho H Hr F Ho}
    {rad : H →ₗ.[ℂ] H} {hard : (Fin N × Fin 3) → Configuration N → H →ₗ.[ℂ] H}
    {rest : Configuration N → H →ₗ.[ℂ] F} {e : ℝ}
    {soft : (Fin N × Fin 3) → Q × Configuration N → ℝ}
    (p : LatticePFCoreData src rad hard rest e soft) :
    src.original.PFData rad hard rest e (fun _ => soft) :=
  src.originalPFData_of_cores p.curried p.curriedRest p.representative p.representativeRest
    rad hard rest e soft p.core p.derivative p.radiation p.hardField p.derivative_graph
    p.radiation_graph p.hard_graph p.rest_graph p.covariant_graph

end GptLean.RemovalSource
