import GptLean.RemovalLatticePF
import GptLean.Gaussian.ProductGraphSlicing

/-! The original WIS reference data are obtained from closed operators on
standard cores. Universal fibre graph descriptions and the ordinary
Fubini identification then give the actual product-L2 representatives.
No all-domain WIS intertwining is an input. -/

noncomputable section

set_option maxHeartbeats 1200000

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal

variable {Q H H' K K' : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

/-- Ordinary operator-core background, independent of any source family. -/
structure SpatialGraphCore (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (V : H' ≃ₗᵢ[ℂ] Lp K' 2 μ) where
  operator : H →ₗ.[ℂ] H'
  fibre : Q → K →ₗ.[ℂ] K'
  closed : operator.IsClosed
  fibre_closed : ∀ᵐ q ∂μ, (fibre q).IsClosed
  core : Submodule ℂ H
  hasCore : operator.HasCore core
  core_graph : ∀ v : core, ∀ᵐ q ∂μ,
    (U (v : H) q, V (operator ⟨v, hasCore.le_domain v.property⟩) q) ∈ (fibre q).graph

theorem SpatialGraphCore.graph
    {U : H ≃ₗᵢ[ℂ] Lp K 2 μ} {V : H' ≃ₗᵢ[ℂ] Lp K' 2 μ}
    (C : SpatialGraphCore U V) {u : H} {v : H'} (h : (u,v) ∈ C.operator.graph) :
    ∀ᵐ q ∂μ, (U u q, V v q) ∈ (C.fibre q).graph := by
  obtain ⟨w, hw, hdw⟩ := C.operator.mem_graph_iff.mp h
  have hg := unitary_closed_graph_between_of_hasCore U V C.operator C.closed C.fibre
    C.fibre_closed C.core C.hasCore C.core_graph w
  simpa only [hw, hdw, unitaryFiber] using hg

/-- The covariant core graph is itself derived from the separate hard
and soft WIS core intertwinings. Its all-domain extension is then supplied
by `SpatialGraphCore.graph`. -/
def SpatialGraphCore.ofCovariantPrimitive
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (A F D : H →ₗ.[ℂ] H) (e : ℂ)
    (hD : D.IsClosed) (S : Submodule ℂ H) (hS : D.HasCore S)
    (hcommon : S ≤ (A - e • F).domain)
    (hsource : ∀ v : S, D ⟨v, hS.le_domain v.property⟩ =
      (A - e • F) ⟨v, hcommon v.property⟩)
    (Aq Fq : Q → K →ₗ.[ℂ] K)
    (hclosed : ∀ᵐ q ∂μ, (Aq q - e • Fq q).IsClosable)
    (hA : ∀ v : S, ∀ᵐ q ∂μ,
      (U (v : H) q, U (A ⟨v, (hcommon v.property).1⟩) q) ∈ (Aq q).graph)
    (hF : ∀ v : S, ∀ᵐ q ∂μ,
      (U (v : H) q, U (F ⟨v, (hcommon v.property).2⟩) q) ∈ (Fq q).graph) :
    SpatialGraphCore U U where
  operator := D
  fibre := fun q => (Aq q - e • Fq q).closure
  closed := hD
  fibre_closed := hclosed.mono fun _ h => h.closure_isClosed
  core := S
  hasCore := hS
  core_graph := by
    intro v
    have hg := unitary_covariant_core_graph U A F Aq Fq e
      ⟨v, hcommon v.property⟩ (hA v) (hF v)
    filter_upwards [hg] with q hq
    have hq' := LinearPMap.le_graph_of_le (Aq q - e • Fq q).le_closure hq
    simpa only [hsource v, unitaryFiber] using hq'

end GptLean.Gaussian

namespace GptLean.RemovalSource

open MeasureTheory MeasureTheory.Measure Filter GptLean.Repair GptLean.SymmetricLift
  GptLean.RemovalEnergy GptLean.Gaussian

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] {N : ℕ}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [MeasurableSpace Kr] [BorelSpace Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

abbrev SpatialL2 (N : ℕ) (H : Type*) [NormedAddCommGroup H] :=
  Lp H 2 (volume : Measure (Configuration N))

/-- Universal canonical graph descriptions of the electronic derivative,
radiation, hard field, rest form and covariant derivative. These apply to
all vectors in the fibre operator graphs, not to the removal outputs. -/
structure PFCoreDescription
    (Uc : SpatialL2 N H ≃ₗᵢ[ℂ] Lp (SpatialL2 N K) 2 μ)
    (Vc : SpatialL2 N Hr ≃ₗᵢ[ℂ] Lp (SpatialL2 N Kr) 2 μ)
    (R : K →ₗ.[ℂ] K) (A : (Fin N × Fin 3) → Configuration N → K →ₗ.[ℂ] K)
    (B : Configuration N → K →ₗ.[ℂ] Kr) (e : ℝ)
    (soft : (Fin N × Fin 3) → Q × Configuration N → ℝ) where
  derivative : (Fin N × Fin 3) → SpatialGraphCore Uc Uc
  radiation : SpatialGraphCore Uc Uc
  hard : (Fin N × Fin 3) → SpatialGraphCore Uc Uc
  rest : SpatialGraphCore Uc Vc
  covariant : (Fin N × Fin 3) → SpatialGraphCore Uc Uc
  weak : ∀ q (f : SpatialL2 N K) (d : (Fin N × Fin 3) → SpatialL2 N K),
    (∀ j, (f,d j) ∈ ((derivative j).fibre q).graph) →
      HasWeakH1Local (fun x => f x) (fun j x => d j x)
  radiation_graph : ∀ q (f r : SpatialL2 N K), (f,r) ∈ (radiation.fibre q).graph →
    ∀ᵐ x ∂volume, (f x,r x) ∈ R.graph
  hard_graph : ∀ q j (f a : SpatialL2 N K), (f,a) ∈ ((hard j).fibre q).graph →
    ∀ᵐ x ∂volume, (f x,a x) ∈ (A j x).graph
  rest_graph : ∀ q (f : SpatialL2 N K) (r : SpatialL2 N Kr),
    (f,r) ∈ (rest.fibre q).graph → ∀ᵐ x ∂volume, (f x,r x) ∈ (B x).graph
  covariant_eval : ∀ᵐ q ∂μ, ∀ j (f d a u : SpatialL2 N K),
    (f,d) ∈ ((derivative j).fibre q).graph →
    (f,a) ∈ ((hard j).fibre q).graph → (f,u) ∈ ((covariant j).fibre q).graph →
    ∀ᵐ x ∂volume, u x = -Complex.I • d x - (e : ℂ) • a x -
      ((e * soft j (q,x) : ℝ) : ℂ) • f x
  radiation_measurable : MeasurableSet (R.graph : Set (K × K))
  hard_measurable : ∀ j, MeasurableSet
    {p : Configuration N × K × K | (p.2.1,p.2.2) ∈ (A j p.1).graph}
  rest_measurable : MeasurableSet
    {p : Configuration N × K × Kr | (p.2.1,p.2.2) ∈ (B p.1).graph}
  soft_measurable : ∀ j, StronglyMeasurable (soft j)

namespace LatticeSourceData

/-- The original PFData are a conclusion of core slicing. Inputs on the
original spectral vectors are membership in the original operator graphs.
The only representation bridge is the universal Fubini L2 identification. -/
def originalPFData_of_cores (D : LatticeSourceData N μ H K Hr Kr Hs)
    (Uc : SpatialL2 N H ≃ₗᵢ[ℂ] Lp (SpatialL2 N K) 2 μ)
    (Vc : SpatialL2 N Hr ≃ₗᵢ[ℂ] Lp (SpatialL2 N Kr) 2 μ)
    (hU : ∀ v, ∀ᵐ q ∂μ, (fun x => Uc v q x) =ᵐ[volume] (fun x => D.U v (q,x)))
    (hV : ∀ v, ∀ᵐ q ∂μ, (fun x => Vc v q x) =ᵐ[volume] (fun x => D.Ur v (q,x)))
    (R : K →ₗ.[ℂ] K) (A : (Fin N × Fin 3) → Configuration N → K →ₗ.[ℂ] K)
    (B : Configuration N → K →ₗ.[ℂ] Kr) (e : ℝ)
    (soft : (Fin N × Fin 3) → Q × Configuration N → ℝ)
    (C : PFCoreDescription Uc Vc R A B e soft)
    (derivative : ℕ → (Fin N × Fin 3) → SpatialL2 N H)
    (radiation : ℕ → SpatialL2 N H)
    (hard : ℕ → (Fin N × Fin 3) → SpatialL2 N H)
    (hderivative : ∀ n j, (D.ψ n,derivative n j) ∈ (C.derivative j).operator.graph)
    (hradiation : ∀ n, (D.ψ n,radiation n) ∈ C.radiation.operator.graph)
    (hhard : ∀ n j, (D.ψ n,hard n j) ∈ (C.hard j).operator.graph)
    (hrest : ∀ n, (D.ψ n,D.rest n) ∈ C.rest.operator.graph)
    (hcovariant : ∀ n j, (D.ψ n,D.dψ n j) ∈ (C.covariant j).operator.graph) :
    D.original.PFData R A B e (fun _ => soft) := by
  have hsection (n : ℕ) : ∀ᵐ q ∂μ,
      HasWeakH1Local (fun x => D.U (D.ψ n) (q,x))
        (fun j x => D.U (derivative n j) (q,x)) ∧
      (∀ᵐ x ∂volume, (D.U (D.ψ n) (q,x),D.U (radiation n) (q,x)) ∈ R.graph) ∧
      (∀ j, ∀ᵐ x ∂volume, (D.U (D.ψ n) (q,x),D.U (hard n j) (q,x)) ∈ (A j x).graph) ∧
      (∀ᵐ x ∂volume, (D.U (D.ψ n) (q,x),D.Ur (D.rest n) (q,x)) ∈ (B x).graph) ∧
      (∀ j, ∀ᵐ x ∂volume, D.U (D.dψ n j) (q,x) =
        -Complex.I • D.U (derivative n j) (q,x) - (e : ℂ) • D.U (hard n j) (q,x) -
        ((e * soft j (q,x) : ℝ) : ℂ) • D.U (D.ψ n) (q,x)) := by
    filter_upwards [ae_all_iff.mpr (fun j => (C.derivative j).graph (hderivative n j)),
      C.radiation.graph (hradiation n), ae_all_iff.mpr (fun j => (C.hard j).graph (hhard n j)),
      C.rest.graph (hrest n), ae_all_iff.mpr (fun j => (C.covariant j).graph (hcovariant n j)),
      hU (D.ψ n), ae_all_iff.mpr (fun j => hU (derivative n j)), hU (radiation n),
      ae_all_iff.mpr (fun j => hU (hard n j)), hV (D.rest n),
      ae_all_iff.mpr (fun j => hU (D.dψ n j)), C.covariant_eval]
      with q hd hr ha hb hc hf hdp hrp hap hbp hcp hce
    refine ⟨(C.weak q _ _ hd).congr hf hdp, ?_, ?_, ?_, ?_⟩
    · filter_upwards [C.radiation_graph q _ _ hr, hf, hrp] with x hx hfx hrx
      rwa [← hfx, ← hrx]
    · intro j
      filter_upwards [C.hard_graph q j _ _ (ha j), hf, hap j] with x hx hfx hax
      rwa [← hfx, ← hax]
    · filter_upwards [C.rest_graph q _ _ hb, hf, hbp] with x hx hfx hbx
      rwa [← hfx, ← hbx]
    · intro j
      filter_upwards [hce j _ _ _ _ (hd j) (ha j) (hc j),
        hf, hdp j, hap j, hcp j] with x hx hfx hdx hax hcx
      rwa [← hfx, ← hdx, ← hax, ← hcx]
  refine {
    derivative := fun n j => D.U (derivative n j)
    radiation := fun n => D.U (radiation n)
    hardField := fun n j => D.U (hard n j)
    weak := fun n => (hsection n).mono fun _ h => h.1
    radiation_graph := ?_
    hard_graph := ?_
    rest_graph := ?_
    covariant_eq := ?_
  }
  · intro n
    apply (ae_prod_iff_ae_ae (C.radiation_measurable.preimage
      ((Lp.stronglyMeasurable (D.U (D.ψ n))).measurable.prodMk
        (Lp.stronglyMeasurable (D.U (radiation n))).measurable))).mpr
    exact (hsection n).mono fun _ h => h.2.1
  · intro n j
    apply (ae_prod_iff_ae_ae ((C.hard_measurable j).preimage
      (measurable_snd.prodMk ((Lp.stronglyMeasurable (D.U (D.ψ n))).measurable.prodMk
        (Lp.stronglyMeasurable (D.U (hard n j))).measurable)))).mpr
    exact (hsection n).mono fun _ h => h.2.2.1 j
  · intro n
    apply (ae_prod_iff_ae_ae (C.rest_measurable.preimage
      (measurable_snd.prodMk ((Lp.stronglyMeasurable (D.U (D.ψ n))).measurable.prodMk
        (Lp.stronglyMeasurable (D.Ur (D.rest n))).measurable)))).mpr
    exact (hsection n).mono fun _ h => h.2.2.2.1
  · intro n j
    have hm : Measurable (fun p : Q × Configuration N =>
        -Complex.I • D.U (derivative n j) p - (e : ℂ) • D.U (hard n j) p -
          ((e * soft j p : ℝ) : ℂ) • D.U (D.ψ n) p) := by
      exact (((Lp.stronglyMeasurable (D.U (derivative n j))).const_smul (-Complex.I)).sub
        ((Lp.stronglyMeasurable (D.U (hard n j))).const_smul (e : ℂ))).sub
          ((Complex.continuous_ofReal.comp_stronglyMeasurable
            ((C.soft_measurable j).const_mul e)).smul (Lp.stronglyMeasurable (D.U (D.ψ n)))) |>.measurable
    apply (ae_prod_iff_ae_ae (measurableSet_eq_fun
      (Lp.stronglyMeasurable (D.U (D.dψ n j))).measurable hm)).mpr
    exact (hsection n).mono fun _ h => h.2.2.2.2 j

end LatticeSourceData
end GptLean.RemovalSource
