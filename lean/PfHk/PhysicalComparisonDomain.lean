import PfHk.PhysicalFreeOperator
import GptLean.WeylRadiationOperator
import GptLean.PhysicalPFFormEvaluation
import PfHk.PhysicalLocalEnergySobolev
import PfHk.ComparisonGraphAlgebra

/-! The explicitly named standard operator-theory inputs are domain
identification, graph-norm equivalence, and supported operator-core
approximation. Their graphs are the actual PF variational graph and the
actual electronic Laplacian/radiation graph. No polar identity, weighted
estimate, or unique-continuation assertion is a background field. -/

noncomputable section
namespace PfHk.PhysicalOperatorDomain

open MeasureTheory Filter GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
  GptLean.PhysicalPFReference GptLean.ElectronicH1Multiplier
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open scoped Topology InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

local instance comparisonPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.referenceSubspace radiationHamiltonian
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.derivative ElectronicH1Complex.value

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem zero_potential_relation (V : Position I → ℝ) (u : Reference I V) :
    ∀ᵐ x ∂volume, (0 : WaveSpace I) x =
      (Real.sqrt (0 : ℝ) : ℂ) • (PhysicalPFReference.freeVector I V u).value x := by
  filter_upwards [Lp.coeFn_zero PhotonFock 2 (volume : Measure (Position I))] with x hx
  simp only [hx, Pi.zero_apply, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

/-- Forget the scalar potential graph while retaining the actual wave,
all weak electronic derivatives and the radiation square root. -/
def toFreeReference (V : Position I → ℝ) (u : Reference I V) : Reference I (fun _ => 0) :=
  PhysicalPFFormEvaluation.referenceOfFree I (fun _ => 0)
    (PhysicalPFReference.freeVector I V u) 0 (zero_potential_relation V u)

theorem toFreeReference_value (V : Position I → ℝ) (u : Reference I V) :
    inclusion I (fun _ => 0) (toFreeReference V u) = inclusion I V u := by
  exact PhysicalPFFormEvaluation.referenceOfFree_value I (fun _ => 0)
    (PhysicalPFReference.freeVector I V u) 0 (zero_potential_relation V u)

theorem toFreeReference_ordinary (V : Position I → ℝ) (u : Reference I V) (i : I) :
    ordinary I (fun _ => 0) i (toFreeReference V u) = ordinary I V i u := by
  exact PhysicalPFFormEvaluation.referenceOfFree_ordinary I (fun _ => 0)
    (PhysicalPFReference.freeVector I V u) 0 (zero_potential_relation V u) i

theorem toFreeReference_radiation (V : Position I → ℝ) (u : Reference I V) :
    radiation I (fun _ => 0) (toFreeReference V u) = radiation I V u := by
  exact PhysicalPFFormEvaluation.referenceOfFree_radiation I (fun _ => 0)
    (PhysicalPFReference.freeVector I V u) 0 (zero_potential_relation V u)

attribute [local irreducible] toFreeReference

/-- The positive electronic Laplacian, without the kinetic coefficient
one half, defined by its usual H1 variational graph. -/
def IsLaplacianPair (V : Position I → ℝ) (u : Reference I V) (l : WaveSpace I) : Prop :=
  ComparisonGraphAlgebra.WeakLaplacian (H := PhotonFock) (fun i => ordinary I V i u) l

/-- The pointwise full radiation Hamiltonian has a global L2 output. -/
def IsRadiationPair (V : Position I → ℝ) (u : Reference I V) (r : WaveSpace I) : Prop :=
  ∀ᵐ x ∂volume, (inclusion I V u x, r x) ∈ radiationHamiltonian.graph

/-- The graph of `L = -Δ + Hrad + 1`, with both domain conditions explicit. -/
def IsComparisonPair (V : Position I → ℝ) (u : Reference I V) (L : WaveSpace I) : Prop :=
  ∃ l r : WaveSpace I, IsLaplacianPair V u l ∧ IsRadiationPair V u r ∧
    L = l + r + inclusion I V u

def ComparisonDomain (V : Position I → ℝ) (u : Reference I V) : Prop :=
  ∃ L : WaveSpace I, IsComparisonPair V u L

theorem comparisonPair_toFree {V : Position I → ℝ} {u : Reference I V} {L : WaveSpace I}
    (h : IsComparisonPair V u L) : IsComparisonPair (fun _ => 0) (toFreeReference V u) L := by
  obtain ⟨l, r, hl, hr, hL⟩ := h
  refine ⟨l, r, ?_, ?_, ?_⟩
  · exact ComparisonGraphAlgebra.WeakLaplacian.congr hl (toFreeReference_ordinary V u)
  · filter_upwards [hr] with x hx
    exact (congrArg (fun z : PhotonFock => (z, r x) ∈ radiationHamiltonian.graph)
      (congrArg (fun z : WaveSpace I => z x) (toFreeReference_value V u))).mpr hx
  · exact hL.trans (congrArg (fun z : WaveSpace I => l + r + z)
      (toFreeReference_value V u).symm)

def OperatorGraph (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
    (κ : I → Position I → WeightedPhotonKernel)
    (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
    (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
    (A : I → Position I → ℝ) (positive negative : Position I → ℝ)
    (u : Reference I V) (f : WaveSpace I) : Prop :=
  ∃ hu : ExternalDomain V A positive negative u,
    IsOperatorPair V C κ hκ M hbound e A positive negative u hu f

/-- Standard domain identification, uniformly for every graph vector. -/
def DomainIdentification (V : Position I → ℝ)
    (G : Reference I V → WaveSpace I → Prop) : Prop :=
  ∀ u, (∃ f, G u f) ↔ ComparisonDomain V u

/-- Standard equivalence of the two operator graph norms. -/
abbrev GraphNormEquivalence (V : Position I → ℝ)
    (G : Reference I V → WaveSpace I → Prop) :=
  ComparisonGraphAlgebra.GraphNormComparison (inclusion I V) G (IsComparisonPair V)

theorem comparison_graph_bound {V : Position I → ℝ}
    {G : Reference I V → WaveSpace I → Prop}
    (hD : DomainIdentification V G) (hG : GraphNormEquivalence V G)
    {u : Reference I V} {f : WaveSpace I} (hf : G u f) :
    ∃ L, IsComparisonPair V u L ∧
      ‖L‖ ^ 2 ≤ (2 * hG.bound ^ 2) * (‖f‖ ^ 2 + ‖inclusion I V u‖ ^ 2) :=
  ComparisonGraphAlgebra.comparison_graph_bound hG hf ((hD u).mp ⟨f, hf⟩)

/-- The uniform squared graph bound used on each dyadic annulus. -/
theorem exists_comparison_graph_constant {V : Position I → ℝ}
    {G : Reference I V → WaveSpace I → Prop}
    (hD : DomainIdentification V G) (hG : GraphNormEquivalence V G) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ u f, G u f → ∃ L, IsComparisonPair V u L ∧
      ‖L‖ ^ 2 ≤ Cg * (‖f‖ ^ 2 + ‖inclusion I V u‖ ^ 2) := by
  exact ⟨2 * hG.bound ^ 2, mul_nonneg (by norm_num) (sq_nonneg _),
    fun _ _ hf => comparison_graph_bound hD hG hf⟩

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

def FreeGraph (u : Reference I (fun _ => 0)) (f : WaveSpace I) : Prop :=
  OperatorGraph (fun _ => 0) C κ hκ M hbound e
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0) u f

/-- Hasler–Herbst domain identification for the given physical form factors. -/
abbrev HaslerHerbstDomain : Prop :=
  DomainIdentification (fun _ => 0) (FreeGraph C κ hκ M hbound e)

/-- The graph-norm part of the standard Hasler–Herbst theorem. -/
abbrev HaslerHerbstGraphNorm :=
  GraphNormEquivalence (fun _ => 0) (FreeGraph C κ hκ M hbound e)

theorem free_graph_of_comparison (hD : HaslerHerbstDomain C κ hκ M hbound e)
    {V : Position I → ℝ} {u : Reference I V} {L : WaveSpace I}
    (hL : IsComparisonPair V u L) :
    ∃ f, FreeGraph C κ hκ M hbound e (toFreeReference V u) f :=
  (hD (toFreeReference V u)).mpr ⟨L, comparisonPair_toFree hL⟩

theorem freeGraph_iff (u : Reference I (fun _ => 0)) (f : WaveSpace I) :
    FreeGraph C κ hκ M hbound e u f ↔
      ∀ v : Reference I (fun _ => 0),
        PhysicalLocalEnergy.form (fun _ => 0) C κ hκ M hbound e v u =
          ⟪inclusion I (fun _ => 0) v, f⟫_ℂ := by
  constructor
  · rintro ⟨hu, h⟩
    exact (isOperatorPair_zero_iff (fun _ => 0) C κ hκ M hbound e u f).mp h
  · intro h
    exact ⟨zeroExternalDomain (fun _ => 0) u,
      (isOperatorPair_zero_iff (fun _ => 0) C κ hκ M hbound e u f).mpr h⟩


end PfHk.PhysicalOperatorDomain
