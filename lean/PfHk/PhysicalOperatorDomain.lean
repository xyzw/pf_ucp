import PfHk.PhysicalComparisonDomain
import PfHk.PhysicalOperatorCoreSource
import PfHk.PositiveFormGraphLimits

/-! Localized operator-domain consequences and supported core transfer for
actual PF graph vectors. The ordinary comparison graph and standard
Hasler–Herbst inputs are defined in PhysicalComparisonDomain. -/

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

local instance operatorDomainPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  PhysicalPFReference.referenceSubspace radiationHamiltonian SmoothCore.reference toFreeReference
  ElectronicH1Complex.complexWeakGraph ElectronicH1Complex.derivative ElectronicH1Complex.value
  FreeGraph OperatorGraph IsComparisonPair IsLaplacianPair IsRadiationPair

variable {I : Type} [Fintype I] [DecidableEq I]

local instance operatorDomainWaveDirectInner : InnerProductSpace ℂ (WaveSpace I) :=
  { (inferInstance : InnerProductSpace ℂ (WaveSpace I)) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (WaveSpace I)) }
variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

variable (V : Position I → ℝ) (A : I → Position I → ℝ)
  (positive negative : Position I → ℝ)

/-- Standard Kato–Rellich identification with the form realization of a
globally truncated perturbation. Relative-boundedness verification belongs
to the ordinary scalar multiplier input for that realization. -/
abbrev KatoRellichDomain : Prop :=
  DomainIdentification V (OperatorGraph V C κ hκ M hbound e A positive negative)

abbrev KatoRellichGraphNorm :=
  GraphNormEquivalence V (OperatorGraph V C κ hκ M hbound e A positive negative)

/-- The actual localized weak eigenstate lies in both ordinary operator
domains once the standard domain theorem for its realization is supplied. -/
theorem localized_eigenstate_comparison_domain
    (hD : KatoRellichDomain C κ hκ M hbound e V A positive negative)
    (a : TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {E : ℝ}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu) :
    ComparisonDomain V (PhysicalPFScalarMultiplier.multiply V a.scalar u) := by
  apply (hD _).mp
  unfold OperatorGraph
  exact ⟨_, hu.localize V a.scalar,
    eigenstate_operatorPair_localize V C κ hκ M hbound e A positive negative a heigen⟩

theorem local_operator_comparison_domain
    (hD : KatoRellichDomain C κ hκ M hbound e V A positive negative)
    (a : TwiceDifferentiableMultiplier I) {s : Set (Position I)}
    (hsupp : ∀ x, x ∉ s → a.scalar.weight x = 0)
    {u : Reference I V} {hu : ExternalDomain V A positive negative u} {f : WaveSpace I}
    (hf : IsLocalOperatorPair V C κ hκ M hbound e A positive negative s u hu f) :
    ComparisonDomain V (PhysicalPFScalarMultiplier.multiply V a.scalar u) := by
  apply (hD _).mp
  unfold OperatorGraph
  exact ⟨_, hu.localize V a.scalar,
    local_operatorPair_localize V C κ hκ M hbound e A positive negative a hsupp hf⟩

/-- The localized physical eigenstate has an actual free PF graph
representative with exactly the same electronic wave function. -/
theorem localized_eigenstate_free_graph
    (hHH : HaslerHerbstDomain C κ hκ M hbound e)
    (hKR : KatoRellichDomain C κ hκ M hbound e V A positive negative)
    (a : TwiceDifferentiableMultiplier I) {u : Reference I V}
    {hu : ExternalDomain V A positive negative u} {E : ℝ}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu) :
    ∃ f, FreeGraph C κ hκ M hbound e
      (toFreeReference V (PhysicalPFScalarMultiplier.multiply V a.scalar u)) f :=
  Exists.elim (localized_eigenstate_comparison_domain C κ hκ M hbound e V A positive negative
    hKR a heigen) (fun _ hL => free_graph_of_comparison C κ hκ M hbound e hHH hL)

/-- Standard operator-core approximation, retaining a prescribed open
neighborhood of the compact electronic support. The core vectors themselves
were constructed in the actual radiation operator graph. -/
structure AnnularCoreApproximation : Prop where
  approximate : ∀ (u : Reference I (fun _ => 0)) (f : WaveSpace I)
    (K s : Set (Position I)), FreeGraph C κ hκ M hbound e u f →
    IsCompact K → IsOpen s → K ⊆ s →
    (∀ᵐ x ∂volume, x ∉ K → inclusion I (fun _ => 0) u x = 0) →
    ∃ a : ℕ → SmoothCore s, ∃ g : ℕ → WaveSpace I,
      (∀ n, FreeGraph C κ hκ M hbound e (a n).reference (g n)) ∧
      (∀ n, Nonempty (CompactSource s (g n))) ∧
      Tendsto (fun n => inclusion I (fun _ => 0) (a n).reference) atTop
        (𝓝 (inclusion I (fun _ => 0) u)) ∧ Tendsto g atTop (𝓝 f)

theorem freeGraph_isPositiveGraph {u : Reference I (fun _ => 0)} {f : WaveSpace I}
    (hf : FreeGraph C κ hκ M hbound e u f) :
    PositiveFormGraphLimits.IsGraph (I := I) (Q := Reference I (fun _ => 0)) (H := WaveSpace I)
      (inclusion I (fun _ => 0))
      (fun i => (covariant I (fun _ => 0) C κ hκ M hbound e i))
      (radiation I (fun _ => 0)) (potential I (fun _ => 0)) u f :=
  (freeGraph_iff C κ hκ M hbound e u f).mp hf

attribute [local irreducible] PositiveFormGraphLimits.IsGraph PositiveFormGraphLimits.form

set_option maxHeartbeats 100000

/-- The actual covariant and radiation coordinates converge whenever the
free PF operator graph coordinates converge. -/
theorem freeGraph_form_convergence {u : ℕ → Reference I (fun _ => 0)}
    {v : Reference I (fun _ => 0)} {f : ℕ → WaveSpace I} {g : WaveSpace I}
    (hu : ∀ n, FreeGraph C κ hκ M hbound e (u n) (f n))
    (hv : FreeGraph C κ hκ M hbound e v g)
    (hψ : Tendsto (fun n => inclusion I (fun _ => 0) (u n)) atTop
      (𝓝 (inclusion I (fun _ => 0) v))) (hf : Tendsto f atTop (𝓝 g)) :
    (∀ i, Tendsto (fun n => covariant I (fun _ => 0) C κ hκ M hbound e i (u n)) atTop
      (𝓝 (covariant I (fun _ => 0) C κ hκ M hbound e i v))) ∧
    Tendsto (fun n => radiation I (fun _ => 0) (u n)) atTop
      (𝓝 (radiation I (fun _ => 0) v)) :=
  PositiveFormGraphLimits.form_convergence (I := I) (Q := Reference I (fun _ => 0)) (H := WaveSpace I)
    (inclusion I (fun _ => 0))
    (fun i => (covariant I (fun _ => 0) C κ hκ M hbound e i))
    (radiation I (fun _ => 0)) (potential I (fun _ => 0))
    (u := u) (v := v) (f := f) (g := g)
    (fun n => freeGraph_isPositiveGraph C κ hκ M hbound e (u := u n) (f := f n) (hu n))
    (freeGraph_isPositiveGraph C κ hκ M hbound e hv) hψ hf

namespace AnnularCoreApproximation

variable (hcore : AnnularCoreApproximation C κ hκ M hbound e)
  {u : Reference I (fun _ => 0)} {f : WaveSpace I} {K s : Set (Position I)}
  (hu : FreeGraph C κ hκ M hbound e u f) (hK : IsCompact K) (hs : IsOpen s)
  (hKs : K ⊆ s) (hsupp : ∀ᵐ x ∂volume, x ∉ K → inclusion I (fun _ => 0) u x = 0)

def approximants : ℕ → SmoothCore s :=
  Classical.choose (hcore.approximate u f K s hu hK hs hKs hsupp)

def sources : ℕ → WaveSpace I :=
  Classical.choose (Classical.choose_spec (hcore.approximate u f K s hu hK hs hKs hsupp))

theorem properties :
    (∀ n, FreeGraph C κ hκ M hbound e
      (hcore.approximants C κ hκ M hbound e hu hK hs hKs hsupp n).reference
      (hcore.sources C κ hκ M hbound e hu hK hs hKs hsupp n)) ∧
    (∀ n, Nonempty (CompactSource s (hcore.sources C κ hκ M hbound e hu hK hs hKs hsupp n))) ∧
    Tendsto (fun n => inclusion I (fun _ => 0)
      (hcore.approximants C κ hκ M hbound e hu hK hs hKs hsupp n).reference) atTop
      (𝓝 (inclusion I (fun _ => 0) u)) ∧
    Tendsto (hcore.sources C κ hκ M hbound e hu hK hs hKs hsupp) atTop (𝓝 f) :=
  Classical.choose_spec (Classical.choose_spec (hcore.approximate u f K s hu hK hs hKs hsupp))

end AnnularCoreApproximation

attribute [local irreducible] AnnularCoreApproximation.approximants AnnularCoreApproximation.sources

end PfHk.PhysicalOperatorDomain
