import PfHk.PhysicalExternalOperator
import PfHk.KatoRellichBackground

/-! Identification of the actual external weak graph by the ordinary
Kato--Rellich theorem. The only physical inputs are the proved multiplier
membership, smooth scalar approximation, and a relative norm bound.
No conclusion about the external operator domain is an assumption. -/

noncomputable section
namespace PfHk.PhysicalExternalOperator

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open PfHk.PhysicalLocalEnergy PfHk.PhysicalCutoffCommutator
open PfHk.KatoRellichBackground PfHk.SymmetricGraphExtension
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000
set_option Elab.async false

local instance externalDomainPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  PfHk.PhysicalOperatorDomain.comparisonPhotonDirectInner

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential roughMultiply perturbation HasMultiplier
  PhysicalPFReference.referenceSubspace

variable {I : Type} [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative divA : Position I → ℝ)

def FreePair (u : Reference I V) (f : WaveSpace I) : Prop :=
  ∀ v, PhysicalLocalEnergy.form V C κ hκ M hbound e v u = ⟪inclusion I V v, f⟫_ℂ

def freeHilbertGraph (x f : WaveSpace I) : Prop :=
  ∃ u : Reference I V, inclusion I V u = x ∧ FreePair V C κ hκ M hbound e u f

def externalHilbertGraph (x f : WaveSpace I) : Prop :=
  ∃ (u : Reference I V) (hu : ExternalDomain V A positive negative u),
    inclusion I V u = x ∧ IsOperatorPair V C κ hκ M hbound e A positive negative u hu f

theorem externalForm_conj (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) :
    starRingEnd ℂ (externalForm V C κ hκ M hbound e A positive negative u v hu hv) =
      externalForm V C κ hκ M hbound e A positive negative v u hv hu := by
  simp only [externalForm, map_sub, map_add, map_mul, map_sum, inner_conj_symm,
    map_div₀, map_one, map_ofNat]

theorem externalHilbertGraph_symmetric :
    SymmetricGraphExtension.Symmetric (externalHilbertGraph V C κ hκ M hbound e A positive negative) := by
  rintro x f y g ⟨u, hu, hux, huf⟩ ⟨v, hv, hvy, hvg⟩
  subst x
  subst y
  calc
    _ = externalForm V C κ hκ M hbound e A positive negative u v hu hv := (hvg u hu).symm
    _ = starRingEnd ℂ (externalForm V C κ hκ M hbound e A positive negative v u hv hu) :=
      (externalForm_conj V C κ hκ M hbound e A positive negative v u hv hu).symm
    _ = starRingEnd ℂ ⟪inclusion I V v, f⟫_ℂ := congrArg (starRingEnd ℂ) (huf v hv)
    _ = _ := inner_conj_symm _ _

variable
  (hmul : ∀ (u : Reference I V) (f : WaveSpace I), FreePair V C κ hκ M hbound e u f →
    OperatorMultipliers V C κ hκ M hbound e A positive negative divA u)

/-- The algebraic sum graph, whose domain is by construction the free
operator domain. Its equality to the external weak graph is proved below. -/
def sumHilbertGraph (x y : WaveSpace I) : Prop :=
  ∃ (u : Reference I V) (f : WaveSpace I) (hf : FreePair V C κ hκ M hbound e u f),
    inclusion I V u = x ∧
      y = f + perturbation V C κ hκ M hbound e A positive negative divA u (hmul u f hf)

theorem sumHilbertGraph_domain (x : WaveSpace I) :
    (∃ f, freeHilbertGraph V C κ hκ M hbound e x f) ↔
      ∃ f, sumHilbertGraph V C κ hκ M hbound e A positive negative divA hmul x f := by
  constructor
  · rintro ⟨f, u, hux, hf⟩
    exact ⟨_, u, f, hf, hux, rfl⟩
  · rintro ⟨y, u, f, hf, hux, hy⟩
    exact ⟨f, u, hux, hf⟩

variable
  (happrox : ∀ (u : Reference I V) (f : WaveSpace I)
    (hf : FreePair V C κ hκ M hbound e u f)
    (v : Reference I V) (hv : ExternalDomain V A positive negative v),
    DivergenceApproximation V A divA u v
      (fun i => roughMultiply (A i) (inclusion I V u) ((hmul u f hf).domain.vector i))
      (fun i => roughMultiply (A i) (inclusion I V v) (hv.vector i))
      (roughMultiply divA (inclusion I V u) (hmul u f hf).divergence))

include happrox

theorem sumHilbertGraph_external (x y : WaveSpace I)
    (h : sumHilbertGraph V C κ hκ M hbound e A positive negative divA hmul x y) :
    externalHilbertGraph V C κ hκ M hbound e A positive negative x y := by
  rcases h with ⟨u, f, hf, hux, hy⟩
  refine ⟨u, (hmul u f hf).domain, hux, ?_⟩
  rw [hy]
  exact operatorPair_add_perturbation V C κ hκ M hbound e A positive negative divA u f
    (hmul u f hf) hf (happrox u f hf)

omit happrox in
theorem freeHilbertGraph_intro (u : Reference I V) (f x : WaveSpace I)
    (hx : inclusion I V u = x) (hf : FreePair V C κ hκ M hbound e u f) :
    freeHilbertGraph V C κ hκ M hbound e x f := ⟨u, hx, hf⟩

omit happrox in
theorem freePair_value (u : Reference I V) (f : WaveSpace I)
    (hf : FreePair V C κ hκ M hbound e u f) (v : Reference I V) :
    PhysicalLocalEnergy.form V C κ hκ M hbound e v u = ⟪inclusion I V v, f⟫_ℂ := hf v

omit happrox in
theorem externalHilbertGraph_intro (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (f x : WaveSpace I)
    (hx : inclusion I V u = x)
    (hf : IsOperatorPair V C κ hκ M hbound e A positive negative u hu f) :
    externalHilbertGraph V C κ hκ M hbound e A positive negative x f := ⟨u, hu, hx, hf⟩

attribute [local irreducible] FreePair freeHilbertGraph externalHilbertGraph sumHilbertGraph

set_option maxHeartbeats 60000 in
theorem external_graph_eq_sum (B : StandardKatoRellich)
    (hSA : SelfAdjointGraph (freeHilbertGraph V C κ hκ M hbound e))
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ (u : Reference I V) (f : WaveSpace I) (hf : FreePair V C κ hκ M hbound e u f),
      ‖perturbation V C κ hκ M hbound e A positive negative divA u (hmul u f hf)‖ ≤
        a * ‖f‖ + b * ‖inclusion I V u‖) :
    ∀ x y : WaveSpace I, externalHilbertGraph V C κ hκ M hbound e A positive negative x y ↔
      sumHilbertGraph V C κ hκ M hbound e A positive negative divA hmul x y := by
  apply weak_graph_eq (H := WaveSpace I) B (freeHilbertGraph V C κ hκ M hbound e)
    (sumHilbertGraph V C κ hκ M hbound e A positive negative divA hmul)
    (externalHilbertGraph V C κ hκ M hbound e A positive negative) hSA
    (externalHilbertGraph_symmetric V C κ hκ M hbound e A positive negative)
    (sumHilbertGraph_external V C κ hκ M hbound e A positive negative divA hmul happrox)
    (sumHilbertGraph_domain V C κ hκ M hbound e A positive negative divA hmul)
    a b ha ha1 hb
  intro x v w hg hp
  unfold freeHilbertGraph at hg
  unfold sumHilbertGraph at hp
  rcases hg with ⟨u, hux, hu⟩
  rcases hp with ⟨u', f, hf, hu'x, hw⟩
  have huu' : u' = u := inclusion_injective I V (hu'x.trans hux.symm)
  subst u'
  have hfv : f = v := hSA.single_valued
    (freeHilbertGraph_intro V C κ hκ M hbound e u f x hux hf)
    (freeHilbertGraph_intro V C κ hκ M hbound e u v x hux hu)
  subst f
  have hsub : w - v = perturbation V C κ hκ M hbound e A positive negative divA u (hmul u v hf) :=
    (congrArg (fun z : WaveSpace I => z - v) hw).trans (add_sub_cancel_left _ _)
  exact (congrArg norm hsub).trans_le ((hrel u v hf).trans_eq
    (congrArg (fun r : ℝ => a * ‖v‖ + b * r) (congrArg norm hux)))

theorem external_domain_iff_free (B : StandardKatoRellich)
    (hSA : SelfAdjointGraph (freeHilbertGraph V C κ hκ M hbound e))
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ (u : Reference I V) (f : WaveSpace I) (hf : FreePair V C κ hκ M hbound e u f),
      ‖perturbation V C κ hκ M hbound e A positive negative divA u (hmul u f hf)‖ ≤
        a * ‖f‖ + b * ‖inclusion I V u‖)
    (u : Reference I V) :
    (∃ (hu : ExternalDomain V A positive negative u) (f : WaveSpace I),
      IsOperatorPair V C κ hκ M hbound e A positive negative u hu f) ↔
      ∃ f : WaveSpace I, FreePair V C κ hκ M hbound e u f := by
  have heq := external_graph_eq_sum V C κ hκ M hbound e A positive negative divA
    hmul happrox B hSA a b ha ha1 hb hrel
  constructor
  · rintro ⟨hu, f, hf⟩
    have hh := (heq (inclusion I V u) f).mp
      (externalHilbertGraph_intro V C κ hκ M hbound e A positive negative u hu f _ rfl hf)
    unfold sumHilbertGraph at hh
    rcases hh with ⟨v, g, hg, hvu, hfg⟩
    have hv : v = u := inclusion_injective I V hvu
    subst v
    exact ⟨g, hg⟩
  · rintro ⟨f, hf⟩
    exact ⟨(hmul u f hf).domain, _, operatorPair_add_perturbation V C κ hκ M hbound e
      A positive negative divA u f (hmul u f hf)
      (freePair_value V C κ hκ M hbound e u f hf) (happrox u f hf)⟩

/-- The actual source equation, including its first-order perturbation,
follows from the domain identification rather than being a hypothesis. -/
theorem operatorPair_iff_free_sum (B : StandardKatoRellich)
    (hSA : SelfAdjointGraph (freeHilbertGraph V C κ hκ M hbound e))
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ (u : Reference I V) (f : WaveSpace I) (hf : FreePair V C κ hκ M hbound e u f),
      ‖perturbation V C κ hκ M hbound e A positive negative divA u (hmul u f hf)‖ ≤
        a * ‖f‖ + b * ‖inclusion I V u‖)
    (u : Reference I V) (f : WaveSpace I) (hu : ExternalDomain V A positive negative u) :
    IsOperatorPair V C κ hκ M hbound e A positive negative u hu f ↔
      ∃ (g : WaveSpace I) (hg : FreePair V C κ hκ M hbound e u g),
        f = g + perturbation V C κ hκ M hbound e A positive negative divA u (hmul u g hg) := by
  have heq := external_graph_eq_sum V C κ hκ M hbound e A positive negative divA
    hmul happrox B hSA a b ha ha1 hb hrel
  constructor
  · intro hf
    have hh := (heq (inclusion I V u) f).mp
      (externalHilbertGraph_intro V C κ hκ M hbound e A positive negative u hu f _ rfl hf)
    unfold sumHilbertGraph at hh
    rcases hh with ⟨v, g, hg, hvu, hfg⟩
    have hv : v = u := inclusion_injective I V hvu
    subst v
    exact ⟨g, hg, hfg⟩
  · rintro ⟨g, hg, rfl⟩
    exact operatorPair_add_perturbation V C κ hκ M hbound e A positive negative divA u g
      (hmul u g hg) (freePair_value V C κ hκ M hbound e u g hg) (happrox u g hg)

end PfHk.PhysicalExternalOperator
