import GptLean.ElectronicH1Complex
import GptLean.PhysicalFockSpatialField
import GptLean.PhysicalMultiplicationGraph

/-!
One common reference domain for ordinary electronic derivatives, the
actual photon radiation graph, and the potential square-root graph.
Matching L2 values defines a closed subspace of three complete graph
spaces. The covariant derivatives use the constructed position-dependent
Fock fields on this very same domain.
-/

noncomputable section

namespace GptLean.PhysicalPFReference

open MeasureTheory PhysicalFock
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

private def differencePair {Q W : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f g h : Q →L[ℂ] W) : Q →L[ℂ] W × W := (f - g).prod (f - h)

private def affineDerivative {Q W : Type*} [TopologicalSpace Q] [AddCommGroup Q] [Module ℂ Q]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f g : Q →L[ℂ] W) (e : ℝ) : Q →L[ℂ] W := (-Complex.I) • f - (e : ℂ) • g

private theorem lp_norm_le_add {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {μ : Measure X} (u : Lp E 2 μ) (f : Lp F 2 μ) (g : Lp G 2 μ)
    (h : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖ + ‖g x‖) : ‖u‖ ≤ ‖f‖ + ‖g‖ := by
  let fn : Lp ℝ 2 μ := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  let gn : Lp ℝ 2 μ := (Lp.memLp g).norm.toLp (fun x => ‖g x‖)
  have hb : ‖u‖ ≤ ‖fn + gn‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, (Lp.memLp f).norm.coeFn_toLp,
      (Lp.memLp g).norm.coeFn_toLp, Lp.coeFn_add fn gn] with x hx hf hg ha
    rw [ha, Pi.add_apply]
    change ‖u x‖ ≤ ‖fn x + gn x‖
    rw [hf, hg, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hx
  have hf : ‖fn‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hg : ‖gn‖ = ‖g‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  exact hb.trans ((norm_add_le fn gn).trans_eq (by rw [hf, hg]))

private theorem lp_maps_norm_le {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (μ : Measure X) (f : E →L[ℂ] F) (g : E →L[ℂ] G)
    (h : ∀ v, ‖v‖ ≤ ‖f v‖ + ‖g v‖) (u : Lp E 2 μ) :
    ‖u‖ ≤ ‖f.compLpL 2 μ u‖ + ‖g.compLpL 2 μ u‖ := by
  apply lp_norm_le_add u (f.compLpL 2 μ u) (g.compLpL 2 μ u)
  filter_upwards [f.coeFn_compLpL u, g.coeFn_compLpL u] with x hf hg
  rw [hf, hg]
  exact h (u x)

private theorem spatialRadiation_norm_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : SpatialRadiationGraph μ) :
    ‖u‖ ≤ ‖spatialRadiationInclusion μ u‖ + ‖spatialRadiationDerivative μ u‖ := by
  exact lp_maps_norm_le μ radiationGraphInclusion radiationGraphDerivative
    (fun v => max_le (le_add_of_nonneg_right (norm_nonneg v.val.2))
      (le_add_of_nonneg_left (norm_nonneg v.val.1))) u

variable (I : Type*) [Fintype I] [DecidableEq I]

abbrev Position := EuclideanSpace ℝ I
abbrev WaveSpace := Lp PhotonFock 2 (volume : Measure (Position I))
abbrev ElectronicGraph := ElectronicH1Complex.ComplexH1 PhotonFock I
abbrev RadiationGraph := SpatialRadiationGraph (volume : Measure (Position I))
abbrev PotentialGraph (V : Position I → ℝ) :=
  PhysicalMultiplicationGraph.GraphSpace volume (H := PhotonFock) (fun x => (Real.sqrt (V x) : ℂ))
abbrev Ambient (V : Position I → ℝ) := ElectronicGraph I × RadiationGraph I × PotentialGraph I V

variable (V : Position I → ℝ)

def electronicCoordinate : Ambient I V →L[ℂ] ElectronicGraph I := ContinuousLinearMap.fst _ _ _
def radiationCoordinate : Ambient I V →L[ℂ] RadiationGraph I :=
  (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
def potentialCoordinate : Ambient I V →L[ℂ] PotentialGraph I V :=
  (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)

def ambientValue : Ambient I V →L[ℂ] WaveSpace I :=
  (ElectronicH1Complex.value (E := PhotonFock) (I := I)).comp (electronicCoordinate I V)

def ambientRadiationValue : Ambient I V →L[ℂ] WaveSpace I :=
  (spatialRadiationInclusion (volume : Measure (Position I))).comp (radiationCoordinate I V)

def ambientPotentialValue : Ambient I V →L[ℂ] WaveSpace I :=
  (PhysicalMultiplicationGraph.inclusion (volume : Measure (Position I))
    (H := PhotonFock) (fun x => (Real.sqrt (V x) : ℂ))).comp (potentialCoordinate I V)

def matching : Ambient I V →L[ℂ] WaveSpace I × WaveSpace I :=
  differencePair (Q := Ambient I V) (W := WaveSpace I)
    (ambientValue I V) (ambientRadiationValue I V) (ambientPotentialValue I V)

def referenceSubspace : Submodule ℂ (Ambient I V) := (matching I V).ker
abbrev Reference := ↥(referenceSubspace I V)

instance referenceNormedSpace : NormedSpace ℂ (Reference I V) :=
  (referenceSubspace I V).normedSpace

instance referenceCompleteSpace : CompleteSpace (Reference I V) :=
  (matching I V).isClosed_ker.completeSpace_coe

def electronic : Reference I V →L[ℂ] ElectronicGraph I :=
  (electronicCoordinate I V).comp (referenceSubspace I V).subtypeL
def radiationSource : Reference I V →L[ℂ] RadiationGraph I :=
  (radiationCoordinate I V).comp (referenceSubspace I V).subtypeL
def potentialSource : Reference I V →L[ℂ] PotentialGraph I V :=
  (potentialCoordinate I V).comp (referenceSubspace I V).subtypeL

def inclusion : Reference I V →L[ℂ] WaveSpace I := ElectronicH1Complex.value.comp (electronic I V)
def ordinary (i : I) : Reference I V →L[ℂ] WaveSpace I :=
  (ElectronicH1Complex.derivative i).comp (electronic I V)
def radiation : Reference I V →L[ℂ] WaveSpace I :=
  (spatialRadiationDerivative volume).comp (radiationSource I V)
def potential : Reference I V →L[ℂ] WaveSpace I :=
  (PhysicalMultiplicationGraph.output volume _).comp (potentialSource I V)

theorem radiation_matches (u : Reference I V) :
    spatialRadiationInclusion volume (radiationSource I V u) = inclusion I V u := by
  have h := congrArg Prod.fst u.property
  change inclusion I V u - spatialRadiationInclusion volume (radiationSource I V u) = 0 at h
  exact (sub_eq_zero.mp h).symm

theorem potential_matches (u : Reference I V) :
    PhysicalMultiplicationGraph.inclusion volume _ (potentialSource I V u) = inclusion I V u := by
  have h := congrArg Prod.snd u.property
  change inclusion I V u -
    PhysicalMultiplicationGraph.inclusion volume _ (potentialSource I V u) = 0 at h
  exact (sub_eq_zero.mp h).symm

private theorem radiationGraphInclusion_injective : Function.Injective radiationGraphInclusion := by
  intro u v h
  have hz : (u - v).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (u - v).property hz
  apply Subtype.ext
  exact Prod.ext h (sub_eq_zero.mp ho)

omit [DecidableEq I] in
private theorem spatialRadiationInclusion_injective :
    Function.Injective (spatialRadiationInclusion (volume : Measure (Position I))) := by
  intro u v h
  apply Lp.ext
  filter_upwards [radiationGraphInclusion.coeFn_compLpL u,
    radiationGraphInclusion.coeFn_compLpL v] with x hu hv
  apply radiationGraphInclusion_injective
  have he := congrArg (fun w : WaveSpace I => w x) h
  exact hu.symm.trans (he.trans hv)

/-- A vector in the reference domain is uniquely determined by its
physical L2 wave function, including all three graph components. -/
theorem inclusion_injective : Function.Injective (inclusion I V) := by
  intro u v h
  have he : electronic I V u = electronic I V v := ElectronicH1Complex.value_injective h
  have hr : radiationSource I V u = radiationSource I V v :=
    spatialRadiationInclusion_injective I
      ((radiation_matches I V u).trans (h.trans (radiation_matches I V v).symm))
  have hp : potentialSource I V u = potentialSource I V v :=
    PhysicalMultiplicationGraph.inclusion_injective volume _
      ((potential_matches I V u).trans (h.trans (potential_matches I V v).symm))
  apply Subtype.ext
  exact Prod.ext he (Prod.ext hr hp)

theorem radiationSource_norm_le (u : Reference I V) :
    ‖radiationSource I V u‖ ≤ ‖inclusion I V u‖ + ‖radiation I V u‖ := by
  have h := spatialRadiation_norm_le volume (radiationSource I V u)
  exact h.trans_eq (congrArg₂ (fun (f g : WaveSpace I) => ‖f‖ + ‖g‖)
    (radiation_matches I V u) rfl)

theorem potentialSource_norm (u : Reference I V) :
    ‖potentialSource I V u‖ = max ‖inclusion I V u‖ ‖potential I V u‖ := by
  exact congrArg₂ (fun (f g : WaveSpace I) => max ‖f‖ ‖g‖)
    (potential_matches I V u) rfl

theorem potential_energy (hV : ∀ x, 0 ≤ V x) (u : Reference I V) :
    ENNReal.ofReal (‖potential I V u‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal (V x) * ENNReal.ofReal (‖inclusion I V u x‖ ^ 2) := by
  have h := PhysicalMultiplicationGraph.sqrt_output_energy volume V hV (potentialSource I V u)
  exact h.trans (congrArg (fun f : WaveSpace I =>
    ∫⁻ x, ENNReal.ofReal (V x) * ENNReal.ofReal (‖f x‖ ^ 2)) (potential_matches I V u))

theorem radiation_graph (u : Reference I V) :
    ∀ᵐ x ∂volume, (inclusion I V u x, radiation I V u x) ∈ radiationRoot.graph := by
  have hi : inclusion I V u =ᵐ[volume]
      (fun x => radiationGraphInclusion (radiationSource I V u x)) :=
    (Filter.EventuallyEq.of_eq (congrArg (fun f : WaveSpace I => ⇑f)
      (radiation_matches I V u).symm)).trans
        (radiationGraphInclusion.coeFn_compLpL (radiationSource I V u))
  have hd : radiation I V u =ᵐ[volume]
      (fun x => radiationGraphDerivative (radiationSource I V u x)) :=
    radiationGraphDerivative.coeFn_compLpL (radiationSource I V u)
  filter_upwards [hi, hd] with x hx hy
  exact (congrArg (fun p : PhotonFock × PhotonFock => p ∈ radiationRoot.graph)
    (Prod.ext hx hy)).mpr (radiationSource I V u x).property

def freeVector (u : Reference I V) :
    PhotonLocalization.SpatialFreeVector (I := I) radiationRoot where
  value := inclusion I V u
  derivative := fun i => ordinary I V i u
  radiation := radiation I V u
  weak := ElectronicH1Complex.weak (electronic I V u)
  radiation_graph := radiation_graph I V u

theorem freeVector_form (u : Reference I V) :
    (freeVector I V u).form = ‖inclusion I V u‖ ^ 2 +
      (∑ i, ‖ordinary I V i u‖ ^ 2) + ‖radiation I V u‖ ^ 2 := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)

def field (i : I) : Reference I V →L[ℂ] WaveSpace I :=
  (spatialField volume C (κ i) (hκ i) M (hbound i)).comp (radiationSource I V)

def covariant (e : ℝ) (i : I) : Reference I V →L[ℂ] WaveSpace I :=
  affineDerivative (Q := Reference I V) (W := WaveSpace I)
    (ordinary I V i) (field I V C κ hκ M hbound i) e

theorem covariant_apply (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i u =
      (-Complex.I) • ordinary I V i u - (e : ℂ) • field I V C κ hκ M hbound i u := rfl

def kineticEnergy (e : ℝ) (u : Reference I V) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ‖covariant I V C κ hκ M hbound e i u‖ ^ 2

def energy (e : ℝ) (u : Reference I V) : ℝ :=
  kineticEnergy I V C κ hκ M hbound e u + ‖radiation I V u‖ ^ 2 + ‖potential I V u‖ ^ 2

theorem energy_nonneg (e : ℝ) (u : Reference I V) : 0 ≤ energy I V C κ hκ M hbound e u := by
  unfold energy kineticEnergy
  positivity

theorem radiation_le_energy (e : ℝ) (u : Reference I V) :
    ‖radiation I V u‖ ^ 2 ≤ energy I V C κ hκ M hbound e u := by
  have hk : 0 ≤ kineticEnergy I V C κ hκ M hbound e u := by
    unfold kineticEnergy
    positivity
  unfold energy
  linarith [sq_nonneg ‖potential I V u‖]

theorem potential_le_energy (e : ℝ) (u : Reference I V) :
    ‖potential I V u‖ ^ 2 ≤ energy I V C κ hκ M hbound e u := by
  have hk : 0 ≤ kineticEnergy I V C κ hκ M hbound e u := by
    unfold kineticEnergy
    positivity
  unfold energy
  linarith [sq_nonneg ‖radiation I V u‖]

theorem field_radiation_bound (i : I) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hneg : ∀ᵐ x ∂volume, ‖(κ i x).val.2‖ ≤ A)
    (hl2 : ∀ᵐ x ∂volume, ‖(κ i x).val.1‖ ≤ B) (u : Reference I V) :
    ‖field I V C κ hκ M hbound i u‖ ^ 2 ≤
      8 * A ^ 2 * ‖radiation I V u‖ ^ 2 + 2 * B ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  have h := spatialField_radiation_bound volume C (κ i) (hκ i) M (hbound i)
    A B hA hB hneg hl2 (radiationSource I V u)
  exact h.trans_eq (congrArg₂ (fun (f g : WaveSpace I) =>
    8 * A ^ 2 * ‖f‖ ^ 2 + 2 * B ^ 2 * ‖g‖ ^ 2) rfl (radiation_matches I V u))

end GptLean.PhysicalPFReference
