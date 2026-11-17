import GptLean.WeylFormDisplacement
import GptLean.PhysicalFockRadiationCutoff
import GptLean.TransformationsFormOperator

/-! The represented radiation operator and its exact Weyl graph shift.
The operator is constructed from the actual densely defined radiation form.
The full-frequency assumption is used only to represent the field cross
term by a vector, as in Appendix A.
-/

noncomputable section
namespace GptLean.PhysicalWeyl

open MeasureTheory Filter Topology PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000

theorem radiationGraphInclusion_dense_weyl : DenseRange radiationGraphInclusion := by
  intro u
  exact mem_closure_of_tendsto (energyCutoff_tendsto u)
    (Eventually.of_forall fun M => ⟨radiationEnergyCutoff M u, rfl⟩)

/-- The actual radiation form as a densely embedded sesquilinear form. -/
def radiationOperatorForm : TransformationsFormOperator.Form
    (Q := RadiationGraphSpace) (H := PhotonFock) where
  inclusion := radiationGraphInclusion.toLinearMap
  injective := radiationGraphInclusion_injective_weyl
  dense := radiationGraphInclusion_dense_weyl
  value :=
    { toFun := fun q =>
        { toFun := fun r => ⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ
          map_add' := fun r s =>
            (congrArg (fun v : PhotonFock => ⟪radiationGraphDerivative q, v⟫_ℂ)
              (map_add radiationGraphDerivative r s)).trans (inner_add_right _ _ _)
          map_smul' := fun c r =>
            (congrArg (fun v : PhotonFock => ⟪radiationGraphDerivative q, v⟫_ℂ)
              (map_smul radiationGraphDerivative c r)).trans (inner_smul_right _ _ _) }
      map_add' := by
        intro q r
        ext s
        change ⟪radiationGraphDerivative (q + r), radiationGraphDerivative s⟫_ℂ =
          ⟪radiationGraphDerivative q, radiationGraphDerivative s⟫_ℂ +
          ⟪radiationGraphDerivative r, radiationGraphDerivative s⟫_ℂ
        exact (congrArg (fun v : PhotonFock => ⟪v, radiationGraphDerivative s⟫_ℂ)
          (map_add radiationGraphDerivative q r)).trans (inner_add_left _ _ _)
      map_smul' := by
        intro c q
        ext r
        change ⟪radiationGraphDerivative (c • q), radiationGraphDerivative r⟫_ℂ =
          (starRingEnd ℂ) c * ⟪radiationGraphDerivative q, radiationGraphDerivative r⟫_ℂ
        exact (congrArg (fun v : PhotonFock => ⟪v, radiationGraphDerivative r⟫_ℂ)
          (map_smul radiationGraphDerivative c q)).trans (inner_smul_left _ _ _) }

/-- The Hamiltonian represented by the radiation form, as a partially defined linear map. -/
def radiationHamiltonian : PhotonFock →ₗ.[ℂ] PhotonFock := radiationOperatorForm.operator

theorem radiationHamiltonian_graph (q : RadiationGraphSpace) (v : PhotonFock) :
    (radiationGraphInclusion q, v) ∈ radiationHamiltonian.graph ↔
      ∀ r, ⟪radiationGraphDerivative r, radiationGraphDerivative q⟫_ℂ =
        ⟪radiationGraphInclusion r, v⟫_ℂ := by
  have he := radiationOperatorForm.mem_operator_graph (radiationGraphInclusion q) v
  constructor
  · intro hq
    obtain ⟨p, hp, h⟩ := he.mp hq
    have hpq : p = q := radiationGraphInclusion_injective_weyl hp
    subst p
    exact h
  · intro h
    exact he.mpr ⟨q, rfl, h⟩

theorem weightedFieldForm_kernel (C : CanonicalSectorCCR photonMeasure)
    {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)
    (q r : RadiationGraphSpace) :
    weightedFieldForm K.val.2 q r = ⟪radiationGraphInclusion q, kernelField C K r⟫_ℂ := by
  calc
    weightedFieldForm K.val.2 q r =
        ⟪kernelAnnihilation K q, radiationGraphInclusion r⟫_ℂ +
          ⟪radiationGraphInclusion q, kernelAnnihilation K r⟫_ℂ :=
      congrArg₂ (fun a b : PhotonFock => ⟪a, radiationGraphInclusion r⟫_ℂ +
        ⟪radiationGraphInclusion q, b⟫_ℂ)
        (weightedAnnihilation_eq_kernel K hK q) (weightedAnnihilation_eq_kernel K hK r)
    _ = ⟪radiationGraphInclusion q, kernelCreation C K r⟫_ℂ +
          ⟪radiationGraphInclusion q, kernelAnnihilation K r⟫_ℂ :=
      congrArg (fun z : ℂ => z + ⟪radiationGraphInclusion q, kernelAnnihilation K r⟫_ℂ)
        (kernelAnnihilation_creation_duality C K q r)
    _ = _ := (add_comm _ _).trans (inner_add_right _ _ _).symm

variable (C : CanonicalSectorCCR photonMeasure) (W : ConcreteWeylLaw photonMeasure)
  (f : Lp ℂ 2 photonMeasure) (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

include hK in
/-- The exact radiation Hamiltonian shift on its full operator domain. -/
theorem radiationHamiltonian_weyl_graph (q : RadiationGraphSpace) (v : PhotonFock)
    (hv : (radiationGraphInclusion q, v) ∈ radiationHamiltonian.graph) :
    (W.weyl f (radiationGraphInclusion q),
      W.weyl f (v + kernelField C K q + (‖K.val.2‖ ^ 2 : ℂ) • radiationGraphInclusion q)) ∈
      radiationHamiltonian.graph := by
  let z := v + kernelField C K q + (‖K.val.2‖ ^ 2 : ℂ) • radiationGraphInclusion q
  have hq := (radiationHamiltonian_graph q v).mp hv
  have hm (r : RadiationGraphSpace) :
      ⟪radiationGraphDerivative (weylWeightedGraph W f K.val.2 hK r),
        radiationGraphDerivative (weylWeightedGraph W f K.val.2 hK q)⟫_ℂ =
        ⟪radiationGraphInclusion (weylWeightedGraph W f K.val.2 hK r), W.weyl f z⟫_ℂ := by
    calc
      _ = ⟪radiationGraphDerivative r, radiationGraphDerivative q⟫_ℂ +
          weightedFieldForm K.val.2 r q +
          (‖K.val.2‖ ^ 2 : ℂ) * ⟪radiationGraphInclusion r, radiationGraphInclusion q⟫_ℂ :=
        weylWeightedGraph_form W f K.val.2 hK r q
      _ = ⟪radiationGraphInclusion r, v⟫_ℂ +
          ⟪radiationGraphInclusion r, kernelField C K q⟫_ℂ +
          (‖K.val.2‖ ^ 2 : ℂ) * ⟪radiationGraphInclusion r, radiationGraphInclusion q⟫_ℂ :=
        congrArg (fun t : ℂ => t + (‖K.val.2‖ ^ 2 : ℂ) *
          ⟪radiationGraphInclusion r, radiationGraphInclusion q⟫_ℂ)
          (congrArg₂ (fun a b : ℂ => a + b) (hq r) (weightedFieldForm_kernel C K hK r q))
      _ = ⟪radiationGraphInclusion r, z⟫_ℂ := by
        dsimp only [z]
        exact (congrArg₂ (fun a b : ℂ => a + b) (inner_add_right _ _ _).symm
          (inner_smul_right _ _ _).symm).trans (inner_add_right _ _ _).symm
      _ = ⟪W.weyl f (radiationGraphInclusion r), W.weyl f z⟫_ℂ :=
        ((W.weyl f).inner_map_map _ _).symm
      _ = _ := congrArg (fun a : PhotonFock => ⟪a, W.weyl f z⟫_ℂ)
        (weylWeightedGraph_inclusion W f K.val.2 hK r).symm
  have hout : (radiationGraphInclusion (weylWeightedGraph W f K.val.2 hK q), W.weyl f z) ∈
      radiationHamiltonian.graph := (radiationHamiltonian_graph _ _).mpr (by
    intro p
    obtain ⟨r, rfl⟩ := weylWeightedGraph_surjective W f K.val.2 hK p
    exact hm r)
  simpa only [weylWeightedGraph_inclusion] using hout

include C hK in
theorem radiationHamiltonian_weyl_mem_domain (u : PhotonFock)
    (hu : u ∈ radiationHamiltonian.domain) : W.weyl f u ∈ radiationHamiltonian.domain := by
  obtain ⟨v, hv⟩ := LinearPMap.mem_domain_iff.mp hu
  obtain ⟨q, hq, _⟩ := (radiationOperatorForm.mem_operator_graph u v).mp hv
  have hq' : radiationGraphInclusion q = u := hq
  subst u
  exact LinearPMap.mem_domain_iff.mpr ⟨_, radiationHamiltonian_weyl_graph C W f K hK q v hv⟩

include C hK in
/-- Equality of the radiation operator domains in both displacement directions. -/
theorem radiationHamiltonian_weyl_domain_iff (u : PhotonFock) :
    W.weyl f u ∈ radiationHamiltonian.domain ↔ u ∈ radiationHamiltonian.domain := by
  constructor
  · intro hu
    have hn : ∀ᵐ p ∂photonMeasure, (-K).val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * (-f) p :=
      weighted_relation_neg f K.val.2 hK
    have h := radiationHamiltonian_weyl_mem_domain C W (-f) (-K) hn (W.weyl f u) hu
    rwa [weyl_neg_apply] at h
  · exact radiationHamiltonian_weyl_mem_domain C W f K hK u

end GptLean.PhysicalWeyl
