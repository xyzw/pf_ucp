import GptLean.PhysicalFreeForm
import GptLean.PhysicalSpatialRadiationDomain
import GptLean.PhotonLocalizationRellich
import Mathlib.Analysis.Normed.Operator.Banach

/-!
The actual free reference domain with its Hilbert form norm. It is the
closed range of the mass, weak derivative and radiation-root map, and
it covers exactly the spatial free vectors used by the local spectra.
-/

noncomputable section

namespace GptLean.PhysicalFreeHilbert

open MeasureTheory PhysicalFock PhotonLocalization
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000
set_option Elab.async false

private theorem closed_range_of_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (K : ℝ≥0) (h : ∀ u, ‖u‖ ≤ K * ‖L u‖) :
    IsClosed (Set.range L) :=
  (L.antilipschitz_of_bound (E := E) (F := F) (K := K) h).isClosed_range L.uniformContinuous

variable (I : Type) [Fintype I] [DecidableEq I]

local instance referenceNormedSpace : NormedSpace ℂ (PhysicalFreeForm.Reference I) :=
  (PhysicalFreeReferenceCore.freeSubspace I).normedSpace

local instance referenceModule : Module ℂ (PhysicalFreeForm.Reference I) :=
  (referenceNormedSpace I).toModule

local instance referenceSMul : SMul ℂ (PhysicalFreeForm.Reference I) :=
  (referenceModule I).toSMul

theorem energyOutput_injective : Function.Injective (PhysicalFreeForm.energyOutput I) := by
  intro u v h
  apply PhysicalFreeForm.inclusion_injective I
  exact (PhysicalFreeForm.energyOutput_mass I u).symm.trans
    ((congrArg (fun w : PhysicalFreeForm.EnergyOutput I => w (Sum.inr 0)) h).trans
      (PhysicalFreeForm.energyOutput_mass I v))

theorem energyOutput_closed : IsClosed (Set.range (PhysicalFreeForm.energyOutput I)) := by
  apply closed_range_of_bound (E := PhysicalFreeForm.Reference I)
    (F := PhysicalFreeForm.EnergyOutput I) (PhysicalFreeForm.energyOutput I) 2
  intro u
  exact PhysicalFreeForm.reference_norm_le_energyOutput I u

attribute [local irreducible] PhysicalFreeForm.energyOutput

abbrev Space := ↥(PhysicalFreeForm.energyOutput I).range

instance spaceCompleteSpace : CompleteSpace (Space I) :=
  (energyOutput_closed I).completeSpace_coe

def equiv : PhysicalFreeForm.Reference I ≃L[ℂ] Space I :=
  ContinuousLinearMap.equivRange (E := PhysicalFreeForm.Reference I)
    (F := PhysicalFreeForm.EnergyOutput I) (f := PhysicalFreeForm.energyOutput I)
    (σ' := RingHom.id ℂ) (energyOutput_injective I) (energyOutput_closed I)

@[simp] theorem coe_equiv (u : PhysicalFreeForm.Reference I) :
    (equiv I u).val = PhysicalFreeForm.energyOutput I u := rfl

theorem output_equiv_symm (u : Space I) :
    PhysicalFreeForm.energyOutput I ((equiv I).symm u) = u.val :=
  congrArg Subtype.val ((equiv I).apply_symm_apply u)

def inclusion : Space I →L[ℂ] PhysicalFreeForm.WaveSpace I :=
  (PhysicalFreeForm.inclusion I).comp (equiv I).symm.toContinuousLinearMap

theorem inclusion_injective : Function.Injective (inclusion I) :=
  (PhysicalFreeForm.inclusion_injective I).comp (equiv I).symm.injective

theorem inclusion_equiv (u : PhysicalFreeForm.Reference I) :
    inclusion I (equiv I u) = PhysicalFreeForm.inclusion I u :=
  congrArg (PhysicalFreeForm.inclusion I) ((equiv I).symm_apply_apply u)

theorem inclusion_denseRange : DenseRange (inclusion I) := by
  apply (PhysicalFreeReferenceCore.inclusion_denseRange I).mono
  rintro v ⟨u, rfl⟩
  exact ⟨equiv I u, inclusion_equiv I u⟩

theorem inclusion_norm_le (u : Space I) : ‖inclusion I u‖ ≤ ‖u‖ := by
  have h := PiLp.norm_apply_le u.val (Sum.inr 0)
  have he := congrArg (fun w : PhysicalFreeForm.EnergyOutput I => w (Sum.inr 0))
    (output_equiv_symm I u)
  exact (congrArg norm ((PhysicalFreeForm.energyOutput_mass I ((equiv I).symm u)).symm.trans he)).le.trans h

def vector (u : Space I) : SpatialFreeVector (I := I) radiationRoot where
  value := inclusion I u
  derivative := fun i => PhysicalFreeForm.ordinary I i ((equiv I).symm u)
  radiation := PhysicalFreeForm.radiation I ((equiv I).symm u)
  weak := ElectronicH1Complex.weak (PhysicalFreeReferenceCore.electronic I ((equiv I).symm u))
  radiation_graph := by
    have h := PhysicalSpatialRadiationDomain.source_graph
      (PhysicalFreeReferenceCore.radiationSource I ((equiv I).symm u))
    have he := PhysicalFreeReferenceCore.value_matching I ((equiv I).symm u)
    exact (congrArg (fun v : PhysicalFreeForm.WaveSpace I => ∀ᵐ x ∂volume,
      (v x, PhysicalFreeForm.radiation I ((equiv I).symm u) x) ∈ radiationRoot.graph) he).mpr h

theorem vector_form (u : Space I) : (vector I u).form = ‖u‖ ^ 2 :=
  (PhysicalFreeForm.energyOutput_norm_sq I ((equiv I).symm u)).symm.trans
    (congrArg (fun w : PhysicalFreeForm.EnergyOutput I => ‖w‖ ^ 2) (output_equiv_symm I u))

private theorem radiation_integral_finite (u : SpatialFreeVector (I := I) radiationRoot) :
    ∫⁻ x, radiationForm (u.value x) ∂volume < ⊤ := by
  have he : (fun x => radiationForm (u.value x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (‖u.radiation x‖ ^ 2)) := by
    filter_upwards [u.radiation_graph] with x hx
    obtain ⟨v, hv, hr⟩ := radiationRoot.mem_graph_iff.mp hx
    change (v : PhotonFock) = u.value x at hv
    change radiationRoot v = u.radiation x at hr
    rw [← hv, ← hr]
    exact radiationRoot_energy v
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.radiation)).mp (Lp.memLp u.radiation))
    (ae_of_all _ fun x => sq_nonneg _)]
  exact ENNReal.ofReal_lt_top

def ofVector (u : SpatialFreeVector (I := I) radiationRoot) : PhysicalFreeForm.Reference I :=
  ⟨(⟨(u.value, u.derivative), u.weak⟩,
      PhysicalSpatialRadiationDomain.source u.value (radiation_integral_finite I u)), by
    change u.value - spatialRadiationInclusion volume
      (PhysicalSpatialRadiationDomain.source u.value (radiation_integral_finite I u)) = 0
    exact sub_eq_zero.mpr (PhysicalSpatialRadiationDomain.source_inclusion _ _).symm⟩

@[simp] theorem inclusion_ofVector (u : SpatialFreeVector (I := I) radiationRoot) :
    PhysicalFreeForm.inclusion I (ofVector I u) = u.value := rfl

@[simp] theorem ordinary_ofVector (u : SpatialFreeVector (I := I) radiationRoot) (i : I) :
    PhysicalFreeForm.ordinary I i (ofVector I u) = u.derivative i := rfl

theorem radiation_ofVector (u : SpatialFreeVector (I := I) radiationRoot) :
    PhysicalFreeForm.radiation I (ofVector I u) = u.radiation := by
  have h := PhysicalSpatialRadiationDomain.source_graph
    (PhysicalSpatialRadiationDomain.source u.value (radiation_integral_finite I u))
  have hi := PhysicalSpatialRadiationDomain.source_inclusion u.value (radiation_integral_finite I u)
  have h' : ∀ᵐ x ∂volume,
      (u.value x, PhysicalFreeForm.radiation I (ofVector I u) x) ∈ radiationRoot.graph :=
    (congrArg (fun v : PhysicalFreeForm.WaveSpace I => ∀ᵐ x ∂volume,
      (v x, PhysicalFreeForm.radiation I (ofVector I u) x) ∈ radiationRoot.graph) hi).mp h
  apply Lp.ext
  filter_upwards [h', u.radiation_graph] with x hs hu
  exact radiationRoot.mem_graph_snd_inj hs hu rfl

theorem energy_ofVector (u : SpatialFreeVector (I := I) radiationRoot) :
    PhysicalFreeForm.energy I (ofVector I u) = u.form := by
  simp only [PhysicalFreeForm.energy, inclusion_ofVector, ordinary_ofVector,
    radiation_ofVector, SpatialFreeVector.form]

theorem covers (u : SpatialFreeVector (I := I) radiationRoot) :
    ∃ q : Space I, inclusion I q = u.value ∧ ‖q‖ ^ 2 = u.form := by
  refine ⟨equiv I (ofVector I u), ?_, ?_⟩
  · exact (inclusion_equiv I (ofVector I u)).trans (inclusion_ofVector I u)
  · exact (PhysicalFreeForm.energyOutput_norm_sq I (ofVector I u)).trans (energy_ofVector I u)

end GptLean.PhysicalFreeHilbert
