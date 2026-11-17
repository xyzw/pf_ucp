import GptLean.PhysicalFockHardOperators
import GptLean.PhysicalFockMomentumProjection
import GptLean.PhysicalPFVacuumInsertion
import GptLean.PhysicalSpatialRadiationDomain
import GptLean.RemovalGaussianLatticeSource

/-!
The actual hard radiation graph is recovered from finite integrated
radiation form. Uniqueness gives linearity and scalar locality. A linear
input family with a quadratic form bound therefore has a bounded linear
hard radiation output, without a separate output-matching assumption.
-/

noncomputable section

namespace GptLean.PhysicalHardSpatialRadiation

open MeasureTheory Filter Topology PhysicalFock PhysicalPFVacuumInsertion
  RemovalSource
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section GraphAlgebra

variable {Y H : Type*} [MeasurableSpace Y] (ν : Measure Y)
  [NormedAddCommGroup H] [NormedSpace ℂ H] (D : H →ₗ.[ℂ] H)

private theorem graph_add (u v r s : Lp H 2 ν)
    (hu : ∀ᵐ x ∂ν, (u x, r x) ∈ D.graph)
    (hv : ∀ᵐ x ∂ν, (v x, s x) ∈ D.graph) :
    ∀ᵐ x ∂ν, ((u + v) x, (r + s) x) ∈ D.graph := by
  filter_upwards [hu, hv, Lp.coeFn_add u v, Lp.coeFn_add r s]
    with x hu hv hi ho
  rw [hi, ho, Pi.add_apply, Pi.add_apply]
  exact D.graph.add_mem hu hv

private theorem graph_smul (a : ℂ) (u r : Lp H 2 ν)
    (hu : ∀ᵐ x ∂ν, (u x, r x) ∈ D.graph) :
    ∀ᵐ x ∂ν, ((a • u) x, (a • r) x) ∈ D.graph := by
  filter_upwards [hu, Lp.coeFn_smul a u, Lp.coeFn_smul a r] with x hu hi ho
  rw [hi, ho, Pi.smul_apply, Pi.smul_apply]
  exact D.graph.smul_mem a hu

end GraphAlgebra

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (BF : StandardSymmetricFockExponential) (κ : ℝ)

abbrev Hard := ↥(generatedFockSubspace (hardOnePhoton κ))
abbrev HardL2 := Lp (Hard κ) 2 μ

def finite (u : HardL2 μ κ) : Prop :=
  ∫⁻ x, radiationForm ((u x : Hard κ) : PhotonFock) ∂μ < ⊤

private def ambient (u : HardL2 μ κ) : Lp PhotonFock 2 μ :=
  spatialLift μ (generatedFockSubspace (hardOnePhoton κ)).subtypeₗᵢ u

private theorem ambient_ae (u : HardL2 μ κ) :
    ambient μ κ u =ᵐ[μ] fun x => (u x : PhotonFock) := by
  unfold ambient spatialLift
  exact (generatedFockSubspace (hardOnePhoton κ)).subtypeL.coeFn_compLpL u

private theorem ambient_finite (u : HardL2 μ κ) (hu : finite μ κ u) :
    ∫⁻ x, radiationForm (ambient μ κ u x) ∂μ < ⊤ := by
  rw [lintegral_congr_ae ((ambient_ae μ κ u).mono (fun _ hx => congrArg radiationForm hx))]
  exact hu

private def source (u : HardL2 μ κ) (hu : finite μ κ u) : SpatialRadiationGraph μ :=
  PhysicalSpatialRadiationDomain.source (ambient μ κ u) (ambient_finite μ κ u hu)

private theorem source_value (u : HardL2 μ κ) (hu : finite μ κ u) :
    ∀ᵐ x ∂μ, radiationGraphInclusion (source μ κ u hu x) = (u x : PhotonFock) := by
  have he := PhysicalSpatialRadiationDomain.source_inclusion (ambient μ κ u) (ambient_finite μ κ u hu)
  filter_upwards [radiationGraphInclusion.coeFn_compLpL (source μ κ u hu), ambient_ae μ κ u]
    with x hx hu
  exact hx.symm.trans ((congrArg (fun w : Lp PhotonFock 2 μ => w x) he).trans hu)

def output (u : HardL2 μ κ) (hu : finite μ κ u) : HardL2 μ κ :=
  (((generatedFockSubspace (hardOnePhoton κ)).orthogonalProjectionOnto).comp
    radiationGraphDerivative).compLpL 2 μ (source μ κ u hu)

include BF

theorem output_graph (u : HardL2 μ κ) (hu : finite μ κ u) :
    ∀ᵐ x ∂μ, (u x, output μ κ u hu x) ∈ (hardRadiationOperator κ).graph := by
  filter_upwards [source_value μ κ u hu,
    ((((generatedFockSubspace (hardOnePhoton κ)).orthogonalProjectionOnto).comp
      radiationGraphDerivative).coeFn_compLpL (source μ κ u hu))] with x hi ho
  have hq : radiationGraphInclusion (source μ κ u hu x) ∈
      generatedFockSubspace (hardOnePhoton κ) := hi.symm ▸ (u x).property
  have hr := radiationGraphDerivative_mem_hardGenerated BF κ (source μ κ u hu x) hq
  apply (hardRadiationOperator_graph_iff κ _ _).mpr
  have he : ((output μ κ u hu x : Hard κ) : PhotonFock) =
      radiationGraphDerivative (source μ κ u hu x) := by
    change ((↑((((generatedFockSubspace (hardOnePhoton κ)).orthogonalProjectionOnto).comp
      radiationGraphDerivative).compLpL 2 μ (source μ κ u hu) x) : PhotonFock)) = _
    rw [ho]
    exact ((generatedFockSubspace (hardOnePhoton κ)).coe_orthogonalProjectionOnto_apply _).trans
      ((generatedFockSubspace (hardOnePhoton κ)).starProjection_eq_self_iff.mpr hr)
  rw [he, ← hi]
  exact (source μ κ u hu x).property

omit BF in
theorem graph_unique (u r s : HardL2 μ κ)
    (hr : ∀ᵐ x ∂μ, (u x, r x) ∈ (hardRadiationOperator κ).graph)
    (hs : ∀ᵐ x ∂μ, (u x, s x) ∈ (hardRadiationOperator κ).graph) : r = s := by
  apply Lp.ext
  filter_upwards [hr, hs] with x hr hs
  exact (hardRadiationOperator κ).mem_graph_snd_inj hr hs rfl

omit BF in
theorem graph_integral (u r : HardL2 μ κ)
    (hr : ∀ᵐ x ∂μ, (u x, r x) ∈ (hardRadiationOperator κ).graph) :
    (∫⁻ x, radiationForm (u x : PhotonFock) ∂μ) = ENNReal.ofReal (‖r‖ ^ 2) := by
  rw [lintegral_congr_ae (hr.mono (fun _ hx => hardRadiationOperator_energy κ _ _ hx)),
    ← ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable r)).mp (Lp.memLp r))
      (ae_of_all _ fun x => sq_nonneg _)]
  let : InnerProductSpace ℝ (Hard κ) := InnerProductSpace.complexToReal
  rw [← PhotonKernelLocalization.l2_norm_sq_eq_integral]

omit BF in
theorem finite_of_graph (u r : HardL2 μ κ)
    (hr : ∀ᵐ x ∂μ, (u x, r x) ∈ (hardRadiationOperator κ).graph) : finite μ κ u := by
  change (∫⁻ x, radiationForm (u x : PhotonFock) ∂μ) < ⊤
  rw [graph_integral μ κ u r hr]
  exact ENNReal.ofReal_lt_top

theorem output_norm_sq (u : HardL2 μ κ) (hu : finite μ κ u) :
    ENNReal.ofReal (‖output μ κ u hu‖ ^ 2) =
      ∫⁻ x, radiationForm (u x : PhotonFock) ∂μ :=
  (graph_integral μ κ u _ (output_graph μ BF κ u hu)).symm

theorem output_add (u v : HardL2 μ κ) (hu : finite μ κ u) (hv : finite μ κ v)
    (huv : finite μ κ (u + v)) :
    output μ κ (u + v) huv = output μ κ u hu + output μ κ v hv := by
  exact graph_unique μ κ (u + v) (output μ κ (u + v) huv)
    (output μ κ u hu + output μ κ v hv) (output_graph μ BF κ (u + v) huv)
    (graph_add μ (hardRadiationOperator κ) u v (output μ κ u hu) (output μ κ v hv)
      (output_graph μ BF κ u hu) (output_graph μ BF κ v hv))

theorem output_smul (a : ℂ) (u : HardL2 μ κ) (hu : finite μ κ u)
    (hau : finite μ κ (a • u)) : output μ κ (a • u) hau = a • output μ κ u hu := by
  exact graph_unique μ κ (a • u) (output μ κ (a • u) hau)
    (a • output μ κ u hu) (output_graph μ BF κ (a • u) hau)
    (graph_smul μ (hardRadiationOperator κ) a u (output μ κ u hu)
      (output_graph μ BF κ u hu))

omit BF in
/-- The off-domain value is zero, and every operator identity uses its domain. -/
def apply (u : HardL2 μ κ) : HardL2 μ κ := by
  classical
  exact if hu : finite μ κ u then output μ κ u hu else 0

theorem apply_graph (u : HardL2 μ κ) (hu : finite μ κ u) :
    ∀ᵐ x ∂μ, (u x, apply μ κ u x) ∈ (hardRadiationOperator κ).graph := by
  rw [apply, dite_eq_left hu]
  exact output_graph μ BF κ u hu

theorem apply_norm_sq (u : HardL2 μ κ) (hu : finite μ κ u) :
    ENNReal.ofReal (‖apply μ κ u‖ ^ 2) =
      ∫⁻ x, radiationForm (u x : PhotonFock) ∂μ := by
  rw [apply, dite_eq_left hu]
  exact output_norm_sq μ BF κ u hu

theorem finite_iff_exists_graph (u : HardL2 μ κ) : finite μ κ u ↔
    ∃ r : HardL2 μ κ, ∀ᵐ x ∂μ, (u x, r x) ∈ (hardRadiationOperator κ).graph := by
  constructor
  · intro hu
    exact ⟨output μ κ u hu, output_graph μ BF κ u hu⟩
  · rintro ⟨r, hr⟩
    exact finite_of_graph μ κ u r hr

theorem locality [SFinite μ] : SpatialRadiationLocality (finite μ κ) (apply μ κ) := by
  intro g hg M hb u hu
  have hgraph : ∀ᵐ x ∂μ,
      (boundedRealProduct g hg M hb u x,
        boundedRealProduct g hg M hb (output μ κ u hu) x) ∈
        (hardRadiationOperator κ).graph := by
    filter_upwards [output_graph μ BF κ u hu,
      (boundedRealProduct_memLp g hg M hb u).coeFn_toLp,
      (boundedRealProduct_memLp g hg M hb (output μ κ u hu)).coeFn_toLp]
      with x hx hi ho
    change ((boundedRealProduct_memLp g hg M hb u).toLp _ x,
      (boundedRealProduct_memLp g hg M hb (output μ κ u hu)).toLp _ x) ∈ _
    rw [hi, ho]
    exact (hardRadiationOperator κ).graph.smul_mem (g x : ℂ) hx
  have hp := finite_of_graph μ κ _ _ hgraph
  refine ⟨hp, ?_⟩
  rw [apply, dite_eq_left hp, apply, dite_eq_left hu]
  exact graph_unique μ κ _ _ _ (output_graph μ BF κ _ hp) hgraph

section LinearLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (L : E →L[ℂ] HardL2 μ κ) (hL : ∀ v, finite μ κ (L v))

def linearOutput : E →ₗ[ℂ] HardL2 μ κ where
  toFun v := output μ κ (L v) (hL v)
  map_add' u v := by
    have he := output_add μ BF κ (L u) (L v) (hL u) (hL v)
      ((congrArg (finite μ κ) (L.map_add u v)).mp (hL (u + v)))
    simpa only [L.map_add] using he
  map_smul' a u := by
    have he := output_smul μ BF κ a (L u) (hL u)
      ((congrArg (finite μ κ) (L.map_smul a u)).mp (hL (a • u)))
    simpa only [RingHom.id_apply, L.map_smul] using he

def boundedOutput (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ v, ∫⁻ x, radiationForm (L v x : PhotonFock) ∂μ ≤
      ENNReal.ofReal ((K * ‖v‖) ^ 2)) : E →L[ℂ] HardL2 μ κ := by
  have hnorm : ∀ v, ‖linearOutput μ BF κ L hL v‖ ≤ K * ‖v‖ := by
    intro v
    change ‖output μ κ (L v) (hL v)‖ ≤ K * ‖v‖
    have h := (output_norm_sq μ BF κ (L v) (hL v)).le.trans (hbound v)
    have hsq : ‖output μ κ (L v) (hL v)‖ ^ 2 ≤ (K * ‖v‖) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
    have hout : 0 ≤ ‖output μ κ (L v) (hL v)‖ :=
      norm_nonneg (output μ κ (L v) (hL v))
    exact (sq_le_sq₀ hout (mul_nonneg hK (norm_nonneg v))).mp hsq
  exact LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := E)
    (F := HardL2 μ κ) (σ := RingHom.id ℂ) (linearOutput μ BF κ L hL) K hnorm

theorem boundedOutput_apply (K : ℝ) (hK : 0 ≤ K) (hbound) (v : E) :
    boundedOutput μ BF κ L hL K hK hbound v = output μ κ (L v) (hL v) := rfl

theorem boundedOutput_graph (K : ℝ) (hK : 0 ≤ K) (hbound) (v : E) :
    ∀ᵐ x ∂μ, (L v x, boundedOutput μ BF κ L hL K hK hbound v x) ∈
      (hardRadiationOperator κ).graph := by
  exact (congrArg (fun w : HardL2 μ κ =>
    ∀ᵐ x ∂μ, (L v x, w x) ∈ (hardRadiationOperator κ).graph)
      (boundedOutput_apply μ BF κ L hL K hK hbound v)).mpr
        (output_graph μ BF κ (L v) (hL v))

theorem boundedOutput_norm_sq (K : ℝ) (hK : 0 ≤ K) (hbound) (v : E) :
    ENNReal.ofReal (‖boundedOutput μ BF κ L hL K hK hbound v‖ ^ 2) =
      ∫⁻ x, radiationForm (L v x : PhotonFock) ∂μ :=
  (congrArg (fun w : HardL2 μ κ => ENNReal.ofReal (‖w‖ ^ 2))
    (boundedOutput_apply μ BF κ L hL K hK hbound v)).trans
      (output_norm_sq μ BF κ (L v) (hL v))

end LinearLift

end GptLean.PhysicalHardSpatialRadiation
