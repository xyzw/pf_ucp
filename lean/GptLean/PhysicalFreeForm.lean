import GptLean.PhysicalFreeReferenceCore
import GptLean.PhysicalClosedForms
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The actual free positive form on spatial photon Fock space. Its closed
operator has coordinates consisting of mass, every electronic weak
derivative, and the radiation square root. The pure-state value is
exactly their squared Hilbert norm.
-/

noncomputable section

namespace GptLean.PhysicalFreeForm

open MeasureTheory PhysicalFock PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency.types true

private theorem norm_sq_sum_two {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] (v : PiLp 2 (fun _ : I ⊕ Fin 2 => E)) :
    ‖v‖ ^ 2 = ‖v (Sum.inr 0)‖ ^ 2 +
      (∑ i, ‖v (Sum.inl i)‖ ^ 2) + ‖v (Sum.inr 1)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

private theorem closed_range_of_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (K : ℝ≥0) (h : ∀ u, ‖u‖ ≤ K * ‖L u‖) :
    IsClosed (Set.range L) :=
  (L.antilipschitz_of_bound (E := E) (F := F) (K := K) h).isClosed_range L.uniformContinuous

theorem domain_iff_of_graph_range {Q H K : Type*}
    [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
    (g : Q → H × K) (D : H →ₗ.[ℂ] K)
    (hD : (D.graph : Set (H × K)) = Set.range g) (v : H) :
    v ∈ D.domain ↔ ∃ q, (g q).1 = v := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := LinearPMap.mem_domain_iff.mp hv
    change (v, w) ∈ (D.graph : Set (H × K)) at hw
    rw [hD] at hw
    obtain ⟨q, hq⟩ := hw
    exact ⟨q, congrArg Prod.fst hq⟩
  · rintro ⟨q, hq⟩
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨(g q).2, ?_⟩
    change (v, (g q).2) ∈ (D.graph : Set (H × K))
    rw [hD]
    exact ⟨q, Prod.ext hq rfl⟩

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
  have hf : ‖fn‖ = ‖f‖ := by rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hg : ‖gn‖ = ‖g‖ := by rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  exact hb.trans ((norm_add_le fn gn).trans_eq (by rw [hf, hg]))

private theorem lp_maps_norm_le {X E F G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (μ : Measure X) (f : E →L[ℂ] F) (g : E →L[ℂ] G)
    (h : ∀ v, ‖v‖ ≤ ‖f v‖ + ‖g v‖) (u : Lp E 2 μ) :
    ‖u‖ ≤ ‖f.compLpL 2 μ u‖ + ‖g.compLpL 2 μ u‖ := by
  apply lp_norm_le_add
  filter_upwards [f.coeFn_compLpL u, g.coeFn_compLpL u] with x hf hg
  rw [hf, hg]
  exact h (u x)

variable (I : Type) [Fintype I] [DecidableEq I]

abbrev WaveSpace := ElectronicH1Space.L2 PhotonFock I
abbrev Reference := PhysicalFreeReferenceCore.FreeReference I
abbrev EnergyOutput := PiLp 2 (fun _ : I ⊕ Fin 2 => WaveSpace I)

local instance referenceNormedSpace : NormedSpace ℂ (Reference I) :=
  (PhysicalFreeReferenceCore.freeSubspace I).normedSpace

def inclusion : Reference I →L[ℂ] WaveSpace I := PhysicalFreeReferenceCore.inclusion I

def ordinary (i : I) : Reference I →L[ℂ] WaveSpace I :=
  (ElectronicH1Complex.derivative i).comp (PhysicalFreeReferenceCore.electronic I)

def radiation : Reference I →L[ℂ] WaveSpace I :=
  (radiationGraphDerivative.compLpL 2 volume).comp (PhysicalFreeReferenceCore.radiationSource I)

def energyOutput : Reference I →L[ℂ] EnergyOutput I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I ⊕ Fin 2 => WaveSpace I)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim (ordinary I)
      (fun n : Fin 2 => if n = 0 then inclusion I else radiation I)))

@[simp] theorem energyOutput_inl (u : Reference I) (i : I) :
    energyOutput I u (Sum.inl i) = ordinary I i u := rfl

@[simp] theorem energyOutput_mass (u : Reference I) :
    energyOutput I u (Sum.inr 0) = inclusion I u := by simp [energyOutput]

@[simp] theorem energyOutput_radiation (u : Reference I) :
    energyOutput I u (Sum.inr 1) = radiation I u := by simp [energyOutput]

def energy (u : Reference I) : ℝ :=
  ‖inclusion I u‖ ^ 2 + (∑ i, ‖ordinary I i u‖ ^ 2) + ‖radiation I u‖ ^ 2

theorem energyOutput_norm_sq (u : Reference I) : ‖energyOutput I u‖ ^ 2 = energy I u := by
  simpa only [energyOutput_inl, energyOutput_mass, energyOutput_radiation, energy] using
    norm_sq_sum_two (energyOutput I u)

theorem radiationSource_norm_le (u : Reference I) :
    ‖PhysicalFreeReferenceCore.radiationSource I u‖ ≤
      ‖inclusion I u‖ + ‖radiation I u‖ := by
  have h := lp_maps_norm_le volume radiationGraphInclusion radiationGraphDerivative
    (fun v => max_le (le_add_of_nonneg_right (norm_nonneg v.val.2))
      (le_add_of_nonneg_left (norm_nonneg v.val.1)))
    (PhysicalFreeReferenceCore.radiationSource I u)
  have hm := PhysicalFreeReferenceCore.value_matching I u
  exact h.trans_eq (congrArg (fun w : WaveSpace I => ‖w‖ + ‖radiation I u‖) hm.symm)

theorem reference_norm_le_energyOutput (u : Reference I) : ‖u‖ ≤ 2 * ‖energyOutput I u‖ := by
  have hv : ‖inclusion I u‖ ≤ ‖energyOutput I u‖ := by
    simpa only [energyOutput_mass] using PiLp.norm_apply_le (energyOutput I u) (Sum.inr 0)
  have hr : ‖radiation I u‖ ≤ ‖energyOutput I u‖ := by
    simpa only [energyOutput_radiation] using PiLp.norm_apply_le (energyOutput I u) (Sum.inr 1)
  have hd : ∀ i, ‖ordinary I i u‖ ≤ ‖energyOutput I u‖ := fun i =>
    PiLp.norm_apply_le (energyOutput I u) (Sum.inl i)
  have hH : ‖PhysicalFreeReferenceCore.electronic I u‖ ≤ ‖energyOutput I u‖ := by
    change max ‖inclusion I u‖ ‖fun i => ordinary I i u‖ ≤ _
    exact max_le hv ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hd)
  have hR := (radiationSource_norm_le I u).trans (add_le_add hv hr)
  change max ‖PhysicalFreeReferenceCore.electronic I u‖
    ‖PhysicalFreeReferenceCore.radiationSource I u‖ ≤ _
  apply max_le (hH.trans ?_) (by simpa only [two_mul] using hR)
  nlinarith [norm_nonneg (energyOutput I u)]

private theorem graphInclusion_injective : Function.Injective radiationGraphInclusion := by
  intro u v h
  have hz : (u - v).val.1 = 0 := sub_eq_zero.mpr h
  have ho := radiationRoot.graph_fst_eq_zero_snd (u - v).property hz
  apply Subtype.ext
  exact Prod.ext h (sub_eq_zero.mp ho)

theorem inclusion_injective : Function.Injective (inclusion I) := by
  intro u v h
  have he : PhysicalFreeReferenceCore.electronic I u = PhysicalFreeReferenceCore.electronic I v :=
    ElectronicH1Complex.value_injective h
  have hr : PhysicalFreeReferenceCore.radiationSource I u =
      PhysicalFreeReferenceCore.radiationSource I v := by
    apply Lp.ext
    have hm := (PhysicalFreeReferenceCore.value_matching I u).symm.trans
      (h.trans (PhysicalFreeReferenceCore.value_matching I v))
    filter_upwards [radiationGraphInclusion.coeFn_compLpL
      (PhysicalFreeReferenceCore.radiationSource I u), radiationGraphInclusion.coeFn_compLpL
      (PhysicalFreeReferenceCore.radiationSource I v)] with x hu hv
    apply graphInclusion_injective
    have hx := congrArg (fun w : WaveSpace I => w x) hm
    exact hu.symm.trans (hx.trans hv)
  apply Subtype.ext
  exact Prod.ext he hr

def energyGraphMap : Reference I →L[ℂ] WaveSpace I × EnergyOutput I :=
  (inclusion I).prod (energyOutput I)

theorem energyGraph_closed : IsClosed (Set.range (energyGraphMap I)) := by
  apply closed_range_of_bound (E := Reference I) (F := WaveSpace I × EnergyOutput I)
    (energyGraphMap I) 2
  intro u
  exact (reference_norm_le_energyOutput I u).trans
    (mul_le_mul_of_nonneg_left (norm_snd_le (energyGraphMap I u)) (by norm_num))

def energyGraph : Submodule ℂ (WaveSpace I × EnergyOutput I) := (energyGraphMap I).range

private theorem energyGraph_fst_zero (z : WaveSpace I × EnergyOutput I)
    (hz : z ∈ energyGraph I) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  have hv : inclusion I u = 0 := (congrArg Prod.fst hu).trans hzero
  have hu0 : u = 0 := inclusion_injective I (hv.trans (map_zero _).symm)
  rw [hu0, map_zero] at hu
  exact (congrArg Prod.snd hu).symm

def energyOperator : WaveSpace I →ₗ.[ℂ] EnergyOutput I := (energyGraph I).toLinearPMap

theorem energyOperator_graph : (energyOperator I).graph = energyGraph I :=
  Submodule.toLinearPMap_graph_eq _ (energyGraph_fst_zero I)

theorem energyOperator_closed : (energyOperator I).IsClosed := by
  change IsClosed ((energyOperator I).graph : Set (WaveSpace I × EnergyOutput I))
  exact (congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
    IsClosed (G : Set (WaveSpace I × EnergyOutput I))) (energyOperator_graph I)).mpr
      (energyGraph_closed I)

theorem reference_mem_energyOperator (u : Reference I) :
    (inclusion I u, energyOutput I u) ∈ (energyOperator I).graph := by
  exact (congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
    (inclusion I u, energyOutput I u) ∈ G) (energyOperator_graph I)).mpr ⟨u, rfl⟩

theorem energyOperator_domain (v : WaveSpace I) :
    v ∈ (energyOperator I).domain ↔ ∃ u : Reference I, inclusion I u = v := by
  have hD : ((energyOperator I).graph : Set (WaveSpace I × EnergyOutput I)) =
      Set.range (energyGraphMap I) :=
    congrArg (fun G : Submodule ℂ (WaveSpace I × EnergyOutput I) =>
      (G : Set (WaveSpace I × EnergyOutput I))) (energyOperator_graph I)
  exact domain_iff_of_graph_range (Q := Reference I) (H := WaveSpace I) (K := EnergyOutput I)
    (energyGraphMap I) (energyOperator I) hD v

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def normalEnergy : RemovalState.PositiveForm (B.traceData (H := WaveSpace I)) :=
  PhysicalClosedForms.positiveForm
    (S.resolve (WaveSpace I) (EnergyOutput I) (energyOperator I) (energyOperator_closed I))
    B.normal (B.realization (WaveSpace I)).functional

theorem normalEnergy_rankOne (u : Reference I) :
    (normalEnergy I B S).expectation ((B.realization (WaveSpace I)).rank.rankOne (inclusion I u)) =
      ENNReal.ofReal (energy I u) := by
  exact (PhysicalClosedForms.positiveForm_graph _ _ _ _ _ (reference_mem_energyOperator I u)).trans
    (congrArg ENNReal.ofReal (energyOutput_norm_sq I u))

theorem normalEnergy_finite_iff (v : WaveSpace I) :
    (normalEnergy I B S).expectation ((B.realization (WaveSpace I)).rank.rankOne v) < ⊤ ↔
      ∃ u : Reference I, inclusion I u = v := by
  exact (PhysicalClosedForms.positiveForm_finite_iff _ _ _ v).trans (energyOperator_domain I v)

end GptLean.PhysicalFreeForm
