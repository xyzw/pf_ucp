import GptLean.ElectronicH1Complex
import GptLean.PhysicalClosedForms
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
The ordinary kinetic form on an actual Hilbert-valued electronic L2
space. The closed operator consists of all weak coordinate derivatives.
Its form domain is exactly the constructed electronic H1 graph.
-/

noncomputable section

namespace GptLean.PhysicalKineticForm

open MeasureTheory PhysicalClosedForms PhysicalNormalTrace
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

variable (H I : Type) [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]

abbrev WaveSpace := ElectronicH1Space.L2 H I
abbrev Reference := ElectronicH1Complex.ComplexH1 H I
abbrev EnergyOutput := PiLp 2 (fun _ : I => WaveSpace H I)

local instance referenceNormedSpace : NormedSpace ℂ (Reference H I) :=
  (ElectronicH1Complex.complexWeakGraph H I).normedSpace

def inclusion : Reference H I →L[ℂ] WaveSpace H I := ElectronicH1Complex.value

def energyOutput : Reference H I →L[ℂ] EnergyOutput H I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => WaveSpace H I)).symm.toContinuousLinearMap.comp
    ElectronicH1Complex.gradient

@[simp] theorem energyOutput_apply (u : Reference H I) (i : I) :
    energyOutput H I u i = ElectronicH1Complex.derivative i u := rfl

def energy (u : Reference H I) : ℝ :=
  ∑ i, ‖ElectronicH1Complex.derivative i u‖ ^ 2

theorem energy_nonneg (u : Reference H I) : 0 ≤ energy H I u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energyOutput_norm_sq (u : Reference H I) :
    ‖energyOutput H I u‖ ^ 2 = energy H I u := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

def energyGraphMap : Reference H I →L[ℂ] WaveSpace H I × EnergyOutput H I :=
  (inclusion H I).prod (energyOutput H I)

theorem reference_norm_le_energyGraph (u : Reference H I) :
    ‖u‖ ≤ ‖energyGraphMap H I u‖ := by
  have hv : ‖inclusion H I u‖ ≤ ‖energyGraphMap H I u‖ :=
    norm_fst_le (inclusion H I u, energyOutput H I u)
  have hd : ∀ i, ‖ElectronicH1Complex.derivative i u‖ ≤ ‖energyGraphMap H I u‖ := by
    intro i
    exact (PiLp.norm_apply_le (energyOutput H I u) i).trans (norm_snd_le (inclusion H I u, energyOutput H I u))
  change max ‖inclusion H I u‖ ‖fun i => ElectronicH1Complex.derivative i u‖ ≤ _
  exact max_le hv ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hd)

theorem energyGraph_closed : IsClosed (Set.range (energyGraphMap H I)) := by
  have hanti : AntilipschitzWith 1 (energyGraphMap H I) := by
    apply (energyGraphMap H I).antilipschitz_of_bound
      (E := Reference H I) (F := WaveSpace H I × EnergyOutput H I) (K := 1)
    intro u
    simpa only [NNReal.coe_one, one_mul] using reference_norm_le_energyGraph H I u
  exact hanti.isClosed_range (energyGraphMap H I).uniformContinuous

def energyGraph : Submodule ℂ (WaveSpace H I × EnergyOutput H I) :=
  (energyGraphMap H I).range

private theorem energyGraph_fst_zero (z : WaveSpace H I × EnergyOutput H I)
    (hz : z ∈ energyGraph H I) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  have hv : inclusion H I u = 0 := (congrArg Prod.fst hu).trans hzero
  have hu0 : u = 0 := ElectronicH1Complex.value_injective (hv.trans (map_zero _).symm)
  rw [hu0, map_zero] at hu
  exact (congrArg Prod.snd hu).symm

def energyOperator : WaveSpace H I →ₗ.[ℂ] EnergyOutput H I :=
  (energyGraph H I).toLinearPMap

theorem energyOperator_graph : (energyOperator H I).graph = energyGraph H I :=
  Submodule.toLinearPMap_graph_eq _ (energyGraph_fst_zero H I)

theorem energyOperator_closed : (energyOperator H I).IsClosed := by
  change IsClosed ((energyOperator H I).graph : Set (WaveSpace H I × EnergyOutput H I))
  rw [energyOperator_graph]
  exact energyGraph_closed H I

theorem reference_mem_energyOperator (u : Reference H I) :
    (inclusion H I u, energyOutput H I u) ∈ (energyOperator H I).graph := by
  rw [energyOperator_graph]
  exact ⟨u, rfl⟩

theorem energyOperator_domain (v : WaveSpace H I) :
    v ∈ (energyOperator H I).domain ↔ ∃ u : Reference H I, inclusion H I u = v := by
  rw [LinearPMap.mem_domain_iff, energyOperator_graph]
  constructor
  · rintro ⟨w, u, hu⟩
    exact ⟨u, congrArg Prod.fst hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨energyOutput H I u, u, rfl⟩

variable (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)

def normalEnergy : RemovalState.PositiveForm (B.traceData (H := WaveSpace H I)) :=
  PhysicalClosedForms.positiveForm
    (S.resolve (WaveSpace H I) (EnergyOutput H I) (energyOperator H I) (energyOperator_closed H I))
    B.normal (B.realization (WaveSpace H I)).functional

theorem normalEnergy_rankOne (u : Reference H I) :
    (normalEnergy H I B S).expectation
      ((B.realization (WaveSpace H I)).rank.rankOne (inclusion H I u)) =
        ENNReal.ofReal (energy H I u) := by
  rw [← energyOutput_norm_sq H I u]
  exact PhysicalClosedForms.positiveForm_graph _ _ _ _ _ (reference_mem_energyOperator H I u)

theorem normalEnergy_finite_iff (v : WaveSpace H I) :
    (normalEnergy H I B S).expectation ((B.realization (WaveSpace H I)).rank.rankOne v) < ⊤ ↔
      ∃ u : Reference H I, inclusion H I u = v :=
  (PhysicalClosedForms.positiveForm_finite_iff _ _ _ v).trans (energyOperator_domain H I v)

end GptLean.PhysicalKineticForm
