import GptLean.PhysicalFermionicScalarSeed
import GptLean.PhysicalCoulombReferenceCore
import GptLean.PhysicalFockCreationWords
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
The compact scalar alternant tensored with the actual photon vacuum
gives a nonzero vector in the fermionic common Coulomb reference domain.
The radiation graph and the electronic character are proved for this
vector before normalization or use of any normal trace realization.
-/

noncomputable section

namespace GptLean.PhysicalFermionicSeed

open MeasureTheory Filter Topology PhysicalFock ElectronicH1Complex SymmetricLift
open scoped ENNReal ContDiff

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

def vacuum : PhotonFock := creationWord photonMeasure []

theorem vacuum_norm : ‖vacuum‖ = 1 := PhysicalFock.vacuum_norm photonMeasure

theorem vacuum_ne_zero : vacuum ≠ 0 := by
  intro h
  have hh := vacuum_norm
  rw [h, norm_zero] at hh
  exact zero_ne_one hh

theorem vacuum_radiation_graph : (vacuum, 0) ∈ radiationRoot.graph := by
  apply (radiationRoot_graph_iff _ _).mpr
  intro n
  by_cases hn : n = 0
  · subst n
    filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure 0)] with k hk
    change (0 : FullSector photonMeasure 0) k = _
    simp [sectorDispersion]
  · have hu : vacuum n = 0 := lp.single_apply_ne 2 0 (vacuumSector photonMeasure) hn
    filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure n)] with k hk
    change (0 : FullSector photonMeasure n) k = _
    rw [hu]
    change (0 : FullSector photonMeasure n) k = _ * (0 : FullSector photonMeasure n) k
    rw [hk, Pi.zero_apply, mul_zero]

def vacuumGraph : RadiationGraphSpace := ⟨(vacuum, 0), vacuum_radiation_graph⟩

@[simp] theorem vacuumGraph_value : radiationGraphInclusion vacuumGraph = vacuum := rfl

theorem scalar_vacuum_number (a : ℝ) : photonNumberForm photonMeasure (a • vacuum) = 0 := by
  change (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * ‖(a • vacuum) n‖ ^ 2)) = 0
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have hu : vacuum (n + 1) = 0 :=
      lp.single_apply_ne 2 0 (vacuumSector photonMeasure) (Nat.succ_ne_zero n)
    change ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * ‖a • vacuum (n + 1)‖ ^ 2) = 0
    simp [hu]

variable (N : ℕ)

def graphFunction (x : Configuration N) : RadiationGraphSpace :=
  PhysicalFermionicScalarSeed.scalar N x • vacuumGraph

theorem graphFunction_smooth : ContDiff ℝ ∞ (graphFunction N) :=
  (PhysicalFermionicScalarSeed.scalar_smooth N).smul contDiff_const

theorem graphFunction_compact : HasCompactSupport (graphFunction N) :=
  (PhysicalFermionicScalarSeed.scalar_compact N).smul_right

def graphH1 : ComplexH1 RadiationGraphSpace (Fin N × Fin 3) :=
  let u := ElectronicH1Space.ofSmoothCompact (graphFunction N)
    (graphFunction_smooth N) (graphFunction_compact N)
  ⟨u.val, u.property⟩

theorem graphH1_value_ae :
    (value (graphH1 N) : Configuration N → RadiationGraphSpace) =ᵐ[volume] graphFunction N :=
  ((graphFunction_smooth N).continuous.memLp_of_hasCompactSupport
    (graphFunction_compact N)).coeFn_toLp

def freeReference : PhysicalFreeReferenceCore.FreeReference (Fin N × Fin 3) :=
  PhysicalFreeReferenceCore.fromGraphH1 (Fin N × Fin 3) (graphH1 N)

def wave : PhysicalElectronicFermions.FullSpace N PhotonFock :=
  PhysicalFreeReferenceCore.inclusion (Fin N × Fin 3) (freeReference N)

theorem wave_ae : (wave N : Configuration N → PhotonFock) =ᵐ[volume]
    fun x => PhysicalFermionicScalarSeed.scalar N x • vacuum := by
  have hp := radiationGraphInclusion.coeFn_compLpL (value (graphH1 N))
  filter_upwards [hp, graphH1_value_ae N] with x hx hf
  change (radiationGraphInclusion.compLpL 2 volume (value (graphH1 N))) x = _
  rw [hx, hf]
  exact (radiationGraphInclusion.restrictScalars ℝ).map_smul
    (PhysicalFermionicScalarSeed.scalar N x) vacuumGraph

theorem wave_ne_zero : wave N ≠ 0 := by
  intro h
  have ha : (fun x => PhysicalFermionicScalarSeed.scalar N x • vacuum) =ᵐ[volume]
      (0 : Configuration N → PhotonFock) := by
    have hw := wave_ae N
    rw [h] at hw
    exact hw.symm.trans (Lp.coeFn_zero PhotonFock 2 volume)
  have he := Measure.eq_of_ae_eq ha
    ((PhysicalFermionicScalarSeed.scalar_smooth N).continuous.smul continuous_const)
    continuous_const
  have hz := congrFun he (PhysicalFermionicScalarSeed.seedPoint N)
  exact (smul_ne_zero (PhysicalFermionicScalarSeed.scalar_seedPoint_ne_zero N)
    vacuum_ne_zero) hz

theorem wave_character : Repair.HasElectronicCharacter
    (fun π => permuteConfiguration π) (PhysicalElectronicFermions.signCharacter N) (wave N) := by
  intro π
  have hp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp (wave_ae N)
  filter_upwards [hp, wave_ae N] with x hx hy
  simp only [Function.comp_apply] at hx
  rw [hx, hy, PhysicalFermionicScalarSeed.scalar_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
  · simp [PhysicalElectronicFermions.signCharacter, hs]
  · simp [PhysicalElectronicFermions.signCharacter, hs]

theorem wave_projection : PhysicalElectronicFermions.projection N PhotonFock (wave N) = wave N :=
  (PhysicalElectronicFermions.projection_eq_self_iff N PhotonFock _).mpr (wave_character N)

def reference (c : ℝ) (hc : 0 ≤ c) : PhysicalCoulombReferenceCore.Reference N c :=
  PhysicalCoulombReferenceCore.attach N c hc (freeReference N)

@[simp] theorem reference_value (c : ℝ) (hc : 0 ≤ c) :
    PhysicalPFReference.inclusion (Fin N × Fin 3)
      (fun x => c * PhysicalCoulombH1.potential N x) (reference N c hc) = wave N := rfl

theorem reference_value_ne_zero (c : ℝ) (hc : 0 ≤ c) :
    PhysicalPFReference.inclusion (Fin N × Fin 3)
      (fun x => c * PhysicalCoulombH1.potential N x) (reference N c hc) ≠ 0 := wave_ne_zero N

end GptLean.PhysicalFermionicSeed
