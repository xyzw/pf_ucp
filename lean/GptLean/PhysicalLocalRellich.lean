import GptLean.PhysicalFockPositionSupport
import GptLean.PhysicalLocalFreeGraph
import GptLean.PhysicalSectorCoordinateIdentities
import GptLean.PhysicalRellichFourier
import GptLean.PhotonLocalizationRellichBound

/-!
Actual supported finite-sector coordinates for the local free graph.
The electronic and photon support predicates combine by L2 Fubini into
the bounded configuration regions of the universal Rellich theorem.
-/

noncomputable section
namespace GptLean.PhysicalLocalRellich

open MeasureTheory Filter Topology PhysicalFock PhysicalSectorCoordinates
  PhysicalFockPositionSupport PhysicalLocalSupport PhotonLocalization SymmetricLift
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000
set_option Elab.async false

theorem configurationRegion_measurable (N : ℕ) (r : ℝ) :
    MeasurableSet (electronicConfigurationRegion (N := N) r) := by
  rw [electronicConfigurationRegion, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hp : Continuous (fun x : Configuration N => particle x i) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_pi fun a => PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) (i, a))
  exact (isClosed_le hp.norm continuous_const).measurableSet

section Fubini
variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem uncurry_supported {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (w : Lp (Lp H 2 ν) 2 μ)
    (hw : ∀ᵐ x ∂μ, x ∉ s → w x = 0)
    (hv : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, y ∉ t → w x y = 0) :
    ∀ᵐ z ∂μ.prod ν, z ∉ s ×ˢ t → PhysicalSourceFubini.curryEquiv.symm w z = 0 := by
  let u : Lp H 2 (μ.prod ν) := PhysicalSourceFubini.curryEquiv.symm w
  have hrep := PhysicalSourceFubini.curryEquiv_represents_ae u
  have he : PhysicalSourceFubini.curryEquiv u = w :=
    LinearIsometryEquiv.apply_symm_apply _ _
  rw [he] at hrep
  have hmeas : MeasurableSet {z : X × Y | z ∉ s ×ˢ t → u z = 0} := by
    convert (hs.prod ht).union
      ((Lp.stronglyMeasurable u).measurableSet_eq_fun stronglyMeasurable_const) using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [hrep, hw, hv] with x hx hsx htx
  filter_upwards [hx, htx, Lp.coeFn_zero H 2 ν] with y hy ht₁ hz
  intro hout
  by_cases hxs : x ∈ s
  · have hyt : y ∉ t := fun hyt => hout ⟨hxs, hyt⟩
    exact hy.symm.trans (ht₁ hyt)
  · exact hy.symm.trans ((congrArg (fun v : Lp H 2 ν => v y) (hsx hxs)).trans hz)

end Fubini

theorem spatialSector_supported (N n L : ℕ) (r : ℝ)
    (u : PhysicalFreeForm.WaveSpace (Fin N × Fin 3))
    (hp : u ∈ photonSupport N r) (he : u ∈ electronicSupport N L) :
    ∀ᵐ x ∂volume, x ∉ sectorConfigurationRegion N n ((L : ℝ) + 1) r →
      spatialSectorPosition N n
        (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume n u) x = 0 := by
  let v := PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume n u
  let w := liftIsometry volume (sectorPosition n) v
  have hw : w =ᵐ[volume] fun x => sectorPosition n (u x n) := by
    filter_upwards [liftIsometry_ae volume (sectorPosition n) v,
      PhysicalFiniteSectorCoordinates.coordinate_ae (Sector photonMeasure) volume n u]
      with x hx hv
    exact hx.trans (congrArg (sectorPosition n) hv)
  have hwe : ∀ᵐ x ∂volume, x ∉ electronicConfigurationRegion ((L : ℝ) + 1) → w x = 0 := by
    filter_upwards [hw, he] with x hx he
    intro hout
    exact hx.trans ((congrArg (fun v : PhotonFock => sectorPosition n (v n)) (he hout)).trans
      ((sectorPosition n).map_zero))
  have hwp : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      y ∉ electronicConfigurationRegion (N := n) r → w x y = 0 := by
    filter_upwards [hw, hp] with x hx hp
    rw [hx]
    exact sectorPosition_supported r (u x) hp n
  have hprod := uncurry_supported (configurationRegion_measurable N ((L : ℝ) + 1))
    (configurationRegion_measurable n r) w hwe hwp
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (PhysicalSourceFubini.curryEquiv.symm w)
      (PhysicalSectorMeasures.configurationSplit_measurePreserving N n),
    (PhysicalSectorMeasures.configurationSplit_measurePreserving N n).quasiMeasurePreserving.ae hprod]
    with x hx hs
  intro hout
  apply hx.trans
  apply hs
  intro hin
  apply hout
  constructor
  · intro i
    have h := hin.1 i
    simpa only [configurationSplit_particle_fst] using h
  · intro j
    have h := hin.2 j
    simpa only [configurationSplit_particle_snd] using h

def sectors (N : ℕ) (r : ℝ) (L M : ℕ) :
    PhysicalLocalFreeGraph.Space N r L M →ₗᵢ[ℂ]
      PiLp 2 (fun m : Fin (M + 1) => PhotonSectorL2 N m.val (Coefficient m.val)) :=
  (finitePosition N M).comp (PhysicalLocalFreeGraph.finiteInclusion N r L M)

theorem sectors_supported (N : ℕ) (r : ℝ) (L M : ℕ)
    (u : PhysicalLocalFreeGraph.Space N r L M) (m : Fin (M + 1)) :
    ∀ᵐ x ∂volume, x ∉ sectorConfigurationRegion N m.val ((L : ℝ) + 1) r →
      sectors N r L M u m x = 0 :=
  spatialSector_supported N m.val L r (PhysicalLocalFreeGraph.embedding N r L M u)
    (PhysicalLocalFreeGraph.value_mem_support N r L M u).1.1
    (PhysicalLocalFreeGraph.value_mem_support N r L M u).1.2

/-- The supported graph uses the same finite-sector coordinates as the free form. -/
theorem sectors_inclusion (N : ℕ) (r : ℝ) (L M : ℕ)
    (u : PhysicalLocalFreeGraph.Domain N r L M) (m : Fin (M + 1)) :
    sectors N r L M (PhysicalLocalFreeGraph.inclusion N r L M u) m =
      spatialSectorPosition N m.val
        (PhysicalFiniteSectorCoordinates.coordinate (Sector photonMeasure) volume m.val
          (PhysicalFreeHilbert.inclusion (Fin N × Fin 3) u.val)) := rfl

end GptLean.PhysicalLocalRellich
