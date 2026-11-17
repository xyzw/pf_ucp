import GptLean.PhysicalFockSectors
import GptLean.PhysicalSourceCoordinates

/-!
Actual measure-preserving sector coordinates separate photon momentum
from polarization and collect the Cartesian momenta into configuration
space. Finite product measures are regrouped directly, including the
zero-photon sector.
-/

noncomputable section

namespace GptLean.PhysicalSectorMeasures

open MeasureTheory PhysicalFock
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

theorem curry_symm_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry I J X).symm
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  refine ⟨(MeasurableEquiv.curry I J X).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry I J X).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have hp : (MeasurableEquiv.curry I J X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, MeasurableEquiv.coe_curry_symm, Set.mem_pi,
      Set.mem_univ, forall_true_left, Prod.forall, Function.uncurry_apply_pair]
  rw [hp, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type fun p : I × J => μ (s p)).symm

abbrev Polarization (m : ℕ) := Fin m → Fin 2
abbrev Configuration (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin 3)

def momentumEquiv (m : ℕ) : (Fin m → Gaussian.FieldSpace) ≃ᵐ Configuration m :=
  ((MeasurableEquiv.piCongrRight fun _ : Fin m =>
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
      (MeasurableEquiv.curry (Fin m) (Fin 3) ℝ).symm).trans
        (MeasurableEquiv.toLp 2 ((Fin m × Fin 3) → ℝ))

@[simp] theorem momentumEquiv_apply (m : ℕ) (k : Fin m → Gaussian.FieldSpace)
    (p : Fin m × Fin 3) : momentumEquiv m k p = k p.1 p.2 := rfl

theorem momentum_measurePreserving (m : ℕ) :
    MeasurePreserving (momentumEquiv m)
      (Measure.pi fun _ : Fin m => (volume : Measure Gaussian.FieldSpace)) volume :=
  (PiLp.volume_preserving_toLp (Fin m × Fin 3)).comp
    ((curry_symm_measurePreserving (I := Fin m) (J := Fin 3) volume).comp
      (measurePreserving_pi (fun _ => volume) (fun _ => volume)
        (fun _ : Fin m => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))))

theorem polarization_measure (m : ℕ) :
    (Measure.pi fun _ : Fin m => (Measure.count : Measure (Fin 2))) =
      (Measure.count : Measure (Polarization m)) := by
  apply Measure.ext_of_singleton
  intro s
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

def modeEquiv (m : ℕ) : (Fin m → PhotonMode) ≃ᵐ Configuration m × Polarization m :=
  (MeasurableEquiv.arrowProdEquivProdArrow Gaussian.FieldSpace (Fin 2) (Fin m)).trans
    ((momentumEquiv m).prodCongr (MeasurableEquiv.refl _))

@[simp] theorem modeEquiv_momentum (m : ℕ) (k : Fin m → PhotonMode) (p : Fin m × Fin 3) :
    (modeEquiv m k).1 p = (k p.1).1 p.2 := rfl

@[simp] theorem modeEquiv_polarization (m : ℕ) (k : Fin m → PhotonMode) (i : Fin m) :
    (modeEquiv m k).2 i = (k i).2 := rfl

theorem mode_measurePreserving (m : ℕ) :
    MeasurePreserving (modeEquiv m) (SectorMeasure photonMeasure m)
      ((volume : Measure (Configuration m)).prod Measure.count) := by
  have hp := measurePreserving_arrowProdEquivProdArrow Gaussian.FieldSpace (Fin 2) (Fin m)
    (fun _ => volume) (fun _ => Measure.count)
  rw [polarization_measure] at hp
  exact ((momentum_measurePreserving m).prod (MeasurePreserving.id Measure.count)).comp hp

def configurationIndex (N m : ℕ) :
    ((Fin N × Fin 3) ⊕ (Fin m × Fin 3)) ≃ (Fin (N + m) × Fin 3) :=
  (Equiv.sumProdDistrib (Fin N) (Fin m) (Fin 3)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin 3)))

def configurationSplit (N m : ℕ) : Configuration (N + m) ≃L[ℝ]
    Configuration N × Configuration m :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (configurationIndex N m).symm).toContinuousLinearEquiv.trans
    EuclideanSpace.sumEquivProd

theorem configurationSplit_measurePreserving (N m : ℕ) :
    MeasurePreserving (configurationSplit N m) volume
      ((volume : Measure (Configuration N)).prod (volume : Measure (Configuration m))) := by
  let S := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2
    (fun _ : (Fin N × Fin 3) ⊕ (Fin m × Fin 3) => ℝ)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (configurationIndex N m).symm
  change MeasurePreserving (fun x => WithLp.ofLp (S (U x))) volume volume
  exact (WithLp.volume_preserving_ofLp (Configuration N) (Configuration m)).comp
    (S.measurePreserving.comp U.measurePreserving)

end GptLean.PhysicalSectorMeasures
