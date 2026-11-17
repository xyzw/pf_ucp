import PfHk.PhysicalCenteredShift
import PfHk.PhysicalAnnularGraphTransfer
import PfHk.CarlemanTranslation

/-! Translation of the actual full-domain free Carleman densities back
to the original field profile and an arbitrary electronic center. -/

noncomputable section
namespace PfHk.PhysicalFreeCarleman

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift
  GptLean.TransformationsTranslation PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference PfHk.PhysicalElectronicShift
  PfHk.PhysicalAnnularGraphTransfer PfHk.CarlemanSpatialDensity

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000
attribute [local irreducible] PhysicalPFReference.inclusion PhysicalPFReference.covariant
  PhysicalPFReference.radiation PhysicalPFReference.referenceSubspace shiftReference

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (e : ℝ) (O : Configuration N)

/-- The physical density for the original free operator, centered at `O`. -/
def centeredOperatorDensity (τ α : ℝ) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Configuration N → ℝ :=
  centeredDensity O τ α (fun X => ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)
    (fun X => ∑ j, ‖covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e j u X‖ ^ 2)
    (fun X => ‖PhysicalPFReference.radiation (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2)

private theorem density_congr_at {I : Type*} [Fintype I] [DecidableEq I]
    (τ α : ℝ) (M D Q M' D' Q' : PfHk.PolarCalculus.Position I → ℝ)
    (X : PfHk.PolarCalculus.Position I) (hM : M X = M' X) (hD : D X = D' X)
    (hQ : Q X = Q' X) : density τ α M D Q X = density τ α M' D' Q' X := by
  unfold density
  rw [hM, hD, hQ]

private theorem norm_density_translate_ae {I : Type*} [Fintype I] [DecidableEq I]
    {H : Type*} [NormedAddCommGroup H] (O : PfHk.PolarCalculus.Position I) (τ α : ℝ)
    (m m' q q' : PfHk.PolarCalculus.Position I → H)
    (d d' : I → PfHk.PolarCalculus.Position I → H)
    (hm : m =ᵐ[volume] fun X => m' (X + O))
    (hd : ∀ j, d j =ᵐ[volume] fun X => d' j (X + O))
    (hq : q =ᵐ[volume] fun X => q' (X + O)) :
    density τ α (fun X => ‖m X‖ ^ 2) (fun X => ∑ j, ‖d j X‖ ^ 2)
      (fun X => ‖q X‖ ^ 2) =ᵐ[volume]
      fun X => centeredDensity O τ α (fun Y => ‖m' Y‖ ^ 2)
        (fun Y => ∑ j, ‖d' j Y‖ ^ 2) (fun Y => ‖q' Y‖ ^ 2) (O + X) := by
  filter_upwards [hm, Filter.eventually_all.mpr hd, hq] with X hM hD hQ
  simp only [add_comm X O] at hM hD hQ
  rw [centeredDensity_add]
  exact density_congr_at τ α _ _ _ _ _ _ X
    (congrArg (fun v : H => ‖v‖ ^ 2) hM)
    (Finset.sum_congr rfl fun j _ => congrArg (fun v : H => ‖v‖ ^ 2) (hD j))
    (congrArg (fun v : H => ‖v‖ ^ 2) hQ)

private theorem norm_source_translate_ae {I : Type*} [Fintype I] [DecidableEq I]
    {H : Type*} [NormedAddCommGroup H] (O : PfHk.PolarCalculus.Position I) (τ α : ℝ)
    (f g : PfHk.PolarCalculus.Position I → H)
    (h : f =ᵐ[volume] fun X => g (X + O)) :
    source τ α (fun X => ‖f X‖ ^ 2) =ᵐ[volume]
      fun X => centeredSource O τ α (fun Y => ‖g Y‖ ^ 2) (O + X) := by
  filter_upwards [h] with X hX
  simp only [add_comm X O] at hX
  rw [centeredSource_add]
  unfold source
  dsimp only
  rw [hX]

attribute [local irreducible] operatorDensity centeredOperatorDensity source centeredSource

theorem shifted_operatorDensity_ae (τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    operatorDensity F χ O C e τ α (shiftReference O u) =ᵐ[volume]
      fun X => centeredOperatorDensity F χ C e O τ α u (O + X) := by
  unfold operatorDensity centeredOperatorDensity
  exact norm_density_translate_ae (I := Fin N × Fin 3) (H := PhotonFock) O τ α
    (inclusion (Fin N × Fin 3) (fun _ => 0) (shiftReference O u))
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (radiation (Fin N × Fin 3) (fun _ => 0) (shiftReference O u))
    (radiation (Fin N × Fin 3) (fun _ => 0) u)
    (fun j => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O)
      (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e j
        (shiftReference O u))
    (fun j => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
      (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e j u)
    (inclusion_shift_ae O u) (centered_covariant_shift_ae F χ O C e u)
    (centered_radiation_shift_ae O u)

theorem shifted_operatorDensity_integral (R τ α : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    (∫ X in Metric.ball 0 R, operatorDensity F χ O C e τ α (shiftReference O u) X) =
      ∫ X in Metric.ball O R, centeredOperatorDensity F χ C e O τ α u X :=
  (integral_congr_ae (ae_restrict_of_ae
    (shifted_operatorDensity_ae F χ C e O τ α u))).trans
      (integral_ball_add_left O R _)

theorem shifted_source_ae (τ α : ℝ) (f : WaveSpace (Fin N × Fin 3)) :
    source (I := Fin N × Fin 3) τ α
      (fun X => ‖shiftL2 (I := Fin N × Fin 3) (F := PhotonFock) O f X‖ ^ 2) =ᵐ[volume]
      fun X => centeredSource O τ α (fun Y : Configuration N => ‖f Y‖ ^ 2) (O + X) :=
  norm_source_translate_ae (I := Fin N × Fin 3) (H := PhotonFock) O τ α
    (shiftL2 (I := Fin N × Fin 3) (F := PhotonFock) O f) f (shiftL2_ae O f)

theorem shifted_source_integral (R τ α : ℝ) (f : WaveSpace (Fin N × Fin 3)) :
    (∫ X in Metric.ball 0 R, source τ α (fun Y => ‖shiftL2 O f Y‖ ^ 2) X) =
      ∫ X in Metric.ball O R, centeredSource O τ α (fun Y => ‖f Y‖ ^ 2) X :=
  (integral_congr_ae (ae_restrict_of_ae (shifted_source_ae O τ α f))).trans
    (integral_ball_add_left O R _)

end PfHk.PhysicalFreeCarleman
