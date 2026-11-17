import PfHk.PhysicalElectronicShift
import PfHk.CenteredPhysicalReference
import PfHk.PhysicalComparisonDomain
import PfHk.PhysicalCarlemanInput

/-! The arbitrary electronic shift specializes to the actual centered
Pauli–Fierz field profile. The photon vector is unchanged. -/

noncomputable section
namespace PfHk.PhysicalElectronicShift

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPolarization GptLean.Representability GptLean.SymmetricLift PfHk.PhysicalFieldRegularity
  PfHk.CenteredPhysicalReference PfHk.PhysicalOperatorDomain PfHk.PhysicalCutoffCommutator
  GptLean.TransformationsTranslation PfHk.PhysicalCarlemanInput

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (O : Configuration N)

theorem centered_profile_shift (j : Fin N × Fin 3) (X : Configuration N) :
    profile F χ O j X = profile F χ 0 j (X + O) := by
  unfold profile
  rw [zero_add, add_comm X O]

attribute [local irreducible] PhysicalPFReference.referenceSubspace
  PhysicalPFReference.inclusion PhysicalPFReference.covariant PhysicalPFReference.ordinary
  PhysicalPFReference.radiation PhysicalPFReference.potential shiftReference

theorem centered_covariant_shift_ae (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) (j : Fin N × Fin 3) :
    covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e j (shiftReference O u) =ᵐ[volume]
      fun X => covariant (Fin N × Fin 3) (fun _ => 0) C (profile F χ 0)
        (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e j u (X + O) :=
  (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ⇑z)
    (covariant_shift O C (profile F χ 0) (profile F χ O)
      (profile_measurable F χ 0) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ 0) (profile_bound F χ O)
      (fun j => ae_of_all _ (centered_profile_shift F χ O j)) e u j))).trans
        (shiftL2_ae O _)

theorem centered_radiation_shift_ae (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    radiation (Fin N × Fin 3) (fun _ => 0) (shiftReference O u) =ᵐ[volume]
      fun X => radiation (Fin N × Fin 3) (fun _ => 0) u (X + O) :=
  (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ⇑z)
    (radiation_shift O u))).trans (shiftL2_ae O _)

theorem centered_annularSupport {u : Reference (Fin N × Fin 3) (fun _ => 0)} {R : ℝ}
    (h : AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) u) O R) :
    AnnularSupport (inclusion (Fin N × Fin 3) (fun _ => 0) (shiftReference O u)) 0 R := by
  rcases h with ⟨ρ, R', hρ, hρR, hR, hs⟩
  refine ⟨ρ, R', hρ, hρR, hR, ?_⟩
  filter_upwards [inclusion_shift_ae O u, ae_shift O hs] with X hX hz hdist
  apply hX.trans
  apply hz
  simpa only [dist_zero_right, dist_eq_norm, add_sub_cancel_right, sub_zero] using hdist

theorem freeGraph_centered (C : CanonicalSectorCCR photonMeasure) (e : ℝ)
    {u : Reference (Fin N × Fin 3) (fun _ => 0)} {f : WaveSpace (Fin N × Fin 3)}
    (hu : FreeGraph C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e u f) :
    FreeGraph C (profile F χ O) (profile_measurable F χ O)
      (profileBound F χ) (profile_bound F χ O) e (shiftReference O u)
        (GptLean.TransformationsTranslation.shiftL2 O f) := by
  apply (freeGraph_iff C (profile F χ O) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ O) e _ _).mpr
  apply (isOperatorPair_zero_iff (fun _ => 0) C (profile F χ O)
    (profile_measurable F χ O) (profileBound F χ) (profile_bound F χ O) e _ _).mp
  apply operatorPair_shift O C (profile F χ 0) (profile F χ O)
    (profile_measurable F χ 0) (profile_measurable F χ O)
    (profileBound F χ) (profile_bound F χ 0) (profile_bound F χ O)
    (fun j => ae_of_all _ (centered_profile_shift F χ O j)) e
  exact (isOperatorPair_zero_iff (fun _ => 0) C (profile F χ 0)
    (profile_measurable F χ 0) (profileBound F χ) (profile_bound F χ 0) e _ _).mpr
    ((freeGraph_iff C (profile F χ 0) (profile_measurable F χ 0)
      (profileBound F χ) (profile_bound F χ 0) e _ _).mp hu)

end PfHk.PhysicalElectronicShift
