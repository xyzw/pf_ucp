import GptLean.PhysicalPFVacuumForm
import GptLean.PhysicalRemovalKernels
import GptLean.PhysicalSoftPhotonField

/-! The article kernels discharge every vacuum field input of the actual PF form identity. -/

noncomputable section

namespace GptLean.PhysicalRemovalVacuum

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization PhysicalNormalTrace
  PhysicalPFReference PhysicalRemovalKernels SymmetricLift
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] PhysicalPolarization.softPhotonHardRealNormedSpace

variable (F : Frame) (χ : ArticleCutoff) (N : ℕ)
  (V : Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (κ : ℝ) (hκ : 0 ≤ κ) (e : ℝ)
  (W : ScalarWienerSegal photonMeasure (softOnePhoton κ) (F.softRealStructure κ))

def vacuumField (i : Fin N × Fin 3) (x : Configuration N) : PhotonFock :=
  (photonWienerSegal F χ κ hκ BF C W).field ⟨i.2, [], particle x i.1⟩ photonVacuum

theorem vacuumField_inner (i : Fin N × Fin 3) (x : Configuration N) :
    inner ℂ photonVacuum (vacuumField F χ N C BF κ hκ W i x) = 0 :=
  photonVacuum_field_inner_zero F χ κ hκ BF C W ⟨i.2, [], particle x i.1⟩

theorem vacuumField_norm_sq (i : Fin N × Fin 3) (x : Configuration N) :
    ‖vacuumField F χ N C BF κ hκ W i x‖ ^ 2 = ‖(soft F χ N κ i x).val.1‖ ^ 2 := by
  rw [soft_eq_label F χ N κ hκ i x]
  exact (photonVacuum_field_norm_sq F χ κ hκ BF C W ⟨i.2, [], particle x i.1⟩).trans
    (derivativeKernel_fst_norm_sq F χ hκ i.2 [] (particle x i.1)).symm

/-- No vacuum form or field matching premise remains for the article profiles. -/
def articleVacuumFormData :=
  PhysicalPFVacuumForm.vacuumFormData (Fin N × Fin 3) V C
    (full F χ N) (hard F χ N κ) (soft F χ N κ)
    (full_measurable F χ N) (hard_measurable F χ N κ) (soft_measurable F χ N κ)
    (bound F χ) (bound F χ) (bound F χ)
    (full_bound F χ N) (hard_bound F χ N κ) (soft_bound F χ N κ)
    (fun i => ae_of_all _ (full_eq_hard_add_soft F χ N κ i)) B S BF κ e
    (fun i => ae_of_all _ (hard_mem F χ N κ i))
    (fun i => ae_of_all _ fun x => WeightedPhotonKernel.soft_fst_mem_hard_orthogonal κ
      (full F χ N i x))
    photonVacuum (vacuumField F χ N C BF κ hκ W) photonVacuum_norm
    (fun i => ae_of_all _ (vacuumField_inner F χ N C BF κ hκ W i))
    (fun i => ae_of_all _ (vacuumField_norm_sq F χ N C BF κ hκ W i))

end GptLean.PhysicalRemovalVacuum
