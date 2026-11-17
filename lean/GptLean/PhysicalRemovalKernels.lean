import GptLean.PhysicalSoftDerivativeKernel
import GptLean.PhysicalFockPhysicalProfiles

/-!
The original particle kernels and their sharp hard and soft parts. Every
profile and bound comes from the same article polarization and cutoff.
-/

noncomputable section
namespace GptLean.PhysicalRemovalKernels

open MeasureTheory Gaussian PhysicalFock PhysicalPolarization SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

variable (F : Frame) (χ : ArticleCutoff) (N : ℕ)

def full : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel :=
  PhysicalProfiles.particleKernel (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _) N

def bound : ℝ :=
  PhysicalProfiles.kernelBound (formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)

theorem full_measurable (i : Fin N × Fin 3) : AEStronglyMeasurable (full F χ N i) volume :=
  PhysicalProfiles.particleKernel_measurable (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) N i

theorem full_bound (i : Fin N × Fin 3) : ∀ᵐ x ∂volume, ‖full F χ N i x‖ ≤ bound F χ :=
  PhysicalProfiles.particleKernel_bound (formFactors F χ) rfl
    (LinearIsometryEquiv.refl ℝ _) N i

variable (κ : ℝ)

def hard (i : Fin N × Fin 3) (x : Configuration N) : WeightedPhotonKernel :=
  WeightedPhotonKernel.hard κ (full F χ N i x)

def soft (i : Fin N × Fin 3) (x : Configuration N) : WeightedPhotonKernel :=
  WeightedPhotonKernel.soft κ (full F χ N i x)

theorem hard_measurable (i : Fin N × Fin 3) : AEStronglyMeasurable (hard F χ N κ i) volume :=
  (WeightedPhotonKernel.hard κ).continuous.comp_aestronglyMeasurable (full_measurable F χ N i)

theorem soft_measurable (i : Fin N × Fin 3) : AEStronglyMeasurable (soft F χ N κ i) volume :=
  (WeightedPhotonKernel.soft κ).continuous.comp_aestronglyMeasurable (full_measurable F χ N i)

theorem hard_bound (i : Fin N × Fin 3) : ∀ᵐ x ∂volume, ‖hard F χ N κ i x‖ ≤ bound F χ := by
  filter_upwards [full_bound F χ N i] with x hx
  exact (WeightedPhotonKernel.hard_norm_le κ _).trans hx

theorem soft_bound (i : Fin N × Fin 3) : ∀ᵐ x ∂volume, ‖soft F χ N κ i x‖ ≤ bound F χ := by
  filter_upwards [full_bound F χ N i] with x hx
  exact (WeightedPhotonKernel.soft_norm_le κ _).trans hx

theorem hard_mem (i : Fin N × Fin 3) (x : Configuration N) :
    (hard F χ N κ i x).val.1 ∈ hardOnePhoton κ :=
  WeightedPhotonKernel.hard_fst_mem κ _

theorem soft_mem (i : Fin N × Fin 3) (x : Configuration N) :
    (soft F χ N κ i x).val.1 ∈ softOnePhoton κ :=
  WeightedPhotonKernel.soft_fst_mem κ _

theorem full_eq_hard_add_soft (i : Fin N × Fin 3) (x : Configuration N) :
    full F χ N i x = hard F χ N κ i x + soft F χ N κ i x :=
  (WeightedPhotonKernel.hard_add_soft κ _).symm

theorem soft_eq_label (hκ : 0 ≤ κ) (i : Fin N × Fin 3) (x : Configuration N) :
    soft F χ N κ i x = derivativeKernel F χ hκ i.2 [] (particle x i.1) :=
  (derivativeKernel_nil F χ hκ i.2 (particle x i.1)).symm

end GptLean.PhysicalRemovalKernels
