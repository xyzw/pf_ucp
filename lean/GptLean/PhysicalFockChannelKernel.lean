import GptLean.PhysicalFockChannelVacuum
import GptLean.PhysicalFockSpatialField

/-!
Continuous kernel dependence for the actual retained channel field and
its orthogonal vacuum correction. A channel kernel is an ordinary kernel
together with the weighted representative of its retained pullback.
The compatibility condition is a closed linear equality of actual maps.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true

variable (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
  WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))

def channelKernelSubspace : Submodule ℂ (Lp ℂ 2 photonMeasure × WeightedPhotonKernel) where
  carrier := {p | (retainedMap j).adjoint p.1 = p.2.val.1}
  zero_mem' := map_zero _
  add_mem' := by
    intro p q hp hq
    change (retainedMap j).adjoint (p.1 + q.1) = p.2.val.1 + q.2.val.1
    rw [map_add, hp, hq]
  smul_mem' := by
    intro c p hp
    change (retainedMap j).adjoint (c • p.1) = c • p.2.val.1
    rw [map_smul, hp]

abbrev ChannelKernel := ↥(channelKernelSubspace j)

variable (BF : StandardSymmetricFockExponential) (C : CanonicalSectorCCR photonMeasure)

def channelKernelAnnihilation (p : ChannelKernel j) :
    RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelAnnihilation BF C j p.val.1 p.val.2 p.property

def channelKernelCreation (p : ChannelKernel j) :
    RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelCreation BF C j p.val.1 p.val.2 p.property

def channelKernelField (p : ChannelKernel j) :
    RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelField BF C j p.val.1 p.val.2 p.property

def channelKernelVacuum (p : ChannelKernel j) :
    RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) :=
  channelVacuum BF C j p.val.1 p.val.2 p.property

theorem channelKernelAnnihilation_add (p q : ChannelKernel j) :
    channelKernelAnnihilation j BF C (p + q) =
      channelKernelAnnihilation j BF C p + channelKernelAnnihilation j BF C q := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext a
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (p.val.1 + q.val.1)
    ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1)) =
      annihilationSector photonMeasure n p.val.1
        ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1)) +
      annihilationSector photonMeasure n q.val.1
        ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1))
  exact congrArg (fun A : Sector photonMeasure (n + 1) →L[ℂ] Sector photonMeasure n =>
    A ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1)))
      (annihilationSector_add photonMeasure n p.val.1 q.val.1)

theorem channelKernelAnnihilation_real_smul (c : ℝ) (p : ChannelKernel j) :
    channelKernelAnnihilation j BF C (c • p) = c • channelKernelAnnihilation j BF C p := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext a
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n ((c : ℂ) • p.val.1)
    ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1)) =
      (c : ℂ) • annihilationSector photonMeasure n p.val.1
        ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1))
  simpa only [Complex.conj_ofReal, smul_apply] using
    congrArg (fun A : Sector photonMeasure (n + 1) →L[ℂ] Sector photonMeasure n =>
      A ((photonFactorization BF).factor j (radiationGraphInclusion u) a (n + 1)))
      (annihilationSector_smul photonMeasure n p.val.1 (c : ℂ))

theorem channelKernelCreation_add (p q : ChannelKernel j) :
    channelKernelCreation j BF C (p + q) =
      channelKernelCreation j BF C p + channelKernelCreation j BF C q := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext a
  apply lp.ext
  funext n
  cases n with
  | zero => exact (zero_add _).symm
  | succ n =>
    change creationSector photonMeasure n (p.val.1 + q.val.1)
      ((photonFactorization BF).factor j (radiationGraphInclusion u) a n) =
        creationSector photonMeasure n p.val.1 ((photonFactorization BF).factor j (radiationGraphInclusion u) a n) +
        creationSector photonMeasure n q.val.1 ((photonFactorization BF).factor j (radiationGraphInclusion u) a n)
    exact congrArg (fun A : Sector photonMeasure n →L[ℂ] Sector photonMeasure (n + 1) =>
      A ((photonFactorization BF).factor j (radiationGraphInclusion u) a n))
      (creationSector_add photonMeasure n p.val.1 q.val.1)

theorem channelKernelCreation_real_smul (c : ℝ) (p : ChannelKernel j) :
    channelKernelCreation j BF C (c • p) = c • channelKernelCreation j BF C p := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext a
  apply lp.ext
  funext n
  cases n with
  | zero => exact (smul_zero c).symm
  | succ n =>
    change creationSector photonMeasure n ((c : ℂ) • p.val.1)
      ((photonFactorization BF).factor j (radiationGraphInclusion u) a n) =
        (c : ℂ) • creationSector photonMeasure n p.val.1
          ((photonFactorization BF).factor j (radiationGraphInclusion u) a n)
    exact congrArg (fun A : Sector photonMeasure n →L[ℂ] Sector photonMeasure (n + 1) =>
      A ((photonFactorization BF).factor j (radiationGraphInclusion u) a n))
      (creationSector_smul photonMeasure n p.val.1 (c : ℂ))

theorem channelKernelField_opNorm_le (p : ChannelKernel j) :
    ‖channelKernelField j BF C p‖ ≤
      (2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hn : ‖p.val.2.val.2‖ ≤ ‖p‖ := (norm_snd_le p.val.2.val).trans (norm_snd_le p.val)
  calc
    _ ≤ 2 * ‖p.val.2.val.2‖ * ‖radiationGraphDerivative u‖ +
        ‖p.val.1‖ * ‖radiationGraphInclusion u‖ :=
      channelField_norm_le BF C j p.val.1 p.val.2 p.property u
    _ ≤ 2 * ‖p‖ * (‖radiationGraphDerivative‖ * ‖u‖) +
        ‖p‖ * (‖radiationGraphInclusion‖ * ‖u‖) := by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num))
          (radiationGraphDerivative.le_opNorm u) (norm_nonneg _) (by positivity))
        (mul_le_mul (norm_fst_le p.val) (radiationGraphInclusion.le_opNorm u)
          (norm_nonneg (radiationGraphInclusion u)) (norm_nonneg p))
    _ = _ := by ring

def channelKernelFieldMap : ChannelKernel j →L[ℝ]
    (RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock)) :=
  LinearMap.mkContinuous
    { toFun := channelKernelField j BF C
      map_add' p q := by
        change channelKernelAnnihilation j BF C (p + q) + channelKernelCreation j BF C (p + q) =
          (channelKernelAnnihilation j BF C p + channelKernelCreation j BF C p) +
          (channelKernelAnnihilation j BF C q + channelKernelCreation j BF C q)
        exact (congrArg₂ (fun A D : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) => A + D)
          (channelKernelAnnihilation_add j BF C p q) (channelKernelCreation_add j BF C p q)).trans
          (by abel)
      map_smul' c p := by
        change channelKernelAnnihilation j BF C (c • p) + channelKernelCreation j BF C (c • p) =
          c • (channelKernelAnnihilation j BF C p + channelKernelCreation j BF C p)
        exact (congrArg₂ (fun A D : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) => A + D)
          (channelKernelAnnihilation_real_smul j BF C c p)
          (channelKernelCreation_real_smul j BF C c p)).trans (smul_add c _ _).symm }
    (2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖)
    (channelKernelField_opNorm_le j BF C)

theorem channelKernelVacuum_norm_le (p : ChannelKernel j) (u : RadiationGraphSpace) :
    ‖channelKernelVacuum j BF C p u‖ ≤ ‖p.val.1‖ * ‖radiationGraphInclusion u‖ := by
  have he := channelVacuum_norm_sq BF C j p.val.1 p.val.2 p.property u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  change ‖channelVacuum BF C j p.val.1 p.val.2 p.property u‖ ^ 2 ≤ _
  nlinarith only [he, mul_nonneg (sq_nonneg ‖p.val.2.val.1‖)
    (sq_nonneg ‖radiationGraphInclusion u‖)]

theorem channelKernelVacuum_opNorm_le (p : ChannelKernel j) :
    ‖channelKernelVacuum j BF C p‖ ≤ ‖radiationGraphInclusion‖ * ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    _ ≤ ‖p.val.1‖ * ‖radiationGraphInclusion u‖ := channelKernelVacuum_norm_le j BF C p u
    _ ≤ ‖p‖ * (‖radiationGraphInclusion‖ * ‖u‖) := by
      gcongr
      · exact norm_fst_le p.val
      · exact radiationGraphInclusion.le_opNorm u
    _ = _ := by ring

def channelKernelVacuumMap : ChannelKernel j →L[ℝ]
    (RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock)) :=
  LinearMap.mkContinuous
    { toFun := channelKernelVacuum j BF C
      map_add' p q := by
        let U := ((photonFactorization BF).factor j).toContinuousLinearMap
        have hK : U.comp (kernelCreation C (p.val.2 + q.val.2)) =
            U.comp (kernelCreation C p.val.2) + U.comp (kernelCreation C q.val.2) :=
          (congrArg (fun A : RadiationGraphSpace →L[ℂ] PhotonFock => U.comp A)
            (kernelCreation_add C p.val.2 q.val.2)).trans (by
              apply ContinuousLinearMap.ext
              intro u
              exact map_add U _ _)
        change channelKernelCreation j BF C (p + q) -
          U.comp (kernelCreation C (p.val.2 + q.val.2)) =
          (channelKernelCreation j BF C p - U.comp (kernelCreation C p.val.2)) +
          (channelKernelCreation j BF C q - U.comp (kernelCreation C q.val.2))
        exact (congrArg₂ (fun A D : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) => A - D)
          (channelKernelCreation_add j BF C p q) hK).trans (by abel)
      map_smul' c p := by
        let U := ((photonFactorization BF).factor j).toContinuousLinearMap
        have hK : U.comp (kernelCreation C (c • p.val.2)) =
            c • U.comp (kernelCreation C p.val.2) :=
          (congrArg (fun A : RadiationGraphSpace →L[ℂ] PhotonFock => U.comp A)
            (kernelCreation_real_smul C c p.val.2)).trans (by
              apply ContinuousLinearMap.ext
              intro u
              exact U.map_smul_of_tower c _)
        change channelKernelCreation j BF C (c • p) -
          U.comp (kernelCreation C (c • p.val.2)) =
          c • (channelKernelCreation j BF C p - U.comp (kernelCreation C p.val.2))
        exact (congrArg₂ (fun A D : RadiationGraphSpace →L[ℂ] Space (fun _ : ℕ => PhotonFock) => A - D)
          (channelKernelCreation_real_smul j BF C c p) hK).trans
          (smul_sub c (channelKernelCreation j BF C p) (U.comp (kernelCreation C p.val.2))).symm }
    ‖radiationGraphInclusion‖ (channelKernelVacuum_opNorm_le j BF C)

end GptLean.PhysicalFock
