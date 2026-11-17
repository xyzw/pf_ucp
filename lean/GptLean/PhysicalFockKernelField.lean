import GptLean.PhysicalFockCCR
import GptLean.PhysicalFockKernelLinearity

/-!
Continuous dependence of the actual graph-domain field on its kernel.

A weighted kernel contains its L² representative and its inverse-frequency
representative, related by the actual momentum multiplier. The field is
real-linear and continuous in this pair. In particular continuous spatial
kernel profiles give continuous operator-valued fields on the radiation
graph, without a separate measurability premise for the field operator.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

def weightedKernelSubspace : Submodule ℂ
    (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure) where
  carrier := {k | ∀ᵐ p ∂photonMeasure, k.1 p = (Real.sqrt ‖p.1‖ : ℂ) * k.2 p}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 photonMeasure] with p hp
    change (0 : Lp ℂ 2 photonMeasure) p =
      (Real.sqrt ‖p.1‖ : ℂ) * (0 : Lp ℂ 2 photonMeasure) p
    simp only [hp, Pi.zero_apply, mul_zero]
  add_mem' := by
    rintro k l hk hl
    filter_upwards [hk, hl, Lp.coeFn_add k.1 l.1, Lp.coeFn_add k.2 l.2] with p hk hl ha hb
    change (k.1 + l.1) p = (Real.sqrt ‖p.1‖ : ℂ) * (k.2 + l.2) p
    rw [ha, hb, Pi.add_apply, Pi.add_apply, hk, hl, mul_add]
  smul_mem' := by
    rintro c k hk
    filter_upwards [hk, Lp.coeFn_smul c k.1, Lp.coeFn_smul c k.2] with p hk ha hb
    change (c • k.1) p = (Real.sqrt ‖p.1‖ : ℂ) * (c • k.2) p
    rw [ha, hb, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hk]
    ring

abbrev WeightedPhotonKernel := ↥weightedKernelSubspace

def kernelAnnihilation (k : WeightedPhotonKernel) : RadiationGraphSpace →L[ℂ] PhotonFock :=
  annihilationRadiation k.val.1 k.val.2 k.property

def kernelCreation (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel) :
    RadiationGraphSpace →L[ℂ] PhotonFock :=
  creationRadiation C k.val.1 k.val.2 k.property

def kernelField (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel) :
    RadiationGraphSpace →L[ℂ] PhotonFock := kernelAnnihilation k + kernelCreation C k

theorem kernelAnnihilation_add (k l : WeightedPhotonKernel) :
    kernelAnnihilation (k + l) = kernelAnnihilation k + kernelAnnihilation l := by
  apply ContinuousLinearMap.ext
  intro q
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (k.val.1 + l.val.1)
    (radiationGraphInclusion q (n + 1)) = _
  rw [annihilationSector_add]
  rfl

theorem kernelAnnihilation_real_smul (c : ℝ) (k : WeightedPhotonKernel) :
    kernelAnnihilation (c • k) = c • kernelAnnihilation k := by
  apply ContinuousLinearMap.ext
  intro q
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n ((c : ℂ) • k.val.1)
    (radiationGraphInclusion q (n + 1)) = (c : ℂ) •
      annihilationSector photonMeasure n k.val.1 (radiationGraphInclusion q (n + 1))
  rw [annihilationSector_smul, Complex.conj_ofReal]
  rfl

theorem kernelCreation_add (C : CanonicalSectorCCR photonMeasure) (k l : WeightedPhotonKernel) :
    kernelCreation C (k + l) = kernelCreation C k + kernelCreation C l := by
  apply ContinuousLinearMap.ext
  intro q
  apply lp.ext
  funext n
  cases n with
  | zero => exact (zero_add _).symm
  | succ n =>
    change creationSector photonMeasure n (k.val.1 + l.val.1)
      (radiationGraphInclusion q n) = _
    rw [creationSector_add]
    rfl

theorem kernelCreation_real_smul (C : CanonicalSectorCCR photonMeasure) (c : ℝ)
    (k : WeightedPhotonKernel) : kernelCreation C (c • k) = c • kernelCreation C k := by
  apply ContinuousLinearMap.ext
  intro q
  apply lp.ext
  funext n
  cases n with
  | zero => exact (smul_zero c).symm
  | succ n =>
    change creationSector photonMeasure n ((c : ℂ) • k.val.1)
      (radiationGraphInclusion q n) = (c : ℂ) •
        creationSector photonMeasure n k.val.1 (radiationGraphInclusion q n)
    rw [creationSector_smul]
    rfl

theorem kernelField_norm_le (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    ‖kernelField C k q‖ ≤ 2 * ‖k.val.2‖ * ‖radiationGraphDerivative q‖ +
      ‖k.val.1‖ * ‖radiationGraphInclusion q‖ := by
  have ha := annihilationRadiation_norm_le k.val.1 k.val.2 k.property q
  have hc := creationGraphOutput_norm_le C k.val.1 k.val.2 k.property q
  have ht := norm_add_le (kernelAnnihilation k q) (kernelCreation C k q)
  change ‖kernelField C k q‖ ≤ _ at ht
  change ‖kernelAnnihilation k q‖ ≤ _ at ha
  change ‖kernelCreation C k q‖ ≤ _ at hc
  linarith

theorem kernelField_opNorm_le (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel) :
    ‖kernelField C k‖ ≤ (2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) * ‖k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  calc
    _ ≤ 2 * ‖k.val.2‖ * ‖radiationGraphDerivative q‖ +
        ‖k.val.1‖ * ‖radiationGraphInclusion q‖ := kernelField_norm_le C k q
    _ ≤ 2 * ‖k‖ * (‖radiationGraphDerivative‖ * ‖q‖) +
        ‖k‖ * (‖radiationGraphInclusion‖ * ‖q‖) := by
      gcongr
      · exact norm_snd_le k.val
      · exact radiationGraphDerivative.le_opNorm q
      · exact norm_fst_le k.val
      · exact radiationGraphInclusion.le_opNorm q
    _ = _ := by ring

/-- Real-linearity is the correct scalar structure for the Segal field. -/
def kernelFieldMap (C : CanonicalSectorCCR photonMeasure) :
    WeightedPhotonKernel →L[ℝ] (RadiationGraphSpace →L[ℂ] PhotonFock) :=
  LinearMap.mkContinuous
    { toFun := kernelField C
      map_add' k l := by
        simp only [kernelField, kernelAnnihilation_add, kernelCreation_add]
        abel
      map_smul' c k := by
        simp only [kernelField, kernelAnnihilation_real_smul, kernelCreation_real_smul,
          smul_add, RingHom.id_apply] }
    (2 * ‖radiationGraphDerivative‖ + ‖radiationGraphInclusion‖) (kernelField_opNorm_le C)

theorem kernelField_continuous (C : CanonicalSectorCCR photonMeasure) :
    Continuous (kernelField C) := (kernelFieldMap C).continuous

end GptLean.PhysicalFock
