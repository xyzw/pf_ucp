import PfHk.RadialGaugeAngular
import PfHk.RadialGaugeRadiation
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Product rules for the genuine physical forms when their arguments
move. They follow from bounded bilinear calculus on the radiation graph,
and provide the product terms in the cylinder commutator. -/

noncomputable section
namespace PfHk.PhysicalFormProductRules

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalWeyl
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

local instance : InnerProductSpace ℝ PhotonFock := InnerProductSpace.rclikeToReal ℂ _
local instance : InnerProductSpace ℝ (lp (fun _ : ℕ => PhotonFock) 2) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] kernelField kernelFieldMap coefficientTensor radiationAnalysis
  radiationGraphInclusion radiationGraphDerivative

def fieldBilinear (C : CanonicalSectorCCR photonMeasure) :
    WeightedPhotonKernel →L[ℝ] RadiationGraphSpace →L[ℝ] PhotonFock :=
  (ContinuousLinearMap.restrictScalarsL ℂ RadiationGraphSpace PhotonFock ℝ ℝ).comp
    (kernelFieldMap C)

theorem fieldBilinear_apply (C : CanonicalSectorCCR photonMeasure)
    (a : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    fieldBilinear C a q = kernelField C a q := by
  unfold fieldBilinear kernelFieldMap
  rfl

theorem field_hasDerivAt (C : CanonicalSectorCCR photonMeasure)
    {a : ℝ → WeightedPhotonKernel} {q : ℝ → RadiationGraphSpace}
    {da : WeightedPhotonKernel} {dq : RadiationGraphSpace} {t : ℝ}
    (ha : HasDerivAt a da t) (hq : HasDerivAt q dq t) :
    HasDerivAt (fun s => kernelField C (a s) (q s))
      (kernelField C (a t) dq + kernelField C da (q t)) t := by
  convert! (fieldBilinear C).hasDerivAt_of_bilinear (fun _ => ha) (fun _ => hq) using 1 <;>
    simp only [fieldBilinear_apply]

theorem angularValue_hasDerivAt (C : CanonicalSectorCCR photonMeasure)
    {a : ℝ → WeightedPhotonKernel} {q : ℝ → RadiationGraphSpace} {v : ℝ → PhotonFock}
    {da : WeightedPhotonKernel} {dq : RadiationGraphSpace} {dv : PhotonFock} {t : ℝ}
    (ha : HasDerivAt a da t) (hq : HasDerivAt q dq t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => RadialGaugeAngular.angularValue C (a s) (q s) (v s))
      (RadialGaugeAngular.angularValue C (a t) dq dv + Complex.I • kernelField C da (q t)) t := by
  convert! hv.add ((field_hasDerivAt C ha hq).const_smul Complex.I) using 1 <;> first
    | rfl
    | simp only [RadialGaugeAngular.angularValue, smul_add, add_assoc, Pi.smul_apply]

theorem angular_energy_hasDerivAt {ι : Type*} [Fintype ι]
    (C : CanonicalSectorCCR photonMeasure)
    {a : ℝ → ι → WeightedPhotonKernel} {q : ℝ → RadiationGraphSpace}
    {v : ℝ → ι → PhotonFock} {da : ι → WeightedPhotonKernel}
    {dq : RadiationGraphSpace} {dv : ι → PhotonFock} {t : ℝ}
    (ha : ∀ j, HasDerivAt (fun s => a s j) (da j) t)
    (hq : HasDerivAt q dq t) (hv : ∀ j, HasDerivAt (fun s => v s j) (dv j) t) :
    HasDerivAt (fun s => RadialGaugeAngular.energy C (a s) (q s) (v s))
      (2 * (∑ j, inner ℝ (RadialGaugeAngular.angularValue C (a t j) (q t) (v t j))
        (RadialGaugeAngular.angularValue C (a t j) dq (dv j))) +
          RadialGaugeAngular.formDerivative C (a t) da (q t) (v t)) t := by
  have hd (j : ι) := (angularValue_hasDerivAt C (ha j) hq (hv j)).norm_sq
  have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert! hs using 1 <;> first
    | rfl
    | (funext s; simp only [RadialGaugeAngular.energy, Finset.sum_apply])
    | simp only [inner_add_right, Finset.sum_add_distrib, mul_add,
        ← Finset.mul_sum, RadialGaugeAngular.formDerivative]

theorem displacedAnalysis_hasDerivAt {y : ℝ → Lp ℂ 2 photonMeasure}
    {q : ℝ → RadiationGraphSpace} {dy : Lp ℂ 2 photonMeasure}
    {dq : RadiationGraphSpace} {t : ℝ} (hy : HasDerivAt y dy t) (hq : HasDerivAt q dq t) :
    HasDerivAt (fun s => RadialGaugeRadiation.displacedAnalysis (y s) (q s))
      (RadialGaugeRadiation.displacedAnalysis (y t) dq +
        coefficientTensor dy (radiationGraphInclusion (q t))) t := by
  have hi := (radiationGraphInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hq
  have ha := (radiationAnalysis.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hq
  let hb := (coefficientTensor (H := PhotonFock)).bilinearRestrictScalars ℝ
  have hc := hb.hasDerivAt_of_bilinear (fun _ => hy) (fun _ => hi)
  convert! ha.add hc using 1 <;> first
    | rfl
    | (simp only [RadialGaugeRadiation.displacedAnalysis, add_assoc]; rfl)

theorem radiation_energy_hasDerivAt {y : ℝ → Lp ℂ 2 photonMeasure}
    {q : ℝ → RadiationGraphSpace} {dy : Lp ℂ 2 photonMeasure}
    {dq : RadiationGraphSpace} {t : ℝ} (hy : HasDerivAt y dy t) (hq : HasDerivAt q dq t) :
    HasDerivAt (fun s => RadialGaugeRadiation.energy (y s) (q s))
      (4 * inner ℝ (RadialGaugeRadiation.displacedAnalysis (y t) (q t))
        (RadialGaugeRadiation.displacedAnalysis (y t) dq) +
          RadialGaugeRadiation.formDerivative (y t) dy (q t)) t := by
  have h := ((displacedAnalysis_hasDerivAt hy hq).norm_sq).const_mul 2
  convert! h using 1 <;> first
    | rfl
    | (simp only [RadialGaugeRadiation.formDerivative, inner_add_right]; ring)

end PfHk.PhysicalFormProductRules
