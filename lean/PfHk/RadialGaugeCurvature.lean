import PfHk.RadialGauge
import PfHk.PhysicalFieldRegularityDerivative
import GptLean.SymmetricLift.MetricGeometry
import GptLean.PhysicalWeightedKernelSplit

/-!
The actual Pauli–Fierz curvature labels and their radial integral. All
curvature norms are uniform in the electronic configuration. The angular
variation is derived from the interval FTC, with the exact factor `-r²`.
-/

noncomputable section
namespace PfHk.RadialGauge

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.PhysicalNonattainmentFluxKernel GptLean.SymmetricLift
  GptLean.Representability Gaussian PfHk.PhysicalFieldRegularity
open scoped ENNReal InnerProductSpace Interval

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (hUV : CarlemanUV χ) (e : ℝ)

/-- The actual directional derivative of the electronic coupling label. -/
def couplingDerivative (j : Fin N × Fin 3) (v X : Configuration N) : WeightedPhotonKernel :=
  (-e) • directionKernel F χ hUV j.2 (particle v j.1) (particle X j.1)

theorem couplingDerivative_continuous (j : Fin N × Fin 3) (v : Configuration N) :
    Continuous (couplingDerivative F χ hUV e j v) := by
  unfold couplingDerivative
  exact (continuous_const : Continuous (fun _ : Configuration N => (-e : ℝ))).smul
    ((directionKernel_continuous F χ hUV j.2 (particle v j.1)).comp
      (particleLinear j.1).continuous_of_finiteDimensional)

theorem couplingKernel_hasLineDerivAt (j : Fin N × Fin 3) (v X : Configuration N) :
    HasLineDerivAt ℝ (couplingKernel F χ e j) (couplingDerivative F χ hUV e j v X) X v := by
  have h := (physicalKernel_hasLineDerivAt F χ hUV j.2 (particle v j.1) (particle X j.1)).const_smul (-e)
  convert! h using 1

/-- `F(X)[v,w] = ∂_v A(X)[w] - ∂_w A(X)[v]`. -/
def curvature (X v w : Configuration N) : WeightedPhotonKernel :=
  (∑ j : Fin N × Fin 3, w j • couplingDerivative F χ hUV e j v X) -
    ∑ j : Fin N × Fin 3, v j • couplingDerivative F χ hUV e j w X

@[simp] theorem curvature_self (X v : Configuration N) : curvature F χ hUV e X v v = 0 :=
  sub_self _

theorem curvature_swap (X v w : Configuration N) :
    curvature F χ hUV e X v w = -curvature F χ hUV e X w v := by
  unfold curvature
  abel

theorem curvature_continuous (v w : Configuration N) :
    Continuous (fun X => curvature F χ hUV e X v w) := by
  unfold curvature
  apply Continuous.sub
  · apply continuous_finsetSum
    intro j _
    exact (continuous_const : Continuous (fun _ : Configuration N => w j)).smul
      (couplingDerivative_continuous F χ hUV e j v)
  · apply continuous_finsetSum
    intro j _
    exact (continuous_const : Continuous (fun _ : Configuration N => v j)).smul
      (couplingDerivative_continuous F χ hUV e j w)

def momentBound : ℝ :=
  PhysicalProfiles.kernelBound (omegaFactors F χ hUV) rfl (LinearIsometryEquiv.refl ℝ _)

theorem momentBound_nonneg : 0 ≤ momentBound F χ hUV :=
  (norm_nonneg (omegaKernel F χ hUV 0 0)).trans (omegaKernel_uniform_bound F χ hUV 0 0)

theorem couplingDerivative_norm_le (j : Fin N × Fin 3) (v X : Configuration N) :
    ‖couplingDerivative F χ hUV e j v X‖ ≤ |e| * ‖v‖ * momentBound F χ hUV := by
  rw [couplingDerivative, norm_smul, Real.norm_eq_abs, abs_neg]
  have h := directionKernel_uniform_bound F χ hUV j.2 (particle v j.1) (particle X j.1)
  calc
    _ ≤ |e| * (‖particle v j.1‖ * momentBound F χ hUV) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (particle_norm_le v j.1) (abs_nonneg _))
        (momentBound_nonneg F χ hUV)

/-- One constant controls the physical curvature in every position and
every pair of directions. -/
theorem curvature_norm_le (X v w : Configuration N) :
    ‖curvature F χ hUV e X v w‖ ≤
      (2 * Fintype.card (Fin N × Fin 3) * |e| * momentBound F χ hUV) * ‖v‖ * ‖w‖ := by
  have h (v w : Configuration N) :
      ‖∑ j : Fin N × Fin 3, w j • couplingDerivative F χ hUV e j v X‖ ≤
        (Fintype.card (Fin N × Fin 3) : ℝ) * (‖w‖ * (|e| * ‖v‖ * momentBound F χ hUV)) := by
    calc
      _ ≤ ∑ j : Fin N × Fin 3, ‖w j • couplingDerivative F χ hUV e j v X‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N × Fin 3, ‖w‖ * (|e| * ‖v‖ * momentBound F χ hUV) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le w j)
          (couplingDerivative_norm_le F χ hUV e j v X) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  exact (norm_sub_le _ _).trans ((add_le_add (h v w) (h w v)).trans_eq (by ring))

/-- The radial curvature formula for the angular connection label. -/
def angularLabel (θ ζ : Configuration N) (r : ℝ) : WeightedPhotonKernel :=
  ∫ s in (0 : ℝ)..r, s • curvature F χ hUV e (s • θ) θ ζ

theorem angularIntegrand_continuous (θ ζ : Configuration N) :
    Continuous (fun s : ℝ => s • curvature F χ hUV e (s • θ) θ ζ) :=
  (continuous_id : Continuous (fun s : ℝ => s)).smul
    ((curvature_continuous F χ hUV e θ ζ).comp (continuous_id.smul continuous_const))

@[simp] theorem angularLabel_radial (θ : Configuration N) (r : ℝ) :
    angularLabel F χ hUV e θ θ r = 0 := by
  simp [angularLabel]

/-- The exact derivative of the physical angular curvature integral. -/
theorem angularLabel_radial_hasDerivAt (θ ζ : Configuration N) (r : ℝ) :
    HasDerivAt (angularLabel F χ hUV e θ ζ)
      (r • curvature F χ hUV e (r • θ) θ ζ) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((angularIntegrand_continuous F χ hUV e θ ζ).intervalIntegrable 0 r)
    (angularIntegrand_continuous F χ hUV e θ ζ).stronglyMeasurable.stronglyMeasurableAtFilter
    (angularIntegrand_continuous F χ hUV e θ ζ).continuousAt

/-- This is the `-r² F(θ,ζ)` variation in the Carleman cylinder. -/
theorem angularLabel_logarithmic_hasDerivAt (θ ζ : Configuration N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => angularLabel F χ hUV e θ ζ (Real.exp (-s)))
      (-(Real.exp (-t) ^ 2) • curvature F χ hUV e (Real.exp (-t) • θ) θ ζ) t := by
  have ht : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  convert! (angularLabel_radial_hasDerivAt F χ hUV e θ ζ (Real.exp (-t))).scomp t ht using 1
  simp only [smul_smul, neg_mul, pow_two]

/-- Evaluation of the field map on a fixed radiation-domain vector. -/
def fieldEvaluation (C : CanonicalSectorCCR photonMeasure) (q : RadiationGraphSpace) :
    WeightedPhotonKernel →L[ℝ] PhotonFock where
  toFun k := kernelField C k q
  map_add' k l := by
    change kernelFieldMap C (k + l) q = _
    rw [map_add]
    rfl
  map_smul' c k := by
    change kernelFieldMap C (c • k) q = _
    rw [map_smul]
    rfl
  cont := (kernelFieldMap C).continuous.clm_apply continuous_const

/-- The exact label derivative gives the same operator derivative on the
fixed radiation graph domain. -/
theorem angularField_logarithmic_hasDerivAt (C : CanonicalSectorCCR photonMeasure)
    (θ ζ : Configuration N) (q : RadiationGraphSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kernelField C (angularLabel F χ hUV e θ ζ (Real.exp (-s))) q)
      (kernelField C (-(Real.exp (-t) ^ 2) •
        curvature F χ hUV e (Real.exp (-t) • θ) θ ζ) q) t :=
  (fieldEvaluation C q).hasFDerivAt.comp_hasDerivAt t
    (angularLabel_logarithmic_hasDerivAt F χ hUV e θ ζ t)



theorem sum_fixed {ι : Type*} [Fintype ι] (k : ι → WeightedPhotonKernel)
    (hk : ∀ j, F.conjugation (k j).val.1 = (k j).val.1) :
    F.conjugation (∑ j, k j).val.1 = (∑ j, k j).val.1 := by
  have h : component false (∑ j, k j) ∈ F.realStructure.fixedSpace := by
    rw [map_sum]
    exact Submodule.sum_mem _ (fun j _ => (F.realStructure.mem_fixedSpace _).mpr (hk j))
  exact (F.realStructure.mem_fixedSpace _).mp h

theorem couplingDerivative_fixed (j : Fin N × Fin 3) (v X : Configuration N) :
    F.conjugation (couplingDerivative F χ hUV e j v X).val.1 =
      (couplingDerivative F χ hUV e j v X).val.1 :=
  real_smul_fixed F (-e) _ (directionKernel_fixed F χ hUV j.2 (particle v j.1) (particle X j.1))

theorem curvature_fixed (X v w : Configuration N) :
    F.conjugation (curvature F χ hUV e X v w).val.1 =
      (curvature F χ hUV e X v w).val.1 := by
  have h (v w : Configuration N) := sum_fixed F
    (fun j : Fin N × Fin 3 => w j • couplingDerivative F χ hUV e j v X)
    (fun j => real_smul_fixed F _ _ (couplingDerivative_fixed F χ hUV e j v X))
  change F.realStructure.realCLM (_ - _) = _ - _
  rw [map_sub]
  exact congrArg₂ (fun a b : Lp ℂ 2 photonMeasure => a - b) (h v w) (h w v)

theorem curvature_label_inner_im (X Y v w : Configuration N) :
    (⟪(label F χ e X).val.1, (curvature F χ hUV e Y v w).val.1⟫_ℂ).im = 0 :=
  realStructure_fixed_inner_im photonMeasure F.realStructure
    ⟨_, (F.realStructure.mem_fixedSpace _).mpr (label_fixed F χ e X)⟩
    ⟨_, (F.realStructure.mem_fixedSpace _).mpr (curvature_fixed F χ hUV e Y v w)⟩

/-- Strong commutation between the radial gauge and the physical curvature. -/
theorem unitary_curvature_groups_commute (W : ConcreteWeylLaw photonMeasure)
    (X Y v w : Configuration N) (s : ℝ) (u : PhotonFock) :
    unitary F χ e W X
      (W.weyl ((Complex.I * (s : ℂ)) • (curvature F χ hUV e Y v w).val.1) u) =
    W.weyl ((Complex.I * (s : ℂ)) • (curvature F χ hUV e Y v w).val.1)
      (unitary F χ e W X u) := by
  simpa only [unitary, Complex.ofReal_one, mul_one] using
    W.field_groups_commute photonMeasure _ _ (curvature_label_inner_im F χ hUV e X Y v w) s 1 u

/-- The standard creation-annihilation bounds, with an explicit quadratic
constant, on the actual radiation graph. -/
theorem fieldEvaluation_sq_le (C : CanonicalSectorCCR photonMeasure)
    (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    ‖kernelField C k q‖ ^ 2 ≤ 5 * ‖k‖ ^ 2 *
      (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2) := by
  have h := (kernelField_norm_le C k q).trans
    (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_snd_le k.val)
        (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (norm_fst_le k.val) (norm_nonneg _)))
  change ‖kernelField C k q‖ ≤ 2 * ‖k‖ * ‖radiationGraphDerivative q‖ +
    ‖k‖ * ‖radiationGraphInclusion q‖ at h
  have h' : ‖kernelField C k q‖ ≤ ‖k‖ *
      (2 * ‖radiationGraphDerivative q‖ + ‖radiationGraphInclusion q‖) := h.trans_eq (by ring)
  calc
    _ ≤ (‖k‖ * (2 * ‖radiationGraphDerivative q‖ + ‖radiationGraphInclusion q‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = ‖k‖ ^ 2 * (2 * ‖radiationGraphDerivative q‖ + ‖radiationGraphInclusion q‖) ^ 2 := mul_pow _ _ _
    _ ≤ ‖k‖ ^ 2 * (5 * (‖radiationGraphDerivative q‖ ^ 2 + ‖radiationGraphInclusion q‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith [sq_nonneg (‖radiationGraphDerivative q‖ - 2 * ‖radiationGraphInclusion q‖)]
    _ = _ := by ring

end PfHk.RadialGauge
