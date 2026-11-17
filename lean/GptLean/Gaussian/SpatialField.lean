import GptLean.Gaussian.FieldMoments
import GptLean.Gaussian.JointRepresentatives
import GptLean.Repair.ParameterSections
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Spatial Fourier kernels and their joint Gaussian representatives. This
module builds jointly measurable versions from the standard continuous
real-linear first-chaos map. No joint measurability of the Gaussian field
is a hypothesis. Identification of a pathwise spatial derivative requires
the weak-derivative and Sobolev passage separately.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

theorem continuous_derivativeFactor (ds : List (Fin 3)) :
    Continuous (derivativeFactor ds) := by
  induction ds with
  | nil => simp only [derivativeFactor]; fun_prop
  | cons j ds ih =>
      simp only [derivativeFactor]
      fun_prop

theorem continuous_fieldPhase :
    Continuous (fun z : FieldSpace × FieldSpace => fieldPhase z.1 z.2) := by
  unfold fieldPhase
  fun_prop

/-- The spatial phase has its expected directional derivative. -/
theorem fieldPhase_hasDerivAt (p x v : FieldSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fieldPhase p (x + s • v))
      ((-Complex.I * (inner ℝ p v : ℂ)) * fieldPhase p (x + t • v)) t := by
  have hlin : HasDerivAt (fun t : ℝ => -(inner ℝ p x + t * inner ℝ p v))
      (-inner ℝ p v) t := by
    convert! (((hasDerivAt_id t).mul_const (inner ℝ p v)).const_add (inner ℝ p x)).neg
      using 1
    simp only [one_mul]
  have h := (hlin.ofReal_comp.mul_const Complex.I).cexp
  convert! h using 1
  · ext t
    simp [fieldPhase, inner_add_right, inner_smul_right]
  · simp only [Complex.ofReal_neg, fieldPhase, inner_add_right, inner_smul_right]
    ring

theorem fieldPhase_hasLineDerivAt (p x v : FieldSpace) :
    HasLineDerivAt ℝ (fieldPhase p)
      ((-Complex.I * (inner ℝ p v : ℂ)) * fieldPhase p x) x v := by
  unfold HasLineDerivAt
  simpa only [zero_smul, add_zero] using fieldPhase_hasDerivAt p x v 0

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The symbols called derivative kernels are actual coordinate derivatives,
including every higher ordered derivative and every momentum point. -/
theorem softDerivativeKernel_hasDerivAt
    (momentum : Ω → FieldSpace) (ds : List (Fin 3)) (j : Fin 3)
    (k : ℝ) (x : FieldSpace) (g : Ω → ℂ) (y : Ω) (t : ℝ) :
    HasDerivAt (fun s : ℝ => softDerivativeKernel momentum ds k
      (x + s • EuclideanSpace.single j 1) g y)
      (softDerivativeKernel momentum (j :: ds) k
        (x + t • EuclideanSpace.single j 1) g y) t := by
  have hphase := fieldPhase_hasDerivAt (momentum y) x (EuclideanSpace.single j 1) t
  have h := (hphase.const_mul (derivativeFactor ds (momentum y))).mul_const
    (softBase momentum k g y)
  have hi : inner ℝ (momentum y) (EuclideanSpace.single j 1) = momentum y j := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [hi] at h
  convert! h using 1
  change ((-Complex.I * (momentum y j : ℂ)) * derivativeFactor ds (momentum y)) *
    fieldPhase (momentum y) (x + t • EuclideanSpace.single j 1) * softBase momentum k g y =
      derivativeFactor ds (momentum y) *
        ((-Complex.I * (momentum y j : ℂ)) *
          fieldPhase (momentum y) (x + t • EuclideanSpace.single j 1)) * softBase momentum k g y
  ring

theorem softDerivativeKernel_hasLineDerivAt
    (momentum : Ω → FieldSpace) (ds : List (Fin 3)) (j : Fin 3)
    (k : ℝ) (x : FieldSpace) (g : Ω → ℂ) (y : Ω) :
    HasLineDerivAt ℝ (fun z => softDerivativeKernel momentum ds k z g y)
      (softDerivativeKernel momentum (j :: ds) k x g y)
      x (EuclideanSpace.single j 1) := by
  unfold HasLineDerivAt
  simpa only [zero_smul, add_zero] using
    softDerivativeKernel_hasDerivAt momentum ds j k x g y 0

theorem measurable_softBase (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (k : ℝ) (g : Ω → ℂ) (hg : Measurable g) :
    Measurable (softBase momentum k g) := by
  unfold softBase
  exact Measurable.ite (hm.norm measurableSet_Iio) hg measurable_const

/-- Joint measurability is proved for the actual Fourier derivative kernel. -/
theorem measurable_softDerivativeKernel (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (ds : List (Fin 3)) (k : ℝ)
    (g : Ω → ℂ) (hg : Measurable g) :
    Measurable (fun z : FieldSpace × Ω =>
      softDerivativeKernel momentum ds k z.1 g z.2) := by
  unfold softDerivativeKernel
  exact (((continuous_derivativeFactor ds).measurable.comp (hm.comp measurable_snd)).mul
    (continuous_fieldPhase.measurable.comp
      ((hm.comp measurable_snd).prodMk measurable_fst))).mul
        ((measurable_softBase momentum hm k g hg).comp measurable_snd)

/-- Every spatial derivative kernel belongs to the actual one-photon L²
space, directly from the ultraviolet cutoff assumption. -/
theorem softDerivativeKernel_memLp (momentum : Ω → FieldSpace)
    (hm : Measurable momentum) (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k)
    (x : FieldSpace) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    MemLp (softDerivativeKernel momentum ds k x g) 2 ν := by
  have hmeas : Measurable (softDerivativeKernel momentum ds k x g) :=
    (measurable_softDerivativeKernel momentum hm ds k g hg).comp
      ((measurable_const (a := x)).prodMk measurable_id)
  apply (memLp_two_iff_integrable_sq_norm hmeas.stronglyMeasurable.aestronglyMeasurable).mpr
  have hi := softBase_weighted_integrable momentum hm k g (fun _ => 1)
    (by simpa using hbase)
  have h := softDerivativeKernel_moment (ν := ν) momentum ds hk x g (fun _ => 1)
    (fun _ => zero_le_one) hi (by simpa only [one_mul] using
      (hmeas.norm.pow_const 2).aestronglyMeasurable)
  simpa only [one_mul] using h.1

/-- The L²-valued Fourier family is built from its explicit representative. -/
def softKernelL2 (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ)
    (hg : Measurable g) (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν)
    (x : FieldSpace) : Lp ℂ 2 ν :=
  (softDerivativeKernel_memLp momentum hm ds hk x g hg hbase).toLp
    (softDerivativeKernel momentum ds k x g)

theorem stronglyMeasurable_softKernelL2 [SFinite ν] [IsSeparable ν]
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    (ds : List (Fin 3)) {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ)
    (hg : Measurable g) (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    StronglyMeasurable (softKernelL2 momentum hm ds hk g hg hbase) := by
  apply GptLean.Repair.stronglyMeasurable_toL2_sections
  exact (measurable_softDerivativeKernel momentum hm ds k g hg).stronglyMeasurable

/-- A single jointly measurable Gaussian representative is constructed for
every derivative order. `T` is the standard continuous real-linear first
chaos map, extended from the commuting real subspace if necessary. Its
identification with the WIS coordinate at each label is a separate standard
intertwining fact. -/
theorem exists_joint_soft_field_representatives
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q} [SFinite ν] [IsSeparable ν]
    (T : Lp ℂ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (momentum : Ω → FieldSpace) (hm : Measurable momentum)
    {k : ℝ} (hk : 0 ≤ k) (g : Ω → ℂ) (hg : Measurable g)
    (hbase : Integrable (fun y => ‖g y‖ ^ 2) ν) :
    ∃ field : List (Fin 3) → FieldSpace → Q → ℝ,
      (∀ ds, Measurable (Function.uncurry (field ds))) ∧
      ∀ ds x, field ds x =ᵐ[μ]
        (T (softKernelL2 momentum hm ds hk g hg hbase x) : Q → ℝ) := by
  have h (ds : List (Fin 3)) := exists_jointly_measurable_L2_representative
    (fun x => T (softKernelL2 momentum hm ds hk g hg hbase x))
    (T.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_softKernelL2 momentum hm ds hk g hg hbase))
  choose field hmeas heq using h
  exact ⟨field, hmeas, heq⟩

end GptLean.Gaussian
