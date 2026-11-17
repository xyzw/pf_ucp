import GptLean.PhysicalSourceFubini
import GptLean.ElectronicH1Space
import GptLean.SymmetricLift.L2Mollification
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Weak derivatives of actual product L2 wave functions pass to their
Hilbert-valued Fubini sources. The compact smooth case is proved using
Bochner test integrals and finite-measure set integrals in the fibre.
-/

noncomputable section

namespace GptLean.PhysicalSourceH1

set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter GptLean.SymmetricLift GptLean.ElectronicH1Space
open GptLean.PhysicalSourceFubini GptLean.Repair
open scoped ENNReal Topology ContDiff

section IntegralRepresentative

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SigmaFinite ν]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Bochner integral in L2 has the actual integrated joint representative.
Only finite-measure set integrals are used, so the fibre measure can be infinite. -/
theorem integral_joint_representative
    (F : X → Lp E 2 ν) (hF : Integrable F μ) (f : X → Y → E)
    (hf : Integrable (Function.uncurry f) (μ.prod ν))
    (heq : ∀ᵐ x ∂μ, f x =ᵐ[ν] (F x : Y → E)) :
    (fun y => ∫ x, f x y ∂μ) =ᵐ[ν] ((∫ x, F x ∂μ : Lp E 2 ν) : Y → E) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ _
    exact hf.integral_prod_right.integrableOn
  · intro s _ hνs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hνs.ne
  · intro s hs hνs
    have hrestrict : Integrable (Function.uncurry f) (μ.prod (ν.restrict s)) :=
      hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    let J : Lp E 2 ν →L[ℝ] E := l2SetIntegralCLM s hs hνs.ne
    calc
      (∫ y in s, ∫ x, f x y ∂μ ∂ν) = ∫ x, ∫ y in s, f x y ∂ν ∂μ :=
        (integral_integral_swap hrestrict).symm
      _ = ∫ x, J (F x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [heq] with x hx
        rw [l2SetIntegralCLM_apply]
        exact integral_congr_ae (ae_restrict_le hx)
      _ = J (∫ x, F x ∂μ) := J.integral_comp_comm hF
      _ = ∫ y in s, (∫ x, F x ∂μ : Lp E 2 ν) y ∂ν :=
        l2SetIntegralCLM_apply s hs hνs.ne _

end IntegralRepresentative

section RawSources

variable {I Y H : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]
  {ν : Measure Y} [SigmaFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

abbrev Position (I : Type*) [Fintype I] := EuclideanSpace ℝ I

def rawSource (f : Position I × Y → H) (hf : MemLp f 2 (volume.prod ν)) :
    Lp (Lp H 2 ν) 2 (volume : Measure (Position I)) := curry (hf.toLp f)

omit [DecidableEq I] [CompleteSpace H] in
theorem rawSource_represents_ae (f : Position I × Y → H)
    (hf : MemLp f 2 (volume.prod ν)) :
    ∀ᵐ x ∂volume, (rawSource f hf x : Y → H) =ᵐ[ν] (fun y => f (x, y)) := by
  filter_upwards [curry_ae (hf.toLp f), section_represents_ae (hf.toLp f),
    Measure.ae_ae_of_ae_prod hf.coeFn_toLp] with x hx hsection hraw
  rw [rawSource, hx]
  exact hsection.trans hraw

omit [DecidableEq I] in
theorem rawSource_test_integral_ae (f : Position I × Y → H)
    (hf : MemLp f 2 (volume.prod ν)) (φ : Position I → ℝ)
    (hφ : MemLp φ 2 volume)
    (hint : Integrable (fun p : Position I × Y => φ p.1 • f p) (volume.prod ν)) :
    (fun y => ∫ x, φ x • f (x, y)) =ᵐ[ν]
      ((∫ x, φ x • rawSource f hf x : Lp H 2 ν) : Y → H) := by
  apply integral_joint_representative _ (integrable_l2_test hφ (rawSource f hf))
    (fun x y => φ x • f (x, y)) hint
  filter_upwards [rawSource_represents_ae f hf] with x hx
  filter_upwards [hx, Lp.coeFn_smul (φ x) (rawSource f hf x)] with y hy hsmul
  simpa only [Pi.smul_apply, hy] using hsmul.symm

/-- A raw sectionwise integration-by-parts identity becomes the Bochner
weak identity of the actual Fubini source. The smooth construction below
discharges its tested integrability and sectionwise identity premises. -/
theorem weakH1_rawSource_of_tests
    (f : Position I × Y → H) (df : I → Position I × Y → H)
    (hf : MemLp f 2 (volume.prod ν)) (hdf : ∀ i, MemLp (df i) 2 (volume.prod ν))
    (htest : ∀ i (φ : Position I → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun p : Position I × Y => φ p.1 • df i p) (volume.prod ν) ∧
      Integrable (fun p : Position I × Y =>
        fderiv ℝ φ p.1 (EuclideanSpace.single i 1) • f p) (volume.prod ν))
    (hweak : ∀ i (φ : Position I → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ᵐ y ∂ν, (∫ x, φ x • df i (x, y)) =
        -(∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) • f (x, y))) :
    HasWeakH1Local (rawSource f hf) (fun i => rawSource (df i) (hdf i)) := by
  refine ⟨fun K _ => (Lp.memLp _).restrict K, fun i K _ => (Lp.memLp _).restrict K, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hright := rawSource_test_integral_ae f hf
    (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
    (hdφ.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)) (htest i φ hφ hs).2
  have hleft := rawSource_test_integral_ae (df i) (hdf i) φ
    (hφ.continuous.memLp_of_hasCompactSupport hs) (htest i φ hφ hs).1
  apply Lp.ext
  filter_upwards [hleft, hright, hweak i φ hφ hs,
    Lp.coeFn_neg (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) • rawSource f hf x)]
    with y hleft hright hweak hneg
  rw [← hleft, hneg, Pi.neg_apply, ← hright, hweak]

end RawSources

section SmoothSources

variable {I J H : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

def firstDerivative (f : Position I × Position J → H) (i : I)
    (p : Position I × Position J) : H :=
  fderiv ℝ f p (EuclideanSpace.single i 1, 0)

omit [DecidableEq J] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem firstDerivative_continuous {f : Position I × Position J → H}
    (hf : ContDiff ℝ ∞ f) (i : I) : Continuous (firstDerivative f i) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

omit [DecidableEq J] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem firstDerivative_compact {f : Position I × Position J → H}
    (hs : HasCompactSupport f) (i : I) : HasCompactSupport (firstDerivative f i) :=
  hs.fderiv_apply ℝ _

omit [DecidableEq J] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem firstDerivative_section {f : Position I × Position J → H}
    (hf : ContDiff ℝ ∞ f) (i : I) (x : Position I) (y : Position J) :
    fderiv ℝ (fun z => f (z, y)) x (EuclideanSpace.single i 1) =
      firstDerivative f i (x, y) := by
  have hpair : HasFDerivAt (fun z : Position I => (z, y))
      ((ContinuousLinearMap.id ℝ (Position I)).prod (0 : Position I →L[ℝ] Position J)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
  have h := (hf.differentiable (by simp) (x, y)).hasFDerivAt.comp x hpair
  change fderiv ℝ (f ∘ fun z => (z, y)) x _ = _
  rw [h.fderiv]
  simp [firstDerivative]

omit [DecidableEq J] in
/-- Currying an actual compact smooth product field gives an H1 source,
whose weak derivatives are precisely the curried first-coordinate derivatives. -/
theorem weakH1_rawSource_of_smooth_compact (f : Position I × Position J → H)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    HasWeakH1Local
      (rawSource (ν := volume) f (hf.continuous.memLp_of_hasCompactSupport hs))
      (fun i => rawSource (ν := volume) (firstDerivative f i)
        ((firstDerivative_continuous hf i).memLp_of_hasCompactSupport
          (firstDerivative_compact hs i))) := by
  apply weakH1_rawSource_of_tests
  · intro i φ hφ hφs
    have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    constructor
    · exact ((hφ.continuous.comp continuous_fst).smul
        (firstDerivative_continuous hf i)).integrable_of_hasCompactSupport
        (firstDerivative_compact hs i).smul_left
    · exact ((hdφ.comp continuous_fst).smul hf.continuous).integrable_of_hasCompactSupport
        hs.smul_left
  · intro i φ hφ hφs
    apply Eventually.of_forall
    intro y
    have hsec : ContDiff ℝ ∞ (fun x : Position I => f (x, y)) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    have hw := (weakH1Local_of_contDiff hsec).weak i φ hφ hφs
    simpa only [firstDerivative_section hf] using hw

end SmoothSources

end GptLean.PhysicalSourceH1
