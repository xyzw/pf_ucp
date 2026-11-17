import GptLean.Repair.MeasuredTag
import GptLean.ElectronicLocalizationMetric
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
The measured six-component tag satisfies the weak H1 hypothesis of the
actual recursive tensor lift. The weak identity is derived from the tag's
classical coordinate derivatives. Their measurability follows from the
measurability theorem for line derivatives of continuous functions, and
their local L2 bounds follow from the explicit tag metric estimate.

The zero-velocity branch is included by the same theorem and has derivative
zero. No separate weak derivative or derivative measurability is assumed.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Multipliers
open scoped ENNReal ContDiff

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

omit [DecidableEq I] [CompleteSpace E] in
private theorem compact_test_integrable
    {f : EuclideanSpace ℝ I → E}
    (hf : ∀ C, IsCompact C → MemLp f 2 (volume.restrict C))
    {φ : EuclideanSpace ℝ I → ℝ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) : Integrable (fun x => φ x • f x) := by
  exact integrable_smul_of_memLp_on_support
    ((hφ.memLp_of_hasCompactSupport hs).restrict (tsupport φ))
    (hf _ hs) (fun x hx => image_eq_zero_of_notMem_tsupport hx)

/-- Continuous fields with bounded classical coordinate derivatives satisfy
the distributional H1 identity. The derivatives are measurable as a
consequence of continuity of the original field. -/
theorem weakH1Local_of_continuous_bounded_lineDeriv
    {f : EuclideanSpace ℝ I → E}
    {df : I → EuclideanSpace ℝ I → E}
    (hf : Continuous f)
    (hderiv : ∀ i x, HasLineDerivAt ℝ f (df i x) x (EuclideanSpace.single i 1))
    (C : ℝ) (hbound : ∀ i x, ‖df i x‖ ≤ C) : HasWeakH1Local f df := by
  have hfm : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K) := by
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC x hx
  have hdm : ∀ i K, IsCompact K → MemLp (df i) 2 (volume.restrict K) := by
    intro i K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    have heq : (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) = df i :=
      funext (fun x => (hderiv i x).lineDeriv)
    have hm : AEStronglyMeasurable (df i) volume := by
      rw [← heq]
      exact aestronglyMeasurable_lineDeriv hf volume
    exact MemLp.of_bound hm.restrict C (Eventually.of_forall (hbound i))
  refine ⟨hfm, hdm, ?_⟩
  intro i φ hφ hs
  have hd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_smul_lineDeriv_eq_neg_of_ae_regularLine (D := Set.univ)
  · exact Eventually.of_forall (fun _ _ => Set.mem_univ _)
  · intro x _
    exact hderiv i x
  · intro x
    exact ((hφ.differentiable (by simp) x).hasFDerivAt).hasLineDerivAt _
  · exact compact_test_integrable hfm hd (hs.fderiv_apply ℝ _)
  · exact compact_test_integrable (hdm i) hφ.continuous hs
  · exact compact_test_integrable hfm hφ.continuous hs

/-- Everywhere differentiability and bounded coordinate derivatives give
the actual weak H1 field, also for many-particle Euclidean coordinates. -/
theorem weakH1Local_of_differentiable_bounded
    {f : EuclideanSpace ℝ I → E} (hf : Differentiable ℝ f)
    (C : ℝ) (hbound : ∀ i x, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ C) :
    HasWeakH1Local f (fun i x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
  weakH1Local_of_continuous_bounded_lineDeriv hf.continuous
    (fun _i x => (hf x).hasFDerivAt.hasLineDerivAt _) C hbound

/-- Continuity of the actual tag follows directly from the original velocity.
The real square root is continuous even on the zero-velocity branch. -/
theorem selectedTag_continuous (V M : ℝ)
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} (hv : Continuous v) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      selectedTag V M v (WithLp.ofLp x)) := by
  unfold selectedTag
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Bool => ℂ)).comp
  apply continuous_pi
  intro k
  have hvk : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => v (WithLp.ofLp x) k.1) :=
    (continuous_apply k.1).comp (hv.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)))
  unfold K amp apVal
  fun_prop

/-- Bundling the six actual scalar derivatives gives the Hilbert-valued
coordinate line derivative required by the weak H1 interface. -/
theorem selectedTag_hasLineDerivAt {V M : ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {dv : Fin 3 → Fin 3 → ℝ}
    (x : EuclideanSpace ℝ (Fin 3)) (hV : 0 ≤ V)
    (hvV : ∀ μ, |v (WithLp.ofLp x) μ| ≤ V)
    (hv : ∀ μ ν, HasDerivAt (fun s : ℝ => v (WithLp.ofLp x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv μ ν) 0) (ν : Fin 3) :
    HasLineDerivAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
      selectedTag V M v (WithLp.ofLp y))
      (selectedTagDerivative V M v (WithLp.ofLp x) ν) x (EuclideanSpace.single ν 1) := by
  have hcoords := hasDerivAt_pi.mpr
    (fun k => selectedTag_coordinate_hasDerivAt (M := M) hV hvV hv k ν)
  have hvec : HasDerivAt (fun s : ℝ => selectedTag V M v
      (WithLp.ofLp x + s • (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)))
      (selectedTagDerivative V M v (WithLp.ofLp x) ν) 0 := by
    exact ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 × Bool => ℂ)).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hcoords
  unfold HasLineDerivAt
  simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single] using hvec

set_option maxHeartbeats 800000 in
/-- The explicit measured tag has weak H1 regularity whenever the original
velocity is continuous with bounded classical first derivatives. In
particular this covers smooth residual fields and includes V = 0. -/
theorem selectedTag_hasWeakH1Local {V M : ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hvcont : Continuous v)
    (hvV : ∀ x μ, |v x μ| ≤ V)
    (hdv : ∀ x, ∑ μ, ∑ ν, (dv x μ ν) ^ 2 ≤ M ^ 2)
    (hv : ∀ x μ ν, HasDerivAt (fun s : ℝ => v (x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv x μ ν) 0) :
    HasWeakH1Local
      (fun x : EuclideanSpace ℝ (Fin 3) => selectedTag V M v (WithLp.ofLp x))
      (fun ν x => selectedTagDerivative V M v (WithLp.ofLp x) ν) := by
  apply weakH1Local_of_continuous_bounded_lineDeriv (selectedTag_continuous V M hvcont)
    (fun ν x => selectedTag_hasLineDerivAt x hV (hvV _) (hv _) ν)
    (Real.sqrt (36 * V ^ 2 + 2 * M))
  intro ν x
  have htotal := selectedTag_metric_le (v := v) (dv := dv (WithLp.ofLp x))
    (x := WithLp.ofLp x) hV hM (hvV (WithLp.ofLp x))
    (hdv (WithLp.ofLp x)) (hv (WithLp.ofLp x))
  have hterm : ‖selectedTagDerivative V M v (WithLp.ofLp x) ν‖ ^ 2 ≤
      ∑ j, ‖selectedTagDerivative V M v (WithLp.ofLp x) j‖ ^ 2 :=
    Finset.single_le_sum
      (fun j _ => sq_nonneg ‖selectedTagDerivative V M v (WithLp.ofLp x) j‖)
      (Finset.mem_univ ν)
  exact Real.le_sqrt_of_sq_le (hterm.trans htotal)

/-- A differentiable residual velocity supplies its own actual coordinate
derivatives. Only the velocity and Jacobian bounds need to be checked. -/
theorem selectedTag_hasWeakH1Local_of_differentiable {V M : ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hv : Differentiable ℝ v)
    (hvV : ∀ x μ, |v x μ| ≤ V)
    (hdv : ∀ x, ∑ μ, ∑ ν,
      ((fderiv ℝ v x (Pi.single ν (1 : ℝ))) μ) ^ 2 ≤ M ^ 2) :
    HasWeakH1Local
      (fun x : EuclideanSpace ℝ (Fin 3) => selectedTag V M v (WithLp.ofLp x))
      (fun ν x => selectedTagDerivative V M v (WithLp.ofLp x) ν) := by
  apply selectedTag_hasWeakH1Local hV hM hv.continuous hvV hdv
  intro x μ ν
  exact hasDerivAt_pi.mp
    ((hv x).hasFDerivAt.hasLineDerivAt (Pi.single ν (1 : ℝ))) μ

/-- The same result in the Euclidean coordinates used by the measured
Gaussian residual field and the recursive lift. -/
theorem selectedTag_hasWeakH1Local_euclidean {V M : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hv : Differentiable ℝ v)
    (hvV : ∀ x μ, |v x μ| ≤ V)
    (hdv : ∀ x, ∑ μ, ∑ ν,
      ((fderiv ℝ v x (EuclideanSpace.single ν 1)) μ) ^ 2 ≤ M ^ 2) :
    HasWeakH1Local
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        selectedTag V M (fun y => v (WithLp.toLp 2 y)) (WithLp.ofLp x))
      (fun ν x => selectedTagDerivative V M
        (fun y => v (WithLp.toLp 2 y)) (WithLp.ofLp x) ν) := by
  apply selectedTag_hasWeakH1Local hV hM
    (hv.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)))
    (fun x => hvV (WithLp.toLp 2 x))
    (fun x => hdv (WithLp.toLp 2 x))
  intro x μ ν
  have h := hasDerivAt_pi.mp
    ((hv (WithLp.toLp 2 x)).hasFDerivAt.hasLineDerivAt (EuclideanSpace.single ν 1)) μ
  simpa only [Function.comp_def, WithLp.toLp_add, WithLp.toLp_smul, PiLp.toLp_single] using h

/-- Joint measurability of the actual tag derivative follows from the
primitive velocity and its derivative representatives. The zero branch is
handled explicitly, so no division at a zero selected wavenumber is used
to identify the derivative. -/
theorem selectedTagDerivative_jointly_stronglyMeasurable
    {Q : Type*} [MeasurableSpace Q] {V M : Q → ℝ}
    {v : Q → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ}
    {dv : Q → EuclideanSpace ℝ (Fin 3) → Fin 3 → Fin 3 → ℝ}
    (hV : Measurable V) (hM : Measurable M)
    (hv : StronglyMeasurable (Function.uncurry v))
    (hdv : StronglyMeasurable (Function.uncurry dv))
    (hVnonneg : ∀ q, 0 ≤ V q) (hvV : ∀ q x μ, |v q x μ| ≤ V q)
    (hderiv : ∀ q x μ ν, HasDerivAt
      (fun s : ℝ => v q (x + s • EuclideanSpace.single ν 1) μ) (dv q x μ ν) 0)
    (ν : Fin 3) :
    StronglyMeasurable (fun p : Q × EuclideanSpace ℝ (Fin 3) =>
      selectedTagDerivative (V p.1) (M p.1)
        (fun y => v p.1 (WithLp.toLp 2 y)) (WithLp.ofLp p.2) ν) := by
  have hq : Measurable (fun p : Q × EuclideanSpace ℝ (Fin 3) =>
      selectedWaveNumber (V p.1) (M p.1)) :=
    selectedWaveNumber_measurable (hV.comp measurable_fst) (hM.comp measurable_fst)
  have hvc (i : Fin 3) : Measurable (fun p : Q × EuclideanSpace ℝ (Fin 3) => v p.1 p.2 i) :=
    (measurable_pi_apply i).comp hv.measurable
  have hdc (i j : Fin 3) :
      Measurable (fun p : Q × EuclideanSpace ℝ (Fin 3) => dv p.1 p.2 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hdv.measurable)
  have hxc (i : Fin 3) : Measurable (fun p : Q × EuclideanSpace ℝ (Fin 3) => p.2 i) :=
    (measurable_pi_apply i).comp
    ((WithLp.measurable_ofLp 2 (Fin 3 → ℝ)).comp measurable_snd)
  have hm : Measurable (fun p : Q × EuclideanSpace ℝ (Fin 3) =>
      if V p.1 = 0 then (0 : SixTag) else WithLp.toLp 2
        (fun k => dK (selectedWaveNumber (V p.1) (M p.1))
          (fun _ => v p.1 p.2) (dv p.1 p.2) (WithLp.ofLp p.2) k ν)) := by
    apply measurable_const.ite (measurableSet_eq_fun (hV.comp measurable_fst) measurable_const)
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro k
    unfold dK apDeriv amp
    fun_prop
  convert hm.stronglyMeasurable using 1
  funext p
  by_cases hzero : V p.1 = 0
  · simp only [hzero, selectedTagDerivative_zero, ite_true]
  · have hpos : 0 < V p.1 := lt_of_le_of_ne (hVnonneg p.1) (Ne.symm hzero)
    have h3 := three_mul_lt_sqrt_max hpos (M p.1)
    have hp : 0 < Real.sqrt (max (36 * V p.1 ^ 2) (M p.1)) := by linarith
    have ha : ∀ μ, 3 * |v p.1 p.2 μ| < Real.sqrt (max (36 * V p.1 ^ 2) (M p.1)) :=
      fun μ => by linarith [hvV p.1 p.2 μ]
    have hd : ∀ μ j, HasDerivAt (fun s : ℝ =>
        v p.1 (WithLp.toLp 2 (WithLp.ofLp p.2 + s •
          (Pi.single j (1 : ℝ) : Fin 3 → ℝ))) μ) (dv p.1 p.2 μ j) 0 := by
      intro μ j
      simpa only [WithLp.toLp_add, WithLp.toLp_smul, PiLp.toLp_single,
        WithLp.toLp_ofLp] using hderiv p.1 p.2 μ j
    have ha' : ∀ μ, 3 * |(fun y => v p.1 (WithLp.toLp 2 y)) (WithLp.ofLp p.2) μ| <
        Real.sqrt (max (36 * V p.1 ^ 2) (M p.1)) := by simpa using ha
    have hpk := pderiv_K (v := fun y => v p.1 (WithLp.toLp 2 y))
      (dv := dv p.1 p.2) (x := WithLp.ofLp p.2) hp ha' hd
    ext k
    simp only [hzero, ite_false, selectedTagDerivative, selectedTag, selectedWaveNumber,
      PiLp.toLp_apply, hpk]
    simp only [dK, amp, WithLp.toLp_ofLp]

/-- The tag now supplies the one-particle weak H1 data to the actual
recursive tensor lift without an independent tag regularity assumption. -/
theorem selectedTag_recursiveLift_hasWeakH1Local
    (B : TensorBackground SixTag) (T : TensorMultilinearData B) (N : ℕ)
    {V M : ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    {dv : (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hvcont : Continuous v)
    (hvV : ∀ x μ, |v x μ| ≤ V)
    (hdv : ∀ x, ∑ μ, ∑ ν, (dv x μ ν) ^ 2 ≤ M ^ 2)
    (hv : ∀ x μ ν, HasDerivAt (fun s : ℝ => v (x + s •
      (Pi.single ν (1 : ℝ) : Fin 3 → ℝ)) μ) (dv x μ ν) 0) :
    HasWeakH1Local (recursiveLiftField B N (configurationTensor B
      (fun x => selectedTag V M v (WithLp.ofLp x))))
      (recursiveLiftWeakGradient B N
        (fun x => selectedTag V M v (WithLp.ofLp x))
        (fun ν x => selectedTagDerivative V M v (WithLp.ofLp x) ν)) := by
  apply recursiveLift_hasWeakH1Local B T N
    (selectedTag_hasWeakH1Local hV hM hvcont hvV hdv hv)
  intro x
  exact (selectedTag_norm V M v hV (WithLp.ofLp x) (hvV _)).le

open GptLean.ElectronicLocalization in
/-- The actual symmetric electronic localization has weak H1 regularity
on the physical Euclidean configuration space, including its zero set. -/
theorem electronicLocalization_hasWeakH1Local {A : Type*} {N : ℕ}
    (η : A → EuclideanSpace ℝ (Fin 3) → ℝ)
    (hloc : LocallyFinite (fun a => Function.support (η a)))
    (hd : ∀ a, Differentiable ℝ (η a)) (hpos : ∀ a x, 0 ≤ η a x)
    (hpart : ∀ x, HasSum (fun a => η a x ^ 2) 1)
    (B : ℝ) (hmetric : ∀ x, (∑ j : Fin 3, ∑' a,
      fderiv ℝ (η a) x (EuclideanSpace.single j 1) ^ 2) ≤ B)
    (α : Fin N → A) :
    HasWeakH1Local
      (fun x : Configuration N => symmetricMultiplier η α (fun i => particle x i))
      (fun q x => fderiv ℝ
        (fun y : Configuration N => symmetricMultiplier η α (fun i => particle y i)) x
        (EuclideanSpace.single q 1)) := by
  classical
  let P : Configuration N →L[ℝ] (Fin N → EuclideanSpace ℝ (Fin 3)) :=
    ContinuousLinearMap.pi (fun i => (particleLinear i).toContinuousLinearMap)
  have hP (i : Fin N) (ν : Fin 3) : P (EuclideanSpace.single (i, ν) 1) =
      Pi.single i (EuclideanSpace.single ν 1) := by
    funext j
    change particle (EuclideanSpace.single (i, ν) 1) j = _
    by_cases hj : j = i
    · subst j
      simp [particle_single_same]
    · simp [Pi.single_eq_of_ne hj, particle_single_ne i ν hj]
  have hf := (symmetricMultiplier_differentiable η hd hpos α).comp P.differentiable
  change HasWeakH1Local (symmetricMultiplier η α ∘ P)
    (fun q x => fderiv ℝ (symmetricMultiplier η α ∘ P) x (EuclideanSpace.single q 1))
  apply weakH1Local_of_differentiable_bounded hf (Real.sqrt B)
  intro ⟨i, ν⟩ x
  have hchain := ((symmetricMultiplier_differentiable η hd hpos α) (P x)).hasFDerivAt.comp x P.hasFDerivAt
  change ‖fderiv ℝ (symmetricMultiplier η α ∘ P) x (EuclideanSpace.single (i, ν) 1)‖ ≤ _
  rw [hchain.fderiv, ContinuousLinearMap.comp_apply, hP]
  have hs : Summable (fun β : Fin N → A =>
      fderiv ℝ (symmetricMultiplier η β) (P x) (Pi.single i (EuclideanSpace.single ν 1)) ^ 2) := by
    apply summable_of_hasFiniteSupport
    apply ((symmetricMultiplier_locallyFinite η hloc).point_finite (P x)).subset
    intro β hβ hzero
    apply hβ
    change fderiv ℝ (symmetricMultiplier η β) (P x)
      (Pi.single i (EuclideanSpace.single ν 1)) ^ 2 = 0
    rw [fderiv_eq_zero_of_nonneg (symmetricMultiplier_nonneg η β) hzero]
    simp
  have hlabel := hs.sum_le_tsum {α} (fun _ _ => sq_nonneg _)
  simp only [Finset.sum_singleton] at hlabel
  have hsingle := symmetricMultiplier_single_metric_le η hloc hd hpos hpart (P x) i
    (EuclideanSpace.single ν 1)
  have hcoord : (∑' a, fderiv ℝ (η a) ((P x) i) (EuclideanSpace.single ν 1) ^ 2) ≤
      ∑ j : Fin 3, ∑' a, fderiv ℝ (η a) ((P x) i) (EuclideanSpace.single j 1) ^ 2 :=
    Finset.single_le_sum (fun j _ => tsum_nonneg (fun a =>
      sq_nonneg (fderiv ℝ (η a) ((P x) i) (EuclideanSpace.single j 1))))
      (Finset.mem_univ ν)
  have hsq := hlabel.trans (hsingle.trans (hcoord.trans (hmetric ((P x) i))))
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt hsq

end GptLean.Repair
