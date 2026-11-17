import GptLean.Gaussian.SpatialFieldDerivative
import GptLean.Repair.MeasuredTagSobolev
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Passage from Bochner L² identities to identities of joint representatives.
The proof uses finite-measure indicator tests in the Gaussian variable and
Fubini. A countable family of spatial tests consequently has one common
exceptional null set. No pointwise evaluation functional on L² is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

variable {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  {σ : Measure X} {μ : Measure Q} [SFinite σ] [IsFiniteMeasure μ]

/-- Integration of a jointly integrable representative agrees almost
everywhere with the representative of its Bochner L² integral. -/
theorem integral_joint_L2_representative
    (F : X → Lp ℝ 2 μ) (hF : Integrable F σ)
    (f : X → Q → ℝ) (hf : Integrable (Function.uncurry f) (σ.prod μ))
    (heq : ∀ x, f x =ᵐ[μ] (F x : Q → ℝ)) :
    (fun q => ∫ x, f x q ∂σ) =ᵐ[μ] ((∫ x, F x ∂σ : Lp ℝ 2 μ) : Q → ℝ) := by
  have hi : Integrable ((∫ x, F x ∂σ : Lp ℝ 2 μ) : Q → ℝ) μ :=
    (Lp.memLp _).integrable (by norm_num)
  apply hf.integral_prod_right.ae_eq_of_forall_setIntegral_eq _ _ hi
  intro A hA hAfin
  have hp : Integrable (Function.uncurry f) (σ.prod (μ.restrict A)) := by
    exact hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  let v : Lp ℝ 2 μ := indicatorConstLp 2 hA hAfin.ne 1
  calc
    (∫ q in A, ∫ x, f x q ∂σ ∂μ) = ∫ x, (∫ q in A, f x q ∂μ) ∂σ :=
      (integral_integral_swap hp).symm
    _ = ∫ x, inner ℝ v (F x) ∂σ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [L2.inner_indicatorConstLp_one]
      exact integral_congr_ae (ae_restrict_le (heq x))
    _ = inner ℝ v (∫ x, F x ∂σ) := (innerSL ℝ v).integral_comp_comm hF
    _ = ∫ q in A, (∫ x, F x ∂σ : Lp ℝ 2 μ) q ∂μ := L2.inner_indicatorConstLp_one hA hAfin.ne _

/-- One Bochner weak identity gives the actual scalar weak identity for
almost every Gaussian point. Product integrability makes both sides genuine
integrals and is kept explicit in this generic Fubini statement. -/
theorem weak_identity_of_L2_identity
    (F D : X → Lp ℝ 2 μ) (f d : X → Q → ℝ) (φ δφ : X → ℝ)
    (hF : Integrable (fun x => δφ x • F x) σ)
    (hD : Integrable (fun x => φ x • D x) σ)
    (hf : Integrable (fun z : X × Q => δφ z.1 * f z.1 z.2) (σ.prod μ))
    (hd : Integrable (fun z : X × Q => φ z.1 * d z.1 z.2) (σ.prod μ))
    (heqf : ∀ x, f x =ᵐ[μ] (F x : Q → ℝ))
    (heqd : ∀ x, d x =ᵐ[μ] (D x : Q → ℝ))
    (hweak : (∫ x, φ x • D x ∂σ) = -(∫ x, δφ x • F x ∂σ)) :
    ∀ᵐ q ∂μ, (∫ x, φ x * d x q ∂σ) = -(∫ x, δφ x * f x q ∂σ) := by
  have hfeq (x : X) : (fun q => δφ x * f x q) =ᵐ[μ] (δφ x • F x : Lp ℝ 2 μ) := by
    filter_upwards [heqf x, Lp.coeFn_smul (δφ x) (F x)] with q hq hs
    simpa [hq] using hs.symm
  have hdeq (x : X) : (fun q => φ x * d x q) =ᵐ[μ] (φ x • D x : Lp ℝ 2 μ) := by
    filter_upwards [heqd x, Lp.coeFn_smul (φ x) (D x)] with q hq hs
    simpa [hq] using hs.symm
  have hfi := integral_joint_L2_representative _ hF (fun x q => δφ x * f x q) hf hfeq
  have hdi := integral_joint_L2_representative _ hD (fun x q => φ x * d x q) hd hdeq
  rw [hweak] at hdi
  filter_upwards [hfi, hdi, Lp.coeFn_neg (∫ x, δφ x • F x ∂σ)] with q hq hdq hn
  rw [hdq, hn, hq]
  rfl

/-- Countably many spatial tests and derivative labels share one null set.
This is the quantifier order needed before deterministic Sobolev density
extends the identities to arbitrary compact smooth tests. -/
theorem simultaneous_weak_identities
    {I : Type*} [Countable I]
    (F D : I → X → Lp ℝ 2 μ) (f d : I → X → Q → ℝ)
    (φ δφ : I → X → ℝ)
    (hF : ∀ i, Integrable (fun x => δφ i x • F i x) σ)
    (hD : ∀ i, Integrable (fun x => φ i x • D i x) σ)
    (hf : ∀ i, Integrable (fun z : X × Q => δφ i z.1 * f i z.1 z.2) (σ.prod μ))
    (hd : ∀ i, Integrable (fun z : X × Q => φ i z.1 * d i z.1 z.2) (σ.prod μ))
    (heqf : ∀ i x, f i x =ᵐ[μ] (F i x : Q → ℝ))
    (heqd : ∀ i x, d i x =ᵐ[μ] (D i x : Q → ℝ))
    (hweak : ∀ i, (∫ x, φ i x • D i x ∂σ) = -(∫ x, δφ i x • F i x ∂σ)) :
    ∀ᵐ q ∂μ, ∀ i,
      (∫ x, φ i x * d i x q ∂σ) = -(∫ x, δφ i x * f i x q ∂σ) :=
  ae_all_iff.mpr (fun i => weak_identity_of_L2_identity
    (F i) (D i) (f i) (d i) (φ i) (δφ i) (hF i) (hD i)
      (hf i) (hd i) (heqf i) (heqd i) (hweak i))

end GptLean.Gaussian

namespace GptLean.Gaussian

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology ContDiff

/-- The standard countable density fact for compact smooth tests, stated
without reference to Gaussian fields. The common compact support makes local
L² pairings continuous. This is a deterministic Sobolev background input. -/
structure CountableSpatialTestCore where
  test : ℕ → FieldSpace → ℝ
  smooth : ∀ n, ContDiff ℝ ∞ (test n)
  compact : ∀ n, HasCompactSupport (test n)
  dense : ∀ (φ : FieldSpace → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ j : Fin 3, ∃ (K : Set FieldSpace), IsCompact K ∧ ∃ index : ℕ → ℕ,
      (∀ x, x ∉ K → φ x = 0) ∧
      (∀ x, x ∉ K → fderiv ℝ φ x (EuclideanSpace.single j 1) = 0) ∧
      (∀ n x, x ∉ K → test (index n) x = 0) ∧
      (∀ n x, x ∉ K → fderiv ℝ (test (index n)) x (EuclideanSpace.single j 1) = 0) ∧
      Tendsto (fun n => eLpNorm (test (index n) - φ) 2 (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => fderiv ℝ (test (index n)) x (EuclideanSpace.single j 1)) -
          (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)))
        2 (volume.restrict K)) atTop (𝓝 0)

/-- Identities on a countable test core imply the full distributional
identity. This is proved by L² pairing continuity, so the core does not
postulate a completed weak derivative. -/
theorem weakH1Local_of_countable_tests
    (C : CountableSpatialTestCore) (f : FieldSpace → ℝ) (df : Fin 3 → FieldSpace → ℝ)
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    (hd : ∀ j K, IsCompact K → MemLp (df j) 2 (volume.restrict K))
    (hw : ∀ j n, (∫ x, C.test n x * df j x) =
      -(∫ x, fderiv ℝ (C.test n) x (EuclideanSpace.single j 1) * f x)) :
    HasWeakH1Local f df := by
  refine ⟨hf, hd, ?_⟩
  intro j φ hφ hφc
  obtain ⟨K, hK, index, hzero, hdZero, hnzero, hdnzero, hconv, hdconv⟩ :=
    C.dense φ hφ hφc j
  have hφLp : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict K
  have hdφLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1))
      2 (volume.restrict K) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ _)).restrict K
  have hnLp : ∀ n, MemLp (C.test (index n)) 2 (volume.restrict K) := fun n =>
    ((C.smooth _).continuous.memLp_of_hasCompactSupport (C.compact _)).restrict K
  have hdnLp : ∀ n, MemLp
      (fun x => fderiv ℝ (C.test (index n)) x (EuclideanSpace.single j 1))
      2 (volume.restrict K) := fun n =>
    ((((C.smooth _).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((C.compact _).fderiv_apply ℝ _)).restrict K
  have restrict_pair (a b : FieldSpace → ℝ) (hz : ∀ x, x ∉ K → b x = 0) :
      (∫ x, a x • b x) = ∫ x in K, a x • b x := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    rw [hz x hx, smul_zero]
  have htest : ∀ n, (∫ x in K, df j x • C.test (index n) x) =
      -(∫ x in K, f x • fderiv ℝ (C.test (index n)) x (EuclideanSpace.single j 1)) := by
    intro n
    rw [← restrict_pair _ _ (hnzero n), ← restrict_pair _ _ (hdnzero n)]
    simpa only [smul_eq_mul, mul_comm] using hw j (index n)
  have hclosed := weak_derivative_identity_closed_eLpNorm
    (hd j K hK) (hf K hK) hdnLp hnLp hdφLp hφLp hdconv hconv
    (Eventually.of_forall htest)
  rw [← restrict_pair _ _ hzero, ← restrict_pair _ _ hdZero] at hclosed
  simpa only [smul_eq_mul, mul_comm] using hclosed

/-- A countable derivative family and countable test core suffice for one
common almost-everywhere distributional realization. -/
theorem simultaneous_weakH1Local_of_countable_tests
    {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    (C : CountableSpatialTestCore) (field : List (Fin 3) → FieldSpace → Q → ℝ)
    (hlocal : ∀ᵐ q ∂μ, ∀ ds K, IsCompact K →
      MemLp (fun x => field ds x q) 2 (volume.restrict K))
    (hweak : ∀ ds j n, ∀ᵐ q ∂μ,
      (∫ x, C.test n x * field (j :: ds) x q) =
        -(∫ x, fderiv ℝ (C.test n) x (EuclideanSpace.single j 1) * field ds x q)) :
    ∀ᵐ q ∂μ, ∀ ds,
      HasWeakH1Local (fun x => field ds x q) (fun j x => field (j :: ds) x q) := by
  have hall : ∀ᵐ q ∂μ, ∀ ds j n,
      (∫ x, C.test n x * field (j :: ds) x q) =
        -(∫ x, fderiv ℝ (C.test n) x (EuclideanSpace.single j 1) * field ds x q) :=
    ae_all_iff.mpr (fun ds => ae_all_iff.mpr (fun j => ae_all_iff.mpr (hweak ds j)))
  filter_upwards [hlocal, hall] with q hq hw ds
  exact weakH1Local_of_countable_tests C _ _ (hq ds) (fun j => hq (j :: ds)) (hw ds)

end GptLean.Gaussian
