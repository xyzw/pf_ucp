import GptLean.PhotonLocalizationChannel
import GptLean.PhotonLocalizationKernelCutoffs

/-!
The physical photon localization channel relative to universal Fock facts.

`FockFactorization` is second quantization followed by the exponential
law for a direct sum and coordinates in an environmental Fock basis. It
acts on every one-photon isometry, not a supplied localization family.
The actual one-photon input below is the smooth L² cutoff isometry.

The optional Weyl calculus is the universal vacuum characteristic identity
for this factorization, tested also against electronic operators. It
proves composition at separated radii from cutoff absorption. No channel
composition law or localized observable identity is assumed.
-/

namespace GptLean.PhotonLocalizationFockChannel

open MeasureTheory
open scoped InnerProductSpace
open PhotonLocalizationChannel PhotonLocalizationKernelCutoffs

variable {h H T : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- The universal bosonic exponential law with an unchanged electronic
factor, represented in a countable basis of the discarded Fock space. -/
structure FockFactorization (h H : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  factor : (h →ₗᵢ[ℂ] WithLp 2 (h × h)) → KrausIsometry H

/-- The first component of a one-photon splitting. -/
noncomputable def retainedMap (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) : h →L[ℂ] h :=
  (WithLp.fstL 2 ℂ h h).comp j.toContinuousLinearMap

/-- Universal Fock Weyl calculus. The tests include electronic bounded
operators so that they separate full electron-photon normal states. The
only dilation identity is the vacuum formula on vectors, before the
partial trace and the normal extension are taken. -/
structure WeylCalculus (R : Gaussian.RankOneData H T) (F : FockFactorization h H)
    (Test : Type*) where
  test : Test → h → T →L[ℝ] ℂ
  separates : ∀ x y : T, (∀ t f, test t f x = test t f y) → x = y
  vacuum_formula : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (adj : h →L[ℂ] h),
    (∀ u v, inner ℂ (retainedMap j u) v = inner ℂ u (adj v)) →
    ∀ t f v, HasSum (fun a => test t f (R.rankOne (F.factor j v a)))
      (Real.exp ((‖adj f‖ ^ 2 - ‖f‖ ^ 2) / 2) • test t (adj f) (R.rankOne v))

namespace WeylCalculus

variable {R : Gaussian.RankOneData H T} {F : FockFactorization h H} {Test : Type*}
  (W : WeylCalculus R F Test) (N : NormalTraceData R)

/-- The normal-channel characteristic identity follows from the pure
vector formula and the proved spectral extension theorem. -/
theorem characteristic (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (adj : h →L[ℂ] h)
    (hadj : ∀ u v, inner ℂ (retainedMap j u) v = inner ℂ u (adj v))
    (t : Test) (f : h) {x : T} (hx : x ∈ R.positive) :
    W.test t f (N.extend (F.factor j) x) =
      Real.exp ((‖adj f‖ ^ 2 - ‖f‖ ^ 2) / 2) • W.test t (adj f) x := by
  apply N.observable (F.factor j) (W.test t f)
    (Real.exp ((‖adj f‖ ^ 2 - ‖f‖ ^ 2) / 2) • W.test t (adj f)) _ hx
  intro v
  exact Repair.rankOneSeries_observable R (W.test t f) (kraus_mass (F.factor j) v)
    (W.vacuum_formula j adj hadj t f v)

include W in
/-- Absorption of the retained one-photon maps proves the channel
composition. The environmental factor disappears by the vacuum formula. -/
theorem composition (j k : h →ₗᵢ[ℂ] WithLp 2 (h × h))
    (a b : h →L[ℂ] h)
    (ha : ∀ u v, inner ℂ (retainedMap j u) v = inner ℂ u (a v))
    (hb : ∀ u v, inner ℂ (retainedMap k u) v = inner ℂ u (b v))
    (hab : ∀ f, b (a f) = a f) {x : T} (hx : x ∈ R.positive) :
    N.extend (F.factor j) (N.extend (F.factor k) x) = N.extend (F.factor j) x := by
  apply W.separates
  intro t f
  rw [W.characteristic N j a ha t f (N.positive (F.factor k) hx),
    W.characteristic N k b hb t (a f) hx,
    W.characteristic N j a ha t f hx, hab]
  simp

end WeylCalculus

section Cutoffs

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]

/-- The actual complex-linear retained multiplier extracted from the
constructed localization isometry. -/
noncomputable def cutoffMap (r : ℝ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  retainedMap (complexOnePhotonIsometry r)

omit [IsScalarTower ℝ ℂ E] in
@[simp] theorem cutoffMap_apply (r : ℝ) (v : Lp E 2 μ) :
    cutoffMap r v = retainedOperator r v := rfl

/-- Real multiplication is self-adjoint on the physical complex L² space. -/
theorem cutoffMap_selfAdjoint (r : ℝ) (u v : Lp E 2 μ) :
    inner ℂ (cutoffMap r u) v = inner ℂ u (cutoffMap r v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) u,
    PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) v]
    with y hu hv
  change inner ℂ (retainedOperator r u y) (v y) =
    inner ℂ (u y) (retainedOperator r v y)
  rw [show retainedOperator r u y = retained r y • u y from hu,
    show retainedOperator r v y = retained r y • v y from hv]
  rw [← IsScalarTower.algebraMap_smul ℂ (retained r y) (u y),
    ← IsScalarTower.algebraMap_smul ℂ (retained r y) (v y)]
  change inner ℂ ((retained r y : ℂ) • u y) (v y) =
    inner ℂ (u y) ((retained r y : ℂ) • v y)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

omit [IsScalarTower ℝ ℂ E] in
/-- Nested retained maps absorb in the order used by Heisenberg tests. -/
theorem cutoffMap_absorption {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : 2 * r ≤ s) (v : Lp E 2 μ) :
    cutoffMap s (cutoffMap r v) = cutoffMap r v := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained s) (retained_measurable s) (ae_of_all _ (retained_abs_le_one s))
      (retainedOperator r v),
    PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) v,
    PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) v]
    with y h₁ h₂ h₃
  change retainedOperator s (retainedOperator r v) y = retainedOperator r v y
  rw [show retainedOperator s (retainedOperator r v) y =
      retained s y • retainedOperator r v y from h₁,
    show retainedOperator r v y = retained r y • v y from h₂,
    smul_smul, mul_comm (retained s y), retained_absorption hr hs hrs]

/-- Fock localization is now a defined trace-class map at the actual
geometric radius, rather than an input family of localized states. -/
noncomputable def localize (R : Gaussian.RankOneData H T) (N : NormalTraceData R)
    (F : FockFactorization (Lp E 2 μ) H) (m : ℕ) : T →L[ℝ] T :=
  N.extend (F.factor (complexOnePhotonIsometry (radius m)))

omit [IsScalarTower ℝ ℂ E] in
theorem localize_positive (R : Gaussian.RankOneData H T) (N : NormalTraceData R)
    (F : FockFactorization (Lp E 2 μ) H) (m : ℕ) {x : T} (hx : x ∈ R.positive) :
    localize R N F m x ∈ R.positive :=
  N.positive _ hx

omit [IsScalarTower ℝ ℂ E] in
theorem localize_trace (R : Gaussian.RankOneData H T) (N : NormalTraceData R)
    (F : FockFactorization (Lp E 2 μ) H) (m : ℕ) {x : T} (hx : x ∈ R.positive) :
    R.trace (localize R N F m x) = R.trace x :=
  N.trace _ hx

theorem localize_comp (R : Gaussian.RankOneData H T) (N : NormalTraceData R)
    (F : FockFactorization (Lp E 2 μ) H) {Test : Type*} (W : WeylCalculus R F Test)
    {m l : ℕ} (hml : m < l) {x : T} (hx : x ∈ R.positive) :
    localize R N F m (localize R N F l x) = localize R N F m x := by
  apply W.composition N _ _ (cutoffMap (radius m)) (cutoffMap (radius l))
    (cutoffMap_selfAdjoint _) (cutoffMap_selfAdjoint _) _ hx
  intro v
  apply cutoffMap_absorption (radius_pos m) (radius_pos l)
  unfold radius
  calc
    2 * (3 : ℝ) ^ (m + 1) ≤ 3 * (3 : ℝ) ^ (m + 1) := by
      gcongr
      norm_num
    _ = (3 : ℝ) ^ (m + 2) := by
      rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
      ring
    _ ≤ (3 : ℝ) ^ (l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)

end Cutoffs

end GptLean.PhotonLocalizationFockChannel
