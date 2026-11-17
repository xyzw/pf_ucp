import GptLean.PhotonLocalizationFockChannel

/-!
Support and electronic identities for the actual Fock localization.
Only the universal Fock subspace functor and the unchanged electronic
factor are inputs. The one-photon range condition is proved from the
explicit smooth multiplier and its exact support.
-/

namespace GptLean.PhotonLocalizationFockChannel

open MeasureTheory
open PhotonLocalizationChannel PhotonLocalizationKernelCutoffs

variable {h H T : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]

/-- Universal support functor for the completed Fock space over a
one-photon subspace. Its statement is uniform in the subspace and split. -/
structure FockSubspaces (F : FockFactorization h H) where
  fockSubspace : Submodule ℂ h → Submodule ℂ H
  factor_mem : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) (V : Submodule ℂ h),
    (∀ u, retainedMap j u ∈ V) → ∀ v a, F.factor j v a ∈ fockSubspace V

/-- Second quantization acts on the photon factor and intertwines every
electronic bounded operator for every one-photon split. -/
structure ElectronicFactor (F : FockFactorization h H) (Electronic : Type*) where
  operator : Electronic → H →L[ℂ] H
  intertwines : ∀ (j : h →ₗᵢ[ℂ] WithLp 2 (h × h)) e v a,
    F.factor j (operator e v) a = operator e (F.factor j v a)

section Cutoffs

variable {P E : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]

/-- The actual one-photon spatial support subspace. -/
def supportedOnePhoton (r : ℝ) : Submodule ℂ (Lp E 2 μ) where
  carrier := {u | ∀ᵐ y ∂μ, 2 * r ≤ ‖y‖ → u y = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with y hy
    intro _
    exact hy
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u v] with y hy hz hsum
    intro hr
    change (u + v) y = 0
    rw [hsum]
    change u y + v y = 0
    rw [hy hr, hz hr, zero_add]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u] with y hy hmul
    intro hr
    simp [hmul, hy hr]

omit [IsScalarTower ℝ ℂ E] in
/-- The range of the actual retained multiplier has the claimed support. -/
theorem cutoffMap_mem_supported {r : ℝ} (hr : 0 < r) (u : Lp E 2 μ) :
    cutoffMap r u ∈ supportedOnePhoton r := by
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) u] with y hy
  intro hyr
  change retainedOperator r u y = 0
  rw [show retainedOperator r u y = retained r y • u y from hy,
    retained_eq_zero hr hyr, zero_smul]

omit [IsScalarTower ℝ ℂ E] in
/-- Every actual Kraus vector retains the physical Fock support. This
holds for the original spectral vectors and hence for their flattening. -/
theorem kraus_mem_supported (F : FockFactorization (Lp E 2 μ) H) (S : FockSubspaces F)
    (m : ℕ) (v : H) (a : ℕ) :
    F.factor (complexOnePhotonIsometry (radius m)) v a ∈
      S.fockSubspace (supportedOnePhoton (radius m)) :=
  S.factor_mem _ _ (cutoffMap_mem_supported (radius_pos m)) v a

omit [IsScalarTower ℝ ℂ E] in
theorem flattened_mem_supported (F : FockFactorization (Lp E 2 μ) H) (S : FockSubspaces F)
    (m : ℕ) (v : ℕ → H) (a : ℕ) :
    Repair.flattenVectors (fun n b => F.factor (complexOnePhotonIsometry (radius m)) (v n) b) a ∈
      S.fockSubspace (supportedOnePhoton (radius m)) :=
  kraus_mem_supported F S m _ _

omit [IsScalarTower ℝ ℂ E] in
/-- Applying an electronic cutoff to the original Kraus vectors keeps
photon support, by moving it to the input of the same universal split. -/
theorem electronic_kraus_mem_supported (F : FockFactorization (Lp E 2 μ) H)
    (S : FockSubspaces F) {Electronic : Type*} (A : ElectronicFactor F Electronic)
    (e : Electronic) (m : ℕ) (v : H) (a : ℕ) :
    A.operator e (F.factor (complexOnePhotonIsometry (radius m)) v a) ∈
      S.fockSubspace (supportedOnePhoton (radius m)) := by
  rw [← A.intertwines]
  exact kraus_mem_supported F S m _ _

omit [IsScalarTower ℝ ℂ E] in
/-- Preservation of every bounded electronic observable on the concrete
localized state follows from the unchanged electronic tensor factor. -/
theorem localize_electronic (R : Gaussian.RankOneData H T) (N : NormalTraceData R)
    (F : FockFactorization (Lp E 2 μ) H) {Electronic : Type*}
    (A : ElectronicFactor F Electronic) (e : Electronic) (B : T →L[ℝ] ℂ)
    (hB : ∀ v, B (R.rankOne v) = inner ℂ v (A.operator e v))
    (m : ℕ) {x : T} (hx : x ∈ R.positive) :
    B (localize R N F m x) = B x :=
  N.electronic _ _ B hB (A.intertwines _ e) hx

/-- The actual retained multiplier is a positive contraction in the
quadratic inequality needed by the vacuum second-quantization argument. -/
theorem cutoffMap_positive_contraction (r : ℝ) (u : Lp E 2 μ) :
    ‖cutoffMap r u‖ ^ 2 ≤ (inner ℂ u (cutoffMap r u)).re := by
  rw [cutoffMap_apply, PhotonKernelLocalization.l2_norm_sq_eq_integral, L2.inner_def]
  change (∫ y, ‖retainedOperator r u y‖ ^ 2 ∂μ) ≤
    RCLike.re (∫ y, inner ℂ (u y) (retainedOperator r u y) ∂μ)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) u (retainedOperator r u))]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _))
    (L2.integrable_inner (𝕜 := ℂ) u (retainedOperator r u)).re
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae
    (retained r) (retained_measurable r) (ae_of_all _ (retained_abs_le_one r)) u] with y hy
  change ‖retainedOperator r u y‖ ^ 2 ≤ (inner ℂ (u y) (retainedOperator r u y)).re
  rw [show retainedOperator r u y = retained r y • u y from hy,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hi : (inner ℂ (u y) (retained r y • u y)).re = retained r y * ‖u y‖ ^ 2 := by
    rw [← IsScalarTower.algebraMap_smul ℂ (retained r y) (u y)]
    change (inner ℂ (u y) ((retained r y : ℂ) • u y)).re = _
    simp only [inner_smul_right, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rfl
  rw [hi]
  have hc := retained_nonneg r y
  have hc1 := retained_le_one r y
  exact mul_le_mul_of_nonneg_right (by nlinarith : retained r y ^ 2 ≤ retained r y)
    (sq_nonneg ‖u y‖)

end Cutoffs

end GptLean.PhotonLocalizationFockChannel
