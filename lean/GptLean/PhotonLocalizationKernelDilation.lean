import GptLean.PhotonLocalizationPhysicalKernelDuality
import GptLean.PhotonLocalizationCovariantGraph

/-!
The physical cutoff kernels supply the sharp kinetic dilation source.

The field background is uniform over continuous kernel profiles and all
one-photon splittings. Its bounds are the annihilation estimate, integrated
CCR and complementary-vacuum identity on a fixed reference graph. The
small scalar in the final source is the proved compact supremum of the
actual Fourier cutoff errors on the electronic support.
-/

noncomputable section

namespace GptLean.PhotonLocalizationPhysicalKernels

open MeasureTheory Filter Topology Gaussian
open PhotonLocalization PhotonLocalizationKernelCutoffs
open PhotonLocalizationChannel PhotonLocalizationFockChannel
open scoped ENNReal InnerProductSpace

variable {Ω E S V ι : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι]
  {μ : Measure FieldSpace}

namespace FourierRadiationCoordinates

variable (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))
  (J : V ≃ₗᵢ[ℝ] S)

omit [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem representative_sub {a b : Lp E 2 μ} {v w : S}
    (ha : C.representative J a v) (hb : C.representative J b w) :
    C.representative J (a - b) (v - w) := by
  unfold representative at ha hb ⊢
  simp only [map_sub]
  filter_upwards [ha, hb, Lp.coeFn_sub (C.energyFourier (J.symm v))
    (C.energyFourier (J.symm w)), Lp.coeFn_sub (C.fourier a) (C.fourier b)]
    with p hp hq he hf
  rw [he, hf]
  simp only [Pi.sub_apply, hp, hq, smul_sub]

omit [SMulCommClass ℝ ℂ E] in
theorem representative_smul (r : ℝ) {a : Lp E 2 μ} {v : S}
    (ha : C.representative J a v) : C.representative J (r • a) (r • v) := by
  unfold representative at ha ⊢
  have henergy : C.energyFourier (r • J.symm v) = r • C.energyFourier (J.symm v) :=
    C.energyFourier.toLinearEquiv.toLinearMap.map_smul_of_tower r _
  have hfourier : C.fourier (r • a) = r • C.fourier a :=
    C.fourier.toLinearEquiv.toLinearMap.map_smul_of_tower r _
  rw [map_smul, henergy, hfourier]
  filter_upwards [ha, Lp.coeFn_smul r (C.energyFourier (J.symm v)),
    Lp.coeFn_smul r (C.fourier a)] with p hp he hf
  rw [he, hf]
  simp only [Pi.smul_apply]
  rw [hp]
  exact smul_comm r (Real.sqrt ‖C.momentum p‖)⁻¹ (C.fourier a p)

end FourierRadiationCoordinates

omit [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E] in
theorem tailOperator_eq_sub_retained (n : ℕ) (a : Lp E 2 μ) :
    tailOperator n a = a - retainedOperator (radius n) a := by
  apply Lp.ext
  filter_upwards [PhotonKernelLocalization.l2Multiplier_apply_ae (tail n)
    (tail_measurable n) (ae_of_all _ (tail_abs_le_one n)) a,
    PhotonKernelLocalization.l2Multiplier_apply_ae (retained (radius n))
      (retained_measurable _) (ae_of_all _ (retained_abs_le_one _)) a,
    Lp.coeFn_sub a (retainedOperator (radius n) a)] with y ht hr hs
  change tailOperator n a y = (a - retainedOperator (radius n) a) y
  change tailOperator n a y = tail n y • a y at ht
  change retainedOperator (radius n) a y = retained (radius n) y • a y at hr
  rw [hs, Pi.sub_apply, ht]
  change (1 - retained (radius n) y) • a y = a y - retainedOperator (radius n) a y
  rw [hr, sub_smul, one_smul]

/-- A kernel profile includes its actual inverse-frequency representative,
not an independent negative-Sobolev norm function. -/
structure SpatialKernelProfile
    (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))
    (J : V ≃ₗᵢ[ℝ] S) (ι : Type*) [TopologicalSpace ι] where
  l2 : ι × FieldSpace → Lp E 2 μ
  negative : ι × FieldSpace → S
  continuous_l2 : Continuous l2
  continuous_negative : Continuous negative
  bounded_l2 : ∃ M : ℝ, ∀ z, ‖l2 z‖ ≤ M
  bounded_negative : ∃ M : ℝ, ∀ z, ‖negative z‖ ≤ M
  represents : ∀ z, C.representative J (l2 z) (negative z)

namespace SpatialKernelProfile

variable {C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν)}
  {J : V ≃ₗᵢ[ℝ] S}

/-- A bounded real electronic multiplier acts on both realizations of
the same profile. It leaves the photon Fourier identification intact. -/
def multiply (p : SpatialKernelProfile C J ι) (η : ι × FieldSpace → ℝ)
    (hη : Continuous η) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, |η z| ≤ M) :
    SpatialKernelProfile C J ι where
  l2 z := η z • p.l2 z
  negative z := η z • p.negative z
  continuous_l2 := hη.smul p.continuous_l2
  continuous_negative := hη.smul p.continuous_negative
  bounded_l2 := by
    obtain ⟨K, hK⟩ := p.bounded_l2
    refine ⟨M * K, fun z => ?_⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbound z) (hK z) (norm_nonneg _) hM
  bounded_negative := by
    obtain ⟨K, hK⟩ := p.bounded_negative
    refine ⟨M * K, fun z => ?_⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbound z) (hK z) (norm_nonneg _) hM
  represents z := C.representative_smul J (η z) (p.represents z)

end SpatialKernelProfile

namespace FormFactors

variable (F : FormFactors ν ι)
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))
  (J : V ≃ₗᵢ[ℝ] S) (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
  (W : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S)
  (hdispersion : F.momentum = C.momentum)
  (hU : ∀ f, C.fourier (U f) = f)
  (hW : ∀ f, C.energyFourier (J.symm (W f)) = f)

def profile : SpatialKernelProfile C J ι where
  l2 := F.positionKernel U
  negative := F.sobolevKernel W
  continuous_l2 := U.continuous.comp F.continuous_fourierKernel
  continuous_negative := W.continuous.comp F.continuous_weightedFourierKernel
  bounded_l2 := by
    classical
    refine ⟨∑ i : ι, ‖F.positionKernel U (i, 0)‖, fun z => ?_⟩
    have he : ‖F.positionKernel U z‖ = ‖F.positionKernel U (z.1, 0)‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [F.positionKernel_norm_sq, F.positionKernel_norm_sq]
    rw [he]
    exact Finset.single_le_sum (f := fun i : ι => ‖F.positionKernel U (i, 0)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ z.1)
  bounded_negative := by
    classical
    refine ⟨∑ i : ι, ‖F.sobolevKernel W (i, 0)‖, fun z => ?_⟩
    have he : ‖F.sobolevKernel W z‖ = ‖F.sobolevKernel W (z.1, 0)‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [F.sobolevKernel_norm_sq, F.sobolevKernel_norm_sq]
    rw [he]
    exact Finset.single_le_sum (f := fun i : ι => ‖F.sobolevKernel W (i, 0)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ z.1)
  represents := C.formFactors_representative F hdispersion U W J hU hW

/-- The field correction is the actual L² tail and the actual Sobolev
tail of the same form factor. Their compatibility follows from universal
multiplier compatibility and subtraction in Fourier coordinates. -/
def tailProfile (B : SobolevMultiplierBackground S)
    (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (_ : HasCompactSupport χ)
      (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
      C.representative J a w →
      C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
        (B.multiplier χ w)) (n : ℕ) : SpatialKernelProfile C J ι where
  l2 z := tailOperator n (F.positionKernel U z)
  negative z := B.negative n (F.sobolevKernel W z)
  continuous_l2 := (tailOperator n).continuous.comp
    (U.continuous.comp F.continuous_fourierKernel)
  continuous_negative := (B.negative n).continuous.comp
    (W.continuous.comp F.continuous_weightedFourierKernel)
  bounded_l2 := by
    obtain ⟨M, hM⟩ := (F.profile C J U W hdispersion hU hW).bounded_l2
    exact ⟨‖tailOperator (E := E) (μ := μ) n‖ * M, fun z =>
      ((tailOperator n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _))⟩
  bounded_negative := by
    obtain ⟨M, hM⟩ := (F.profile C J U W hdispersion hU hW).bounded_negative
    exact ⟨‖B.negative n‖ * M, fun z => ((B.negative n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _))⟩
  represents z := by
    rw [tailOperator_eq_sub_retained]
    apply C.representative_sub J
      (C.formFactors_representative F hdispersion U W J hU hW z)
    exact hmultiplier _ (retained_smooth _) (retained_compact (radius_pos n))
      (retained_measurable _) (ae_of_all _ (retained_abs_le_one _)) _ _
      (C.formFactors_representative F hdispersion U W J hU hW z)

end FormFactors

section FieldCalculus

variable {Q H T : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {A : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}

/-- Universal spatial field calculus on one reference graph. The region
contains its electronic support. The profile and the one-photon split
are arbitrary, and no localization error or asymptotic estimate is a
field. The complementary vacuum norm is expressed by the usual
one-photon norm difference before the physical square partition is used. -/
structure SpatialFieldCalculus
    (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))
    (J : V ≃ₗᵢ[ℝ] S) (Fock : FockFactorization (Lp E 2 μ) H)
    (region : Set FieldSpace) (inclusion radiation : Q →L[ℂ] H) (charge : ℝ) where
  ann : SpatialKernelProfile C J ι → ι → Q →L[ℂ] H
  cre : SpatialKernelProfile C J ι → ι → Q →L[ℂ] H
  covariant : SpatialKernelProfile C J ι → ι → H →ₗ.[ℂ] H
  closed : ∀ p i, (covariant p i).IsClosed
  core : Set Q
  dense : Dense core
  vacuum : (Lp E 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp E 2 μ × Lp E 2 μ)) →
    (Lp E 2 μ →L[ℂ] Lp E 2 μ) → SpatialKernelProfile C J ι →
      ι → Q →L[ℂ] lp (fun _ : ℕ => H) 2
  annihilation_bound : ∀ p i M, 0 ≤ M →
    (∀ x ∈ region, ‖p.negative (i, x)‖ ≤ M) →
    ∀ q, ‖ann p i q‖ ≤ M * ‖radiation q‖
  creation_bound : ∀ p i M, 0 ≤ M →
    (∀ x ∈ region, ‖p.l2 (i, x)‖ ≤ M) →
    ∀ q, ‖cre p i q‖ ^ 2 ≤ ‖ann p i q‖ ^ 2 + M ^ 2 * ‖inclusion q‖ ^ 2
  vacuum_bound : ∀ j adj,
    (∀ u v, ⟪retainedMap j u, v⟫_ℂ = ⟪u, adj v⟫_ℂ) →
    ∀ p i M, 0 ≤ M →
    (∀ x ∈ region, ‖p.l2 (i, x)‖ ^ 2 - ‖adj (p.l2 (i, x))‖ ^ 2 ≤ M ^ 2) →
    ∀ q, ‖vacuum j adj p i q‖ ^ 2 ≤ M ^ 2 * ‖inclusion q‖ ^ 2
  vacuum_orthogonal : ∀ j adj,
    (∀ u v, ⟪retainedMap j u, v⟫_ℂ = ⟪u, adj v⟫_ℂ) →
    ∀ p q i v, ⟪Fock.factor j v, vacuum j adj p i q⟫_ℂ = 0
  core_identity : ∀ p correction j adj,
    (∀ u v, ⟪retainedMap j u, v⟫_ℂ = ⟪u, adj v⟫_ℂ) →
    (∀ z, correction.l2 z = p.l2 z - adj (p.l2 z)) →
    ∀ (derivative : ι → Q →L[ℂ] H) q, q ∈ core →
    (∀ i, (inclusion q, derivative i q) ∈ (covariant p i).graph) →
    ∀ i k, (Fock.factor j (inclusion q) k,
      covariantDilationDerivative (Fock.factor j) (derivative i)
        (ann correction i) (cre correction i) ((charge : ℂ) • vacuum j adj p i) charge q k)
        ∈ (covariant p i).graph

namespace SpatialFieldCalculus

variable
  (C : FourierRadiationCoordinates (E := E) (V := V) (μ := μ) (ν := ν))
  (J : V ≃ₗᵢ[ℝ] S) (Fock : FockFactorization (Lp E 2 μ) H)
  {region : Set FieldSpace} {inclusion radiation : Q →L[ℂ] H}
  {charge : ℝ}
  (G : SpatialFieldCalculus (ι := ι) C J Fock region inclusion radiation charge)

/-- The compact-uniform Fourier error supplies every small field bound
in the reference-core construction. Its radius contains the support of
the actual electronic multiplier at scale `l + 1`. -/
def physicalSource
    (F : FormFactors ν ι) (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (W : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S)
    (hdispersion : F.momentum = C.momentum)
    (hU : ∀ f, C.fourier (U f) = f)
    (hW : ∀ f, C.energyFourier (J.symm (W f)) = f)
    (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (_ : HasCompactSupport χ)
      (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
      C.representative J a w →
      C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
        (B.multiplier χ w))
    (kinetic controlForm : RemovalState.PositiveForm Tr)
    (derivative : ι → Q →L[ℂ] H)
    (hsource : ∀ q ∈ G.core, ∀ i,
      (inclusion q, derivative i q) ∈
        (G.covariant (F.profile C J U W hdispersion hU hW) i).graph)
    (hkinetic : ∀ (v : H) (z : ι → H), (∀ i, (v, z i) ∈
      (G.covariant (F.profile C J U W hdispersion hU hW) i).graph) →
      kinetic.expectation (A.rankOne v) = ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖z i‖ ^ 2))
    (hcontrol : ∀ q, controlForm.expectation (A.rankOne (inclusion q)) =
      ENNReal.ofReal (‖q‖ ^ 2))
    (hinclusion : ‖inclusion‖ ≤ 1) (l n : ℕ)
    (hsupport : ∀ x ∈ region, ‖x‖ ≤ (2 * (l + 1) : ℕ)) (q : Q) :
    KineticDilationSource (A := A) (ι := ι) kinetic controlForm
      (Fock.factor (complexOnePhotonIsometry (radius n))) (inclusion q)
      charge ((F.cutoffFamily U W B).error (2 * (l + 1)) n)
      (2 * ‖radiation‖ + ‖inclusion‖) (∑ i, ‖derivative i‖) := by
  let p := F.profile C J U W hdispersion hU hW
  let c := F.tailProfile C J U W hdispersion hU hW B hmultiplier n
  let j := complexOnePhotonIsometry (E := E) (μ := μ) (radius n)
  let adj := retainedMap j
  let ε := (F.cutoffFamily U W B).error (2 * (l + 1)) n
  have hε : 0 ≤ ε := (F.cutoffFamily U W B).error_nonneg _ _
  have hadj : ∀ u v, ⟪retainedMap j u, v⟫_ℂ = ⟪u, adj v⟫_ℂ := by
    intro u v
    exact (l2Multiplier_inner (retained (radius n)) (retained_measurable _)
      (ae_of_all _ (retained_abs_le_one _)) u v).symm
  have hcomp (z : ι × FieldSpace) (hz : z.2 ∈ region) :=
    F.cutoff_component_bounds U W B (hsupport _ hz) (n := n)
  refine KineticDilationSource.ofReferenceCore kinetic controlForm (Fock.factor j)
    inclusion radiation derivative (G.ann c) (G.cre c)
    (fun i => (charge : ℂ) • G.vacuum j adj p i)
    (G.covariant p) (G.closed p) G.core G.dense hsource hkinetic hcontrol
    hinclusion charge ε ?_ ?_ ?_ ?_ ?_ q
  · intro r hr i k
    apply G.core_identity p c j adj hadj _ derivative r hr (hsource r hr) i k
    intro z
    exact tailOperator_eq_sub_retained n (F.positionKernel U z)
  · exact fun r i => G.annihilation_bound c i ε hε
      (fun x hx => (hcomp (i, x) hx).2.1) r
  · exact fun r i => G.creation_bound c i ε hε (fun x hx => (hcomp (i, x) hx).1) r
  · intro r i
    have hv := G.vacuum_bound j adj hadj p i ε hε (fun x hx => ?_) r
    · simp only [smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv (sq_nonneg charge)
    · have hs := square_partition_l2 (radius n) (F.positionKernel U (i, x))
      have hb := (hcomp (i, x) hx).2.2
      have hb2 : ‖discardOperator n (F.positionKernel U (i, x))‖ ^ 2 ≤ ε ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hε).mpr hb
      change ‖F.positionKernel U (i, x)‖ ^ 2 -
        ‖retainedOperator (radius n) (F.positionKernel U (i, x))‖ ^ 2 ≤ ε ^ 2
      change ‖discardedOperator (radius n) (F.positionKernel U (i, x))‖ ^ 2 ≤ ε ^ 2 at hb2
      linarith
  · intro r i
    simp only [smul_apply, inner_smul_right,
      G.vacuum_orthogonal j adj hadj p r i, mul_zero]

omit [SMulCommClass ℝ ℂ E] in
/-- A compact electronic test restricts the actual tail profile before
the field estimate. The reference source itself need not be electronically
supported in this ball. The commutation identity is uniform over all
profiles and is just multiplication in the electronic variable. -/
theorem tested_tail_field_bound
    (F : FormFactors ν ι) (U : Lp ℂ 2 ν ≃ₗᵢ[ℝ] Lp E 2 μ)
    (W : Lp ℂ 2 ν ≃ₗᵢ[ℝ] S) (B : SobolevMultiplierBackground S)
    (hdispersion : F.momentum = C.momentum)
    (hU : ∀ f, C.fourier (U f) = f)
    (hW : ∀ f, C.energyFourier (J.symm (W f)) = f)
    (hmultiplier : ∀ (χ : FieldSpace → ℝ) (_ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (_ : HasCompactSupport χ)
      (hχm : AEStronglyMeasurable χ μ) (hb : ∀ᵐ y ∂μ, |χ y| ≤ 1) a w,
      C.representative J a w →
      C.representative J (PhotonKernelLocalization.l2Multiplier χ hχm hb a)
        (B.multiplier χ w))
    (η : ι × FieldSpace → ℝ) (hη : Continuous η)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z, |η z| ≤ M)
    (Z : ι → ℝ) (hZ : ∀ i, 0 ≤ Z i) (hηZ : ∀ z, |η z| ≤ Z z.1)
    (r : ℕ) (hsupport : ∀ z, (r : ℝ) < ‖z.2‖ → η z = 0)
    (test : ι → H →L[ℂ] H)
    (htest : ∀ (p : SpatialKernelProfile C J ι) i q,
      test i (G.ann p i q + G.cre p i q) =
        G.ann (p.multiply η hη hM hbound) i q +
          G.cre (p.multiply η hη hM hbound) i q)
    (n : ℕ) (q : Q) (i : ι) :
    let p := F.tailProfile C J U W hdispersion hU hW B hmultiplier n
    ‖test i (G.ann p i q + G.cre p i q)‖ ≤
      Z i * (F.cutoffFamily U W B).error r n *
        (2 * ‖radiation‖ + ‖inclusion‖) * ‖q‖ := by
  dsimp only
  let p := F.tailProfile C J U W hdispersion hU hW B hmultiplier n
  let tested := p.multiply η hη hM hbound
  let ε := (F.cutoffFamily U W B).error r n
  have hε : 0 ≤ ε := (F.cutoffFamily U W B).error_nonneg _ _
  have hb (x : FieldSpace) :
      ‖tested.l2 (i, x)‖ ≤ Z i * ε ∧ ‖tested.negative (i, x)‖ ≤ Z i * ε := by
    by_cases hx : ‖x‖ ≤ (r : ℝ)
    · have hc := F.cutoff_component_bounds U W B (z := (i, x)) (n := n) hx
      constructor
      · change ‖η (i, x) • tailOperator n (F.positionKernel U (i, x))‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hηZ (i, x)) hc.1 (norm_nonneg _) (hZ i)
      · change ‖η (i, x) • B.negative n (F.sobolevKernel W (i, x))‖ ≤ _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hηZ (i, x)) hc.2.1 (norm_nonneg _) (hZ i)
    · have hz := hsupport (i, x) (not_le.mp hx)
      constructor
      all_goals
        simp only [tested, SpatialKernelProfile.multiply, hz, zero_smul, norm_zero]
        exact mul_nonneg (hZ i) hε
  rw [htest]
  have hf := field_norm_le_of_ccr_le_cutoff
    (G.ann tested i q) (G.cre tested i q) (mul_nonneg (hZ i) hε)
    (mul_nonneg (hZ i) hε) (norm_nonneg (radiation q)) (norm_nonneg (inclusion q))
    le_rfl le_rfl
    (G.annihilation_bound tested i (Z i * ε) (mul_nonneg (hZ i) hε)
      (fun x _ => (hb x).2) q)
    (G.creation_bound tested i (Z i * ε) (mul_nonneg (hZ i) hε)
      (fun x _ => (hb x).1) q)
  apply hf.trans
  have hscale : 2 * ‖radiation q‖ + ‖inclusion q‖ ≤
      (2 * ‖radiation‖ + ‖inclusion‖) * ‖q‖ := by
    nlinarith only [radiation.le_opNorm q, inclusion.le_opNorm q]
  exact (mul_le_mul_of_nonneg_left hscale (mul_nonneg (hZ i) hε)).trans_eq (by ring)

end SpatialFieldCalculus

end FieldCalculus

end GptLean.PhotonLocalizationPhysicalKernels
