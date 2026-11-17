import GptLean.RepresentabilityCoherentRadiation
import GptLean.PhysicalFockKernelField
import GptLean.PhysicalFockFieldGraph
import GptLean.PhysicalFockRadiationField

/-!
Displacement of the radiation energy, derived from the Weyl law
(`prop-weyl-radiation`, `weyl-radiation-form-shift`).

Let `W` be a Weyl law on the photon Fock space (`Representability.ConcreteWeylLaw`),
let `f` satisfy `√ω f, ω f ∈ L²`, and let `K = (ω f, √ω f)` be the corresponding
weighted kernel. For every `u` in the radiation form domain,

`‖√H_rad W(f) u‖² = ‖√H_rad u‖² + 2 Re ⟨a(ω f) u, u⟩ + ‖√ω f‖² ‖u‖²`.

The radiation form is the sum of the annihilation forms of the shell family
`gᵢ = √ω sᵢ`, where `sᵢ = 1_{⌊ω⌋ = k} bₘ` for a Hilbert basis `bₘ`. The Weyl
law gives `a(gᵢ) W(f) u = W(f) (a(gᵢ) u + ⟨gᵢ, f⟩ u)`. The shell family is a
Parseval frame, so `∑ᵢ ⟨sᵢ, √ω f⟩ sᵢ = √ω f`. The amplitude `⟨u, a(k) u⟩` is
bounded by the inverse-frequency part of `k`, which identifies the cross term
with `⟨a(ω f) u, u⟩`. Hence `W(f)` preserves the radiation graph, with the
graph-norm bound `‖√H_rad W(f) u‖ ≤ ‖√H_rad u‖ + ‖√ω f‖ ‖u‖`, and the field
shifts by the classical field: `φ(k) W(f) = W(f) (φ(k) + 2 Re ⟨k, f⟩)`.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter Topology PhysicalFock Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Frame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem frameKernel_eq (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (i : ℕ) :
    frameKernel U i = U.toContinuousLinearMap.adjoint (lp.single 2 i 1) := by
  apply ext_inner_right ℂ
  intro y
  rw [frameKernel_inner, ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left]
  simp

theorem adjoint_isometry_apply (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (y : H) :
    U.toContinuousLinearMap.adjoint (U y) = y := by
  apply ext_inner_right ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact U.inner_map_map y z

/-- Reconstruction from an isometric analysis map. -/
theorem frame_hasSum (U : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) (y : H) :
    HasSum (fun i => ⟪frameKernel U i, y⟫_ℂ • frameKernel U i) y := by
  have h := (lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) ENNReal.ofNat_ne_top (U y)).mapL
    U.toContinuousLinearMap.adjoint
  rw [adjoint_isometry_apply] at h
  convert h using 1
  funext i
  rw [frameKernel_inner, frameKernel_eq, ← map_smul]
  congr 1
  rw [← lp.single_smul, smul_eq_mul, mul_one]

variable (s : ℕ → H) (hs : ∀ y, HasSum (fun i => ‖⟪s i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2))

omit [CompleteSpace H] in
/-- The analysis coefficients of a Parseval family. -/
def analysisVec (y : H) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun i => ⟪s i, y⟫_ℂ, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (hs y).summable)⟩

omit [CompleteSpace H] in
theorem analysisVec_norm (y : H) : ‖analysisVec s hs y‖ = ‖y‖ := by
  have h1 := coordinate_mass_hasSum (fun _ : ℕ => ℂ) (analysisVec s hs y)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1.unique (hs y))

omit [CompleteSpace H] in
/-- The analysis map of a Parseval family is an isometry into `ℓ²`. -/
def analysisMap : H →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun := analysisVec s hs
  map_add' y z := by
    apply lp.ext
    funext i
    exact inner_add_right _ _ _
  map_smul' c y := by
    apply lp.ext
    funext i
    exact inner_smul_right _ _ _
  norm_map' := analysisVec_norm s hs

theorem frameKernel_analysis (i : ℕ) : frameKernel (analysisMap s hs) i = s i :=
  ext_inner_right ℂ fun y => frameKernel_inner _ i y

include hs in
/-- **Reconstruction for a Parseval family**, `∑ᵢ ⟨sᵢ, y⟩ sᵢ = y`. -/
theorem parseval_hasSum (y : H) : HasSum (fun i => ⟪s i, y⟫_ℂ • s i) y := by
  simpa only [frameKernel_analysis] using frame_hasSum (analysisMap s hs) y

end Frame

theorem hasSum_of_ofReal {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {c : ℝ} (hc : 0 ≤ c)
    (h : ∑' i, ENNReal.ofReal (x i) = ENNReal.ofReal c) : HasSum x c := by
  have hfin : ∑' i, ENNReal.ofReal (x i) ≠ ⊤ := h ▸ ENNReal.ofReal_ne_top
  have hs : Summable x := by
    simpa only [ENNReal.toReal_ofReal (hx _)] using ENNReal.summable_toReal hfin
  have he := (ENNReal.ofReal_tsum_of_nonneg hx hs).trans h
  exact hs.hasSum_iff.mpr ((ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hx) hc).mp he)

section Multiplier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Real multipliers are symmetric. -/
theorem realL2Multiplier_inner (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |a x| ≤ B) (u v : Lp ℂ 2 μ) :
    ⟪PhotonLocalization.realL2Multiplier a ha B hb u, v⟫_ℂ =
      ⟪u, PhotonLocalization.realL2Multiplier a ha B hb v⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [PhotonLocalization.realL2Multiplier_apply a ha B hb u,
    PhotonLocalization.realL2Multiplier_apply a ha B hb v] with x hu hv
  rw [hu, hv]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal]

theorem realL2Multiplier_adjoint (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |a x| ≤ B) :
    (PhotonLocalization.realL2Multiplier (K := ℂ) a ha B hb).adjoint =
      PhotonLocalization.realL2Multiplier a ha B hb :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (realL2Multiplier_inner a ha B hb)).symm

end Multiplier

section Shells

/-- The indicator of the frequency shell `⌊ω⌋ = k`. -/
def shellIndicator (k : ℕ) (p : PhotonMode) : ℝ :=
  if ⌊photonDispersion p⌋₊ = k then 1 else 0

theorem shellIndicator_measurable (k : ℕ) : Measurable (shellIndicator k) :=
  Measurable.ite (measurableSet_eq_fun photonDispersion_measurable.nat_floor measurable_const)
    measurable_const measurable_const

theorem shellIndicator_bound (k : ℕ) (p : PhotonMode) : |shellIndicator k p| ≤ 1 := by
  unfold shellIndicator
  split_ifs <;> simp

/-- Multiplication by the shell indicator. -/
def shellCut (k : ℕ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  PhotonLocalization.realL2Multiplier (shellIndicator k)
    (shellIndicator_measurable k).aestronglyMeasurable 1 (ae_of_all _ (shellIndicator_bound k))

theorem shellCut_ae (k : ℕ) (y : Lp ℂ 2 photonMeasure) :
    shellCut k y =ᵐ[photonMeasure] fun p => shellIndicator k p • y p :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ y

theorem shellCut_inner (k : ℕ) (x y : Lp ℂ 2 photonMeasure) :
    ⟪shellCut k x, y⟫_ℂ = ⟪x, shellCut k y⟫_ℂ :=
  realL2Multiplier_inner _ _ _ _ x y

theorem shell_adjoint (k : ℕ) : (photonRadiationShell k).adjoint = photonRadiationShell k :=
  realL2Multiplier_adjoint (RadiationShells.weight photonDispersion k)
    (RadiationShells.weight_measurable photonDispersion photonDispersion_measurable k).aestronglyMeasurable
    (Real.sqrt (k + 1 : ℝ)) (ae_of_all photonMeasure (RadiationShells.weight_bound photonDispersion k))

theorem shellIndicator_square_sum (p : PhotonMode) :
    (∑' k, ENNReal.ofReal (shellIndicator k p ^ 2)) = 1 := by
  rw [tsum_eq_single ⌊photonDispersion p⌋₊]
  · simp [shellIndicator]
  · intro k hk
    simp [shellIndicator, Ne.symm hk]

theorem lintegral_norm_sq (y : Lp ℂ 2 photonMeasure) :
    ∫⁻ p, ENNReal.ofReal (‖y p‖ ^ 2) ∂photonMeasure = ENNReal.ofReal (‖y‖ ^ 2) := by
  have hn := Repair.toL2_norm_sq (Lp.memLp y)
  simp only [Lp.toLp_coeFn] at hn
  rw [hn, ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
    (ae_of_all _ fun x => sq_nonneg _)]

theorem shellCut_norm_sq (k : ℕ) (y : Lp ℂ 2 photonMeasure) :
    ENNReal.ofReal (‖shellCut k y‖ ^ 2) =
      ∫⁻ p, ENNReal.ofReal (shellIndicator k p ^ 2) * ENNReal.ofReal (‖y p‖ ^ 2) ∂photonMeasure := by
  rw [← lintegral_norm_sq]
  apply lintegral_congr_ae
  filter_upwards [shellCut_ae k y] with p hp
  rw [hp, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]

/-- The shell family `sᵢ = 1_{⌊ω⌋ = k} bₘ`, `i = ⟨k, m⟩`. -/
def sFamily (i : ℕ) : Lp ℂ 2 photonMeasure := shellCut i.unpair.1 (numberFamily i.unpair.2)

theorem sFamily_inner (i : ℕ) (y : Lp ℂ 2 photonMeasure) :
    ⟪sFamily i, y⟫_ℂ = ⟪numberFamily i.unpair.2, shellCut i.unpair.1 y⟫_ℂ :=
  shellCut_inner _ _ _

/-- **The shell family is a Parseval frame.** -/
theorem sFamily_parseval (y : Lp ℂ 2 photonMeasure) :
    HasSum (fun i => ‖⟪sFamily i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  apply hasSum_of_ofReal (fun _ => sq_nonneg _) (sq_nonneg _)
  calc ∑' i, ENNReal.ofReal (‖⟪sFamily i, y⟫_ℂ‖ ^ 2)
      = ∑' i, ENNReal.ofReal (‖⟪numberFamily i.unpair.2, shellCut i.unpair.1 y⟫_ℂ‖ ^ 2) :=
        tsum_congr fun i => by rw [sFamily_inner]
    _ = ∑' p : ℕ × ℕ, ENNReal.ofReal (‖⟪numberFamily p.2, shellCut p.1 y⟫_ℂ‖ ^ 2) :=
        Nat.pairEquiv.symm.tsum_eq
          (fun p : ℕ × ℕ => ENNReal.ofReal (‖⟪numberFamily p.2, shellCut p.1 y⟫_ℂ‖ ^ 2))
    _ = ∑' k, ∑' m, ENNReal.ofReal (‖⟪numberFamily m, shellCut k y⟫_ℂ‖ ^ 2) :=
        ENNReal.tsum_prod'
    _ = ∑' k, ENNReal.ofReal (‖shellCut k y‖ ^ 2) :=
        tsum_congr fun k => numberFamily_value _
    _ = ∑' k, ∫⁻ p, ENNReal.ofReal (shellIndicator k p ^ 2) *
          ENNReal.ofReal (‖y p‖ ^ 2) ∂photonMeasure :=
        tsum_congr fun k => shellCut_norm_sq k y
    _ = ∫⁻ p, ∑' k, ENNReal.ofReal (shellIndicator k p ^ 2) *
          ENNReal.ofReal (‖y p‖ ^ 2) ∂photonMeasure :=
        (lintegral_tsum fun k => ((shellIndicator_measurable k).pow_const 2).ennreal_ofReal
          |>.aemeasurable.mul ((Lp.aestronglyMeasurable y).norm.pow 2).aemeasurable.ennreal_ofReal).symm
    _ = ∫⁻ p, ENNReal.ofReal (‖y p‖ ^ 2) ∂photonMeasure :=
        lintegral_congr fun p => by rw [ENNReal.tsum_mul_right, shellIndicator_square_sum, one_mul]
    _ = ENNReal.ofReal (‖y‖ ^ 2) := lintegral_norm_sq y

theorem sFamily_hasSum (y : Lp ℂ 2 photonMeasure) :
    HasSum (fun i => ⟪sFamily i, y⟫_ℂ • sFamily i) y :=
  parseval_hasSum sFamily sFamily_parseval y

theorem radiationFamily_eq (i : ℕ) :
    radiationFamily i = photonRadiationShell i.unpair.1 (numberFamily i.unpair.2) := by
  change (photonRadiationShell i.unpair.1).adjoint (numberFamily i.unpair.2) = _
  rw [shell_adjoint]

theorem radiationFamily_weighted (i : ℕ) :
    ∀ᵐ p ∂photonMeasure, radiationFamily i p = (Real.sqrt ‖p.1‖ : ℂ) * sFamily i p := by
  filter_upwards [RadiationShells.multiplier_ae photonMeasure photonDispersion
      photonDispersion_measurable i.unpair.1 (numberFamily i.unpair.2),
    shellCut_ae i.unpair.1 (numberFamily i.unpair.2)] with p h1 h2
  have he : radiationFamily i p =
      RadiationShells.weight photonDispersion i.unpair.1 p • (numberFamily i.unpair.2) p := by
    rw [radiationFamily_eq]
    exact h1
  change radiationFamily i p = (Real.sqrt ‖p.1‖ : ℂ) * shellCut i.unpair.1 (numberFamily i.unpair.2) p
  rw [he, h2]
  unfold RadiationShells.weight shellIndicator
  split_ifs <;> simp [Complex.real_smul, photonDispersion]

/-- The weighted kernel `(gᵢ, sᵢ)` of the shell family. -/
def shellKernel (i : ℕ) : WeightedPhotonKernel :=
  ⟨(radiationFamily i, sFamily i), radiationFamily_weighted i⟩

end Shells

section Amplitude

theorem kernelAnnihilation_smul (c : ℂ) (k : WeightedPhotonKernel) :
    kernelAnnihilation (c • k) = starRingEnd ℂ c • kernelAnnihilation k := by
  apply ContinuousLinearMap.ext
  intro q
  apply lp.ext
  funext n
  change annihilationSector photonMeasure n (c • k.val.1) (radiationGraphInclusion q (n + 1)) =
    starRingEnd ℂ c • annihilationSector photonMeasure n k.val.1 (radiationGraphInclusion q (n + 1))
  rw [annihilationSector_smul]
  rfl

/-- The coherent amplitude `⟨u, a(k₁) u⟩` of a radiation-graph vector. -/
def amplitude (q : RadiationGraphSpace) (k : WeightedPhotonKernel) : ℂ :=
  ⟪radiationGraphInclusion q, kernelAnnihilation k q⟫_ℂ

theorem amplitude_add (q : RadiationGraphSpace) (k l : WeightedPhotonKernel) :
    amplitude q (k + l) = amplitude q k + amplitude q l := by
  unfold amplitude
  rw [kernelAnnihilation_add]
  exact inner_add_right _ _ _

theorem amplitude_smul (q : RadiationGraphSpace) (c : ℂ) (k : WeightedPhotonKernel) :
    amplitude q (c • k) = starRingEnd ℂ c * amplitude q k := by
  unfold amplitude
  rw [kernelAnnihilation_smul]
  exact inner_smul_right _ _ _

theorem kernelAnnihilation_norm_le (k : WeightedPhotonKernel) (q : RadiationGraphSpace) :
    ‖kernelAnnihilation k q‖ ≤ ‖k.val.2‖ * ‖radiationGraphDerivative q‖ :=
  annihilationRadiation_norm_le k.val.1 k.val.2 k.property q

theorem amplitude_norm_le (q : RadiationGraphSpace) (k : WeightedPhotonKernel) :
    ‖amplitude q k‖ ≤
      ‖radiationGraphInclusion q‖ * ‖radiationGraphDerivative q‖ * ‖k.val.2‖ := by
  refine (norm_inner_le_norm _ _).trans ?_
  calc ‖radiationGraphInclusion q‖ * ‖kernelAnnihilation k q‖
      ≤ ‖radiationGraphInclusion q‖ * (‖k.val.2‖ * ‖radiationGraphDerivative q‖) :=
        mul_le_mul_of_nonneg_left (kernelAnnihilation_norm_le k q) (norm_nonneg _)
    _ = _ := by ring

/-- The amplitude as an additive map of the kernel. -/
def amplitudeHom (q : RadiationGraphSpace) : WeightedPhotonKernel →+ ℂ where
  toFun := amplitude q
  map_zero' := by simpa using amplitude_smul q 0 0
  map_add' := amplitude_add q

/-- The amplitude is continuous in the inverse-frequency part of the kernel. -/
theorem amplitude_hasSum (q : RadiationGraphSpace) (K : WeightedPhotonKernel)
    (x : ℕ → WeightedPhotonKernel) (hx : HasSum (fun i => (x i).val.2) K.val.2) :
    HasSum (fun i => amplitude q (x i)) (amplitude q K) := by
  have hsum : ∀ s : Finset ℕ, ∑ i ∈ s, amplitude q (x i) = amplitude q (∑ i ∈ s, x i) :=
    fun s => (map_sum (amplitudeHom q) x s).symm
  have hval : ∀ s : Finset ℕ, (∑ i ∈ s, x i).val.2 = ∑ i ∈ s, (x i).val.2 := fun s => by
    rw [Submodule.coe_sum, Prod.snd_sum]
  unfold HasSum at hx ⊢
  rw [tendsto_iff_norm_sub_tendsto_zero] at hx ⊢
  have hB := hx.const_mul (‖radiationGraphInclusion q‖ * ‖radiationGraphDerivative q‖)
  rw [mul_zero] at hB
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hB
  calc ‖∑ i ∈ s, amplitude q (x i) - amplitude q K‖
      = ‖amplitude q (∑ i ∈ s, x i - K)‖ := by
        rw [hsum]
        exact congrArg norm (map_sub (amplitudeHom q) _ _).symm
    _ ≤ ‖radiationGraphInclusion q‖ * ‖radiationGraphDerivative q‖ *
          ‖(∑ i ∈ s, x i - K).val.2‖ := amplitude_norm_le q _
    _ = ‖radiationGraphInclusion q‖ * ‖radiationGraphDerivative q‖ *
          ‖∑ i ∈ s, (x i).val.2 - K.val.2‖ := by
        rw [Submodule.coe_sub, Prod.snd_sub, hval]

end Amplitude

section Weyl

variable (W : ConcreteWeylLaw photonMeasure) {f : Lp ℂ 2 photonMeasure}
  (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

include hK in
theorem radiationFamily_inner (i : ℕ) : ⟪radiationFamily i, f⟫_ℂ = ⟪sFamily i, K.val.2⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radiationFamily_weighted i, hK] with p h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

include hK in
/-- The cross term of the displaced radiation form. -/
theorem cross_hasSum (q : RadiationGraphSpace) :
    HasSum (fun i => ⟪radiationFamily i, f⟫_ℂ *
        ⟪kernelAnnihilation (shellKernel i) q, radiationGraphInclusion q⟫_ℂ)
      ⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ := by
  have h := (amplitude_hasSum q K (fun i => ⟪sFamily i, K.val.2⟫_ℂ • shellKernel i)
    (sFamily_hasSum K.val.2)).star
  convert h using 1
  · funext i
    rw [amplitude_smul, star_mul', amplitude, radiationFamily_inner K hK]
    simp only [starRingEnd_apply, star_star]
    rw [← starRingEnd_apply, inner_conj_symm]
  · rw [amplitude, ← starRingEnd_apply, inner_conj_symm]

/-- `‖v + c u‖² = ‖v‖² + 2 Re (c ⟨v, u⟩) + |c|² ‖u‖²`. -/
theorem norm_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v u : E) (c : ℂ) :
    ‖v + c • u‖ ^ 2 = ‖v‖ ^ 2 + 2 * (c * ⟪v, u⟫_ℂ).re + ‖c‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow, RCLike.re_to_complex]

include hK in
/-- The displaced radiation form as a real series. -/
theorem weyl_radiation_hasSum (q : RadiationGraphSpace) :
    HasSum (fun i => ‖kernelAnnihilation (shellKernel i) q‖ ^ 2 +
        2 * (⟪radiationFamily i, f⟫_ℂ *
          ⟪kernelAnnihilation (shellKernel i) q, radiationGraphInclusion q⟫_ℂ).re +
        ‖⟪radiationFamily i, f⟫_ℂ‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2)
      (‖radiationGraphDerivative q‖ ^ 2 +
        2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2) := by
  have hgraph : ∀ i, AnnihilationGraph photonMeasure (radiationFamily i)
      (radiationGraphInclusion q) (kernelAnnihilation (shellKernel i) q) := fun i n => rfl
  have hv : HasSum (fun i => ‖kernelAnnihilation (shellKernel i) q‖ ^ 2)
      (‖radiationGraphDerivative q‖ ^ 2) := by
    apply hasSum_of_ofReal (fun _ => sq_nonneg _) (sq_nonneg _)
    rw [← radiationGraph_energy, ← sum_annihilationForm_eq_radiationForm]
    exact tsum_congr fun i => (AnnihilationGraph.form_eq photonMeasure (hgraph i)).symm
  have hc : HasSum (fun i => ‖⟪radiationFamily i, f⟫_ℂ‖ ^ 2) (‖K.val.2‖ ^ 2) := by
    simpa only [radiationFamily_inner K hK] using sFamily_parseval K.val.2
  exact (hv.add ((Complex.hasSum_re (cross_hasSum K hK q)).mul_left 2)).add
    (hc.mul_right (‖radiationGraphInclusion q‖ ^ 2))

theorem weyl_term_nonneg (q : RadiationGraphSpace) (i : ℕ) :
    0 ≤ ‖kernelAnnihilation (shellKernel i) q‖ ^ 2 +
        2 * (⟪radiationFamily i, f⟫_ℂ *
          ⟪kernelAnnihilation (shellKernel i) q, radiationGraphInclusion q⟫_ℂ).re +
        ‖⟪radiationFamily i, f⟫_ℂ‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
  le_of_le_of_eq (sq_nonneg _) (norm_add_smul_sq _ _ _)

include hK in
/-- **`weyl-radiation-form-shift`.** -/
theorem radiationForm_weyl (q : RadiationGraphSpace) :
    radiationForm (W.weyl f (radiationGraphInclusion q)) = ENNReal.ofReal
      (‖radiationGraphDerivative q‖ ^ 2 +
        2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2) := by
  have hgraph : ∀ i, AnnihilationGraph photonMeasure (radiationFamily i)
      (radiationGraphInclusion q) (kernelAnnihilation (shellKernel i) q) := fun i n => rfl
  have hshift : ∀ i, annihilationForm photonMeasure (radiationFamily i)
      (W.weyl f (radiationGraphInclusion q)) = ENNReal.ofReal
        (‖kernelAnnihilation (shellKernel i) q +
          ⟪radiationFamily i, f⟫_ℂ • radiationGraphInclusion q‖ ^ 2) := fun i =>
    (AnnihilationGraph.form_eq photonMeasure (W.annihilation_shift f _ _ _ (hgraph i))).trans
      (congrArg (fun z : ℝ => ENNReal.ofReal (z ^ 2)) (LinearIsometryEquiv.norm_map _ _))
  have htot := weyl_radiation_hasSum K hK q
  calc radiationForm (W.weyl f (radiationGraphInclusion q))
      = ∑' i, annihilationForm photonMeasure (radiationFamily i)
          (W.weyl f (radiationGraphInclusion q)) :=
        (sum_annihilationForm_eq_radiationForm _).symm
    _ = ∑' i, ENNReal.ofReal (‖kernelAnnihilation (shellKernel i) q‖ ^ 2 +
          2 * (⟪radiationFamily i, f⟫_ℂ *
            ⟪kernelAnnihilation (shellKernel i) q, radiationGraphInclusion q⟫_ℂ).re +
          ‖⟪radiationFamily i, f⟫_ℂ‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2) :=
        tsum_congr fun i => (hshift i).trans (congrArg ENNReal.ofReal (norm_add_smul_sq _ _ _))
    _ = ENNReal.ofReal (∑' i, (‖kernelAnnihilation (shellKernel i) q‖ ^ 2 +
          2 * (⟪radiationFamily i, f⟫_ℂ *
            ⟪kernelAnnihilation (shellKernel i) q, radiationGraphInclusion q⟫_ℂ).re +
          ‖⟪radiationFamily i, f⟫_ℂ‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (weyl_term_nonneg q) htot.summable).symm
    _ = _ := congrArg ENNReal.ofReal htot.tsum_eq

include hK in
theorem weyl_radiation_nonneg (q : RadiationGraphSpace) :
    0 ≤ ‖radiationGraphDerivative q‖ ^ 2 +
        2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
  (weyl_radiation_hasSum K hK q).nonneg (weyl_term_nonneg q)

include hK in
theorem weyl_mem_domain (q : RadiationGraphSpace) :
    W.weyl f (radiationGraphInclusion q) ∈ radiationRoot.domain := by
  apply (radiationRoot_domain_iff_finite _).mpr
  rw [radiationForm_weyl W K hK q]
  exact ENNReal.ofReal_lt_top

/-- The displaced graph element. -/
def weylGraphFun (q : RadiationGraphSpace) : RadiationGraphSpace :=
  ⟨(W.weyl f (radiationGraphInclusion q), radiationRoot ⟨_, weyl_mem_domain W K hK q⟩),
    radiationRoot.mem_graph ⟨_, weyl_mem_domain W K hK q⟩⟩

theorem weylGraphFun_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylGraphFun W K hK q)‖ ^ 2 =
      ‖radiationGraphDerivative q‖ ^ 2 +
        2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 := by
  have h := (radiationRoot_energy ⟨_, weyl_mem_domain W K hK q⟩).symm.trans
    (radiationForm_weyl W K hK q)
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (weyl_radiation_nonneg K hK q)).mp h

theorem weylGraphFun_derivative_le (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylGraphFun W K hK q)‖ ≤
      ‖radiationGraphDerivative q‖ + ‖K.val.2‖ * ‖radiationGraphInclusion q‖ := by
  have hre : (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re ≤
      ‖K.val.2‖ * ‖radiationGraphDerivative q‖ * ‖radiationGraphInclusion q‖ :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (kernelAnnihilation_norm_le K q) (norm_nonneg _)))
  have hsq : ‖radiationGraphDerivative (weylGraphFun W K hK q)‖ ^ 2 ≤
      (‖radiationGraphDerivative q‖ + ‖K.val.2‖ * ‖radiationGraphInclusion q‖) ^ 2 := by
    rw [weylGraphFun_derivative_norm_sq]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem weylGraphFun_add (q r : RadiationGraphSpace) :
    weylGraphFun W K hK (q + r) = weylGraphFun W K hK q + weylGraphFun W K hK r := by
  have hx : W.weyl f (radiationGraphInclusion (q + r)) =
      W.weyl f (radiationGraphInclusion q) + W.weyl f (radiationGraphInclusion r) :=
    (congrArg (W.weyl f) (map_add radiationGraphInclusion q r)).trans (map_add _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, weyl_mem_domain W K hK (q + r)⟩ =
      radiationRoot ⟨_, weyl_mem_domain W K hK q⟩ + radiationRoot ⟨_, weyl_mem_domain W K hK r⟩
    rw [← LinearPMap.map_add]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem weylGraphFun_smul (a : ℂ) (q : RadiationGraphSpace) :
    weylGraphFun W K hK (a • q) = a • weylGraphFun W K hK q := by
  have hx : W.weyl f (radiationGraphInclusion (a • q)) =
      a • W.weyl f (radiationGraphInclusion q) :=
    (congrArg (W.weyl f) (map_smul radiationGraphInclusion a q)).trans (map_smul _ _ _)
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · change radiationRoot ⟨_, weyl_mem_domain W K hK (a • q)⟩ =
      a • radiationRoot ⟨_, weyl_mem_domain W K hK q⟩
    rw [← LinearPMap.map_smul]
    exact congrArg radiationRoot (Subtype.ext hx)

theorem weylGraphFun_norm_le (q : RadiationGraphSpace) :
    ‖weylGraphFun W K hK q‖ ≤ (1 + ‖K.val.2‖) * ‖q‖ := by
  have hq1 : ‖radiationGraphInclusion q‖ ≤ ‖q‖ := norm_fst_le q.val
  have hq2 : ‖radiationGraphDerivative q‖ ≤ ‖q‖ := norm_snd_le q.val
  have hk := norm_nonneg K.val.2
  have h1 : ‖radiationGraphInclusion (weylGraphFun W K hK q)‖ ≤ (1 + ‖K.val.2‖) * ‖q‖ := by
    change ‖W.weyl f (radiationGraphInclusion q)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg q]
  have h2 : ‖radiationGraphDerivative (weylGraphFun W K hK q)‖ ≤ (1 + ‖K.val.2‖) * ‖q‖ := by
    refine (weylGraphFun_derivative_le W K hK q).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hq1 hk]
  change max ‖radiationGraphInclusion (weylGraphFun W K hK q)‖
    ‖radiationGraphDerivative (weylGraphFun W K hK q)‖ ≤ _
  exact max_le h1 h2

/-- **`W(f)` on the radiation graph.** -/
def weylGraph : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  LinearMap.mkContinuous
    { toFun := weylGraphFun W K hK
      map_add' := weylGraphFun_add W K hK
      map_smul' := weylGraphFun_smul W K hK }
    (1 + ‖K.val.2‖) (weylGraphFun_norm_le W K hK)

theorem weylGraph_inclusion (q : RadiationGraphSpace) :
    radiationGraphInclusion (weylGraph W K hK q) = W.weyl f (radiationGraphInclusion q) := rfl

theorem weylGraph_derivative_norm_sq (q : RadiationGraphSpace) :
    ‖radiationGraphDerivative (weylGraph W K hK q)‖ ^ 2 =
      ‖radiationGraphDerivative q‖ ^ 2 +
        2 * (⟪kernelAnnihilation K q, radiationGraphInclusion q⟫_ℂ).re +
        ‖K.val.2‖ ^ 2 * ‖radiationGraphInclusion q‖ ^ 2 :=
  weylGraphFun_derivative_norm_sq W K hK q

/-- **The field shifts by the classical field**,
`φ(k) W(f) u = W(f) (φ(k) u + 2 Re ⟨k₁, f⟩ u)`. -/
theorem kernelField_weylGraph (C : CanonicalSectorCCR photonMeasure) (k : WeightedPhotonKernel)
    (q : RadiationGraphSpace) :
    kernelField C k (weylGraph W K hK q) = W.weyl f (kernelField C k q +
      ((2 * (⟪k.val.1, f⟫_ℂ).re : ℝ) : ℂ) • radiationGraphInclusion q) := by
  have h1 := kernelField_segalGraph C k (weylGraph W K hK q)
  have h2 := W.field_shift f k.val.1 _ _ (kernelField_segalGraph C k q)
  apply lp.ext
  funext n
  exact (h1 n).trans (h2 n).symm

end Weyl

end GptLean.PhysicalWeyl
