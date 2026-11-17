import GptLean.PhysicalPFVacuumInsertion
import GptLean.PhysicalFockHardField
import GptLean.PhysicalPFDomain

/-!
The vacuum energy and current calculation on the actual PF reference domain.
An orthogonal hard/soft kernel decomposition gives the exact extra kinetic
energy. Radiation and the potential use the same reference vector. The hard
normal form is the pullback of the actual hard-kernel PF form along insertion.
-/

noncomputable section

namespace GptLean.PhysicalPFVacuumEnergy

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalPFVacuumInsertion PhysicalPFSource RemovalState
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section General

variable {I H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]

/-- Weak derivatives stay in every closed fiber subspace containing the value. -/
theorem derivative_mem_subspace (W : Submodule ℂ H) [CompleteSpace W]
    (u : ElectronicH1Complex.ComplexH1 H I)
    (hu : ∀ᵐ x ∂volume, ElectronicH1Complex.value u x ∈ W) (i : I) :
    ∀ᵐ x ∂volume, ElectronicH1Complex.derivative i u x ∈ W := by
  have he : ElectronicH1Map.map W.starProjection u = u := by
    apply ElectronicH1Complex.value_injective
    apply Lp.ext
    filter_upwards [W.starProjection.coeFn_compLpL (ElectronicH1Complex.value u), hu]
      with x hx hu
    exact hx.trans (W.starProjection_eq_self_iff.mpr hu)
  have hd := congrArg (ElectronicH1Complex.derivative i) he
  filter_upwards [W.starProjection.coeFn_compLpL (ElectronicH1Complex.derivative i u)]
    with x hx
  have hv := congrArg (fun v => v x) hd
  exact W.starProjection_eq_self_iff.mp (hx.symm.trans hv)

end General

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem orthogonal_sub_norm_sq (u v : H) (h : ⟪u, v⟫_ℂ = 0) (e : ℝ) :
    ‖u - (e : ℂ) • v‖ ^ 2 = ‖u‖ ^ 2 + e ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, h, mul_zero, map_zero,
    mul_zero, sub_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

end Hilbert

section L2Sum

variable {X H J : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem complex_l2_norm_sq_integral (u : Lp H 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  exact PhotonKernelLocalization.l2_norm_sq_eq_integral u

private theorem sum_l2_norm_sq_le (d : J → Lp H 2 μ) (ψ : Lp H 2 μ) (σ : ℝ)
    (h : ∀ᵐ x ∂μ, ∑ j, ‖d j x‖ ^ 2 ≤ σ * ‖ψ x‖ ^ 2) :
    (∑ j, ‖d j‖ ^ 2) ≤ σ * ‖ψ‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  have hd (j : J) : Integrable (fun x => ‖d j x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (d j))).mp (Lp.memLp (d j))
  have hψ : Integrable (fun x => ‖ψ x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ)
  calc
    _ = ∫ x, ∑ j, ‖d j x‖ ^ 2 ∂μ := by
      simp_rw [PhotonKernelLocalization.l2_norm_sq_eq_integral]
      exact (integral_finsetSum Finset.univ (fun j _ => hd j)).symm
    _ ≤ ∫ x, σ * ‖ψ x‖ ^ 2 ∂μ :=
      integral_mono_ae (integrable_finsetSum Finset.univ (fun j _ => hd j)) (hψ.const_mul σ) h
    _ = _ := by rw [integral_const_mul, ← PhotonKernelLocalization.l2_norm_sq_eq_integral]

end L2Sum

section Pullback

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : StandardNormalTraceBackground)

/-- Pullback through the ordinary trace-ideal action of a bounded map. -/
def pullbackForm (J : H →L[ℂ] K) (E : PositiveForm (B.traceData (H := K))) :
    PositiveForm (B.traceData (H := H)) where
  truncation n := (E.truncation n).comp (B.push J)
  nonneg n _ hx := E.nonneg n _ (B.push_positive J hx)
  monotone _ hx := E.monotone _ (B.push_positive J hx)

theorem pullbackForm_expectation (J : H →L[ℂ] K)
    (E : PositiveForm (B.traceData (H := K))) (x : B.Trace H) :
    (pullbackForm B J E).expectation x = E.expectation (B.push J x) := rfl

theorem pullbackForm_rankOne (J : H →L[ℂ] K)
    (E : PositiveForm (B.traceData (H := K))) (v : H) :
    (pullbackForm B J E).expectation ((B.realization H).rank.rankOne v) =
      E.expectation ((B.realization K).rank.rankOne (J v)) := by
  rw [pullbackForm_expectation, B.push_rankOne]

private theorem pullbackForm_rankOne_isometry (J : H →ₗᵢ[ℂ] K)
    (E : PositiveForm (B.traceData (H := K))) (v : H) :
    (pullbackForm B J.toContinuousLinearMap E).expectation
        ((B.realization H).rank.rankOne v) =
      E.expectation ((B.realization K).rank.rankOne (J v)) :=
  pullbackForm_rankOne B J.toContinuousLinearMap E v

/-- The ordinary trace push also transports every finite-form observable. -/
def pullbackObservable (J : H →L[ℂ] K) (E : PositiveForm (B.traceData (H := K)))
    (O : FormObservable E) : FormObservable (pullbackForm B J E) where
  approximation n := (O.approximation n).comp (B.push J)
  value x := O.value (B.push J x)
  converges _x hx he := O.converges _ (B.push_positive J hx) he

theorem pullbackObservable_value (J : H →L[ℂ] K)
    (E : PositiveForm (B.traceData (H := K))) (O : FormObservable E) (x : B.Trace H) :
    (pullbackObservable B J E O).value x = O.value (B.push J x) := rfl

theorem pullbackObservable_rankOne (J : H →L[ℂ] K)
    (E : PositiveForm (B.traceData (H := K))) (O : FormObservable E) (v : H) :
    (pullbackObservable B J E O).value ((B.realization H).rank.rankOne v) =
      O.value ((B.realization K).rank.rankOne (J v)) := by
  rw [pullbackObservable_value, B.push_rankOne]

end Pullback

section RepresentativeTransport

variable {X E H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private theorem compLpL_ae_of_eq (L : E →L[ℂ] H) (q : Lp E 2 μ)
    (v : Lp H 2 μ) (h : L.compLpL 2 μ q = v) :
    v =ᵐ[μ] fun x => L (q x) := by
  have he := L.coeFn_compLpL q
  rw [h] at he
  exact he

private theorem ae_smul_sub_smul_mem (W : Submodule ℂ H)
    (a b : Lp H 2 μ) (ha : ∀ᵐ x ∂μ, a x ∈ W) (hb : ∀ᵐ x ∂μ, b x ∈ W)
    (c d : ℂ) : ∀ᵐ x ∂μ, (c • a - d • b) x ∈ W := by
  filter_upwards [ha, hb, Lp.coeFn_smul c a, Lp.coeFn_smul d b,
    Lp.coeFn_sub (c • a) (d • b)] with x ha hb hc hd hsub
  rw [hsub, Pi.sub_apply, hc, hd, Pi.smul_apply, Pi.smul_apply]
  exact W.sub_mem (W.smul_mem _ ha) (W.smul_mem _ hb)

end RepresentativeTransport

section Reference

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (W : Submodule ℂ (Lp ℂ 2 photonMeasure))

theorem reference_radiation_ae (u : Reference I V) :
    inclusion I V u =ᵐ[volume] fun x => radiationGraphInclusion (radiationSource I V u x) :=
  compLpL_ae_of_eq radiationGraphInclusion (radiationSource I V u) (inclusion I V u)
    (radiation_matches I V u)

theorem reference_radiation_mem (u : Reference I V)
    (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W) :
    ∀ᵐ x ∂volume, radiationGraphInclusion (radiationSource I V u x) ∈ generatedFockSubspace W := by
  filter_upwards [reference_radiation_ae I V u, hu] with x hx hu
  exact hx ▸ hu

variable (k : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ M)

theorem reference_field_mem
    (hW : ∀ i, ∀ᵐ x ∂volume, (k i x).val.1 ∈ W)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (i : I) : ∀ᵐ x ∂volume, field I V C k hk M hM i u x ∈ generatedFockSubspace W := by
  filter_upwards [spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V u),
    reference_radiation_mem I V W u hu, hW i] with x hx hq hw
  exact hx.symm ▸ kernelField_mem_generated C W (k i x) hw (radiationSource I V u x) hq

theorem reference_covariant_mem
    (hW : ∀ i, ∀ᵐ x ∂volume, (k i x).val.1 ∈ W)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, covariant I V C k hk M hM e i u x ∈ generatedFockSubspace W := by
  have hd : ∀ᵐ x ∂volume, ordinary I V i u x ∈ generatedFockSubspace W :=
    derivative_mem_subspace (generatedFockSubspace W) (electronic I V u) hu i
  have h := ae_smul_sub_smul_mem (generatedFockSubspace W)
    (ordinary I V i u) (field I V C k hk M hM i u) hd
    (reference_field_mem I V C W k hk M hM hW u hu i) (-Complex.I) (e : ℂ)
  exact (congrArg (fun z : WaveSpace I => ∀ᵐ x ∂volume, z x ∈ generatedFockSubspace W)
    (covariant_apply I V C k hk M hM e i u)).mpr h

theorem reference_soft_inner
    (hW : ∀ i, ∀ᵐ x ∂volume, (k i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (v : WaveSpace I) (hv : ∀ᵐ x ∂volume, v x ∈ generatedFockSubspace W) (i : I) :
    ∀ᵐ x ∂volume, ⟪v x, field I V C k hk M hM i u x⟫_ℂ = 0 := by
  filter_upwards [spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V u),
    reference_radiation_mem I V W u hu, hW i, hv] with x hx hq hw hv
  have hinner : ⟪v x, field I V C k hk M hM i u x⟫_ℂ =
      ⟪v x, kernelField C (k i x) (radiationSource I V u x)⟫_ℂ :=
    congrArg (fun w : PhotonFock => inner ℂ (v x) w) hx
  exact hinner.trans (kernelField_inner_eq_zero_of_orthogonal C W (k i x) hw
    (radiationSource I V u x) hq (v x) hv)

theorem reference_soft_norm_sq
    (hW : ∀ i, ∀ᵐ x ∂volume, (k i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W) (i : I) :
    ‖field I V C k hk M hM i u‖ ^ 2 =
      ∫ x, ‖(k i x).val.1‖ ^ 2 * ‖inclusion I V u x‖ ^ 2 := by
  refine (complex_l2_norm_sq_integral (H := PhotonFock)
    (μ := volume) (field I V C k hk M hM i u)).trans ?_
  apply integral_congr_ae
  have he := reference_radiation_ae I V u
  filter_upwards [spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V u),
    reference_radiation_mem I V W u hu, hW i, he] with x hx hq hw he
  have hfield : ‖field I V C k hk M hM i u x‖ ^ 2 =
      ‖kernelField C (k i x) (radiationSource I V u x)‖ ^ 2 :=
    congrArg (fun w : PhotonFock => ‖w‖ ^ 2) hx
  have hvalue : ‖radiationGraphInclusion (radiationSource I V u x)‖ ^ 2 =
      ‖inclusion I V u x‖ ^ 2 :=
    congrArg (fun w : PhotonFock => ‖w‖ ^ 2) he.symm
  exact hfield.trans ((kernelField_norm_sq_of_orthogonal C W (k i x) hw
    (radiationSource I V u x) hq).trans
      (congrArg (fun r : ℝ => ‖(k i x).val.1‖ ^ 2 * r) hvalue))

theorem reference_soft_sum_le
    (hW : ∀ i, ∀ᵐ x ∂volume, (k i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (σ : ℝ) (hσ : ∀ᵐ x ∂volume, ∑ i, ‖(k i x).val.1‖ ^ 2 ≤ σ) :
    (∑ i, ‖field I V C k hk M hM i u‖ ^ 2) ≤ σ * ‖inclusion I V u‖ ^ 2 := by
  apply sum_l2_norm_sq_le
  have he := reference_radiation_ae I V u
  filter_upwards [ae_all_iff.mpr (fun i =>
      spatialField_ae volume C (k i) (hk i) M (hM i) (radiationSource I V u)),
    reference_radiation_mem I V W u hu, ae_all_iff.mpr hW, he, hσ]
    with x hx hq hw he hσ
  calc
    _ = ∑ i, ‖(k i x).val.1‖ ^ 2 * ‖inclusion I V u x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hfield : ‖field I V C k hk M hM i u x‖ ^ 2 =
          ‖kernelField C (k i x) (radiationSource I V u x)‖ ^ 2 :=
        congrArg (fun w : PhotonFock => ‖w‖ ^ 2) (hx i)
      have hvalue : ‖radiationGraphInclusion (radiationSource I V u x)‖ ^ 2 =
          ‖inclusion I V u x‖ ^ 2 :=
        congrArg (fun w : PhotonFock => ‖w‖ ^ 2) he.symm
      exact hfield.trans ((kernelField_norm_sq_of_orthogonal C W (k i x) (hw i)
        (radiationSource I V u x) hq).trans
          (congrArg (fun r : ℝ => ‖(k i x).val.1‖ ^ 2 * r) hvalue))
    _ = (∑ i, ‖(k i x).val.1‖ ^ 2) * ‖inclusion I V u x‖ ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hσ (sq_nonneg _)

end Reference

private theorem lp_eq_add_of_ae {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} (u v w : Lp H 2 μ)
    (h : ∀ᵐ x ∂μ, u x = v x + w x) : u = v + w := by
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_add v w] with x hx hsum
  exact hx.trans hsum.symm

private theorem sub_smul_split {H : Type*} [AddCommGroup H] [Module ℂ H]
    (d a b c : H) (t : ℂ) (h : a = b + c) :
    d - t • a = (d - t • b) - t • c := by
  rw [h, smul_add]
  abel

private theorem l2_current_of_split {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (u v w z : Lp H 2 μ) (e : ℝ) (heq : u = v - (e : ℂ) • w)
    (horth : ∀ᵐ x ∂μ, ⟪z x, w x⟫_ℂ = 0) :
    ∀ᵐ x ∂μ, ⟪z x, u x⟫_ℂ = ⟪z x, v x⟫_ℂ := by
  rw [heq]
  filter_upwards [horth, Lp.coeFn_smul (e : ℂ) w,
    Lp.coeFn_sub v ((e : ℂ) • w)] with x hz he hd
  rw [hd, Pi.sub_apply, he, Pi.smul_apply, inner_sub_right, inner_smul_right, hz,
    mul_zero, sub_zero]

private theorem l2_norm_sq_of_split {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {μ : Measure X}
    (u v w : Lp H 2 μ) (e : ℝ) (heq : u = v - (e : ℂ) • w)
    (horth : ∀ᵐ x ∂μ, ⟪v x, w x⟫_ℂ = 0) :
    ‖u‖ ^ 2 = ‖v‖ ^ 2 + e ^ 2 * ‖w‖ ^ 2 := by
  have hinner : ⟪v, w⟫_ℂ = 0 := by
    rw [L2.inner_def]
    exact integral_eq_zero_of_ae horth
  exact (congrArg (fun z : Lp H 2 μ => ‖z‖ ^ 2) heq).trans
    (orthogonal_sub_norm_sq v w hinner e)

private theorem finite_energy_split {I : Type*} [Fintype I]
    (a b c : I → ℝ) (r p e : ℝ) (h : ∀ i, a i = b i + e ^ 2 * c i) :
    (1 / 2 : ℝ) * ∑ i, a i + r + p =
      ((1 / 2 : ℝ) * ∑ i, b i + r + p) + e ^ 2 / 2 * ∑ i, c i := by
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

section Decomposition

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (W : Submodule ℂ (Lp ℂ 2 photonMeasure))
  (k h s : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ Mk)
  (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsplit : ∀ i, ∀ᵐ x ∂volume, k i x = h i x + s i x)

include hs Ms hMs hsplit

omit W in
theorem reference_field_split (u : Reference I V) (i : I) :
    field I V C k hk Mk hMk i u =
      field I V C h hh Mh hMh i u + field I V C s hs Ms hMs i u := by
  apply lp_eq_add_of_ae (H := PhotonFock) (μ := volume)
  filter_upwards [spatialField_ae volume C (k i) (hk i) Mk (hMk i) (radiationSource I V u),
    spatialField_ae volume C (h i) (hh i) Mh (hMh i) (radiationSource I V u),
    spatialField_ae volume C (s i) (hs i) Ms (hMs i) (radiationSource I V u), hsplit i]
      with x hkx hhx hsx hsp
  have hfield : kernelField C (k i x) (radiationSource I V u x) =
      kernelField C (h i x + s i x) (radiationSource I V u x) :=
    congrArg (fun q : WeightedPhotonKernel => kernelField C q (radiationSource I V u x)) hsp
  have hadd : kernelField C (h i x + s i x) (radiationSource I V u x) =
      kernelField C (h i x) (radiationSource I V u x) +
        kernelField C (s i x) (radiationSource I V u x) :=
    congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L (radiationSource I V u x))
      ((kernelFieldMap C).map_add (h i x) (s i x))
  exact hkx.trans (hfield.trans (hadd.trans
    (congrArg₂ (fun a b : PhotonFock => a + b) hhx.symm hsx.symm)))

omit W in
theorem reference_covariant_split (u : Reference I V) (e : ℝ) (i : I) :
    covariant I V C k hk Mk hMk e i u =
      covariant I V C h hh Mh hMh e i u - (e : ℂ) • field I V C s hs Ms hMs i u := by
  have hfield := reference_field_split I V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit u i
  have halg := sub_smul_split (H := WaveSpace I)
    ((-Complex.I) • ordinary I V i u)
    (field I V C k hk Mk hMk i u) (field I V C h hh Mh hMh i u)
    (field I V C s hs Ms hMs i u) (e : ℂ) hfield
  exact (covariant_apply I V C k hk Mk hMk e i u).trans (halg.trans
    (congrArg (fun z : WaveSpace I => z - (e : ℂ) • field I V C s hs Ms hMs i u)
      (covariant_apply I V C h hh Mh hMh e i u).symm))

theorem reference_current_eq
    (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (e : ℝ) (i : I) :
    ∀ᵐ x ∂volume, ⟪inclusion I V u x, covariant I V C k hk Mk hMk e i u x⟫_ℂ =
      ⟪inclusion I V u x, covariant I V C h hh Mh hMh e i u x⟫_ℂ := by
  exact l2_current_of_split (H := PhotonFock) (μ := volume)
    (covariant I V C k hk Mk hMk e i u) (covariant I V C h hh Mh hMh e i u)
    (field I V C s hs Ms hMs i u) (inclusion I V u) e
    (reference_covariant_split I V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit u e i)
    (reference_soft_inner I V C W s hs Ms hMs hsoft u hu (inclusion I V u) hu i)

/-- Exact additional kinetic energy on the same physical PF reference vector. -/
theorem reference_energy_eq
    (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ W)
    (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (e : ℝ) :
    energy I V C k hk Mk hMk e u = energy I V C h hh Mh hMh e u +
      e ^ 2 / 2 * ∑ i, ‖field I V C s hs Ms hMs i u‖ ^ 2 := by
  have hn (i : I) : ‖covariant I V C k hk Mk hMk e i u‖ ^ 2 =
      ‖covariant I V C h hh Mh hMh e i u‖ ^ 2 +
        e ^ 2 * ‖field I V C s hs Ms hMs i u‖ ^ 2 :=
    l2_norm_sq_of_split (H := PhotonFock) (μ := volume)
      (covariant I V C k hk Mk hMk e i u)
      (covariant I V C h hh Mh hMh e i u)
      (field I V C s hs Ms hMs i u) e
      (reference_covariant_split I V C k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit u e i)
      (reference_soft_inner I V C W s hs Ms hMs hsoft u hu _
        (reference_covariant_mem I V C W h hh Mh hMh hhard u hu e i) i)
  exact finite_energy_split
    (fun i => ‖covariant I V C k hk Mk hMk e i u‖ ^ 2)
    (fun i => ‖covariant I V C h hh Mh hMh e i u‖ ^ 2)
    (fun i => ‖field I V C s hs Ms hMs i u‖ ^ 2)
    (‖radiation I V u‖ ^ 2) (‖potential I V u‖ ^ 2) e hn

theorem reference_energy_le
    (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ W)
    (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ Wᗮ)
    (u : Reference I V) (hu : ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace W)
    (e σ : ℝ) (hσ : ∀ᵐ x ∂volume, ∑ i, ‖(s i x).val.1‖ ^ 2 ≤ σ) :
    energy I V C k hk Mk hMk e u ≤ energy I V C h hh Mh hMh e u +
      (e ^ 2 / 2 * σ) * ‖inclusion I V u‖ ^ 2 := by
  have he := reference_energy_eq I V C W k h s hk hh hs Mk Mh Ms hMk hMh hMs hsplit
    hhard hsoft u hu e
  have hb := (mul_le_mul_of_nonneg_left
    (reference_soft_sum_le I V C W s hs Ms hMs hsoft u hu σ hσ)
    (by positivity : 0 ≤ e ^ 2 / 2)).trans_eq
      (mul_assoc _ _ _).symm
  exact he.le.trans (add_le_add le_rfl hb)

end Decomposition

attribute [local irreducible] PhysicalPFReference.normalEnergy PhysicalPFVacuumInsertion.insertion

section HardForm

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (h : I → Position I → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (Mh : ℝ) (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (c e : ℝ)

/-- The hard energy is an actual PF form transported by spatial vacuum insertion. -/
def hardEnergy : PositiveForm
    (B.traceData (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
      (volume : Measure (Position I)))) :=
  pullbackForm (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
    (volume : Measure (Position I))) (K := WaveSpace I)
    B (insertion volume BF c).toContinuousLinearMap
    (normalEnergy I V C h hh Mh hMh B S e)

attribute [local irreducible] PositiveForm.expectation

set_option backward.isDefEq.respectTransparency.types true in
theorem hardEnergy_rankOne
    (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2 (volume : Measure (Position I))) :
    (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I)))).rank.rankOne v) =
      (normalEnergy I V C h hh Mh hMh B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne (insertion volume BF c v)) := by
  unfold hardEnergy
  exact pullbackForm_rankOne_isometry
    (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
      (volume : Measure (Position I))) (K := WaveSpace I)
    B (insertion volume BF c)
    (normalEnergy I V C h hh Mh hMh B S e) v

attribute [local irreducible] hardEnergy

set_option backward.isDefEq.respectTransparency.types true in
theorem hardEnergy_finite_iff
    (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2 (volume : Measure (Position I))) :
    (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I)))).rank.rankOne v) < ⊤ ↔
      ∃ u : Reference I V, inclusion I V u = insertion volume BF c v := by
  have hp := hardEnergy_rankOne I V C h hh Mh hMh B S BF c e v
  exact (Iff.of_eq (congrArg (fun z : ℝ≥0∞ => z < ⊤) hp)).trans
    (PhysicalPFRadiation.normalEnergy_rankOne_finite_iff I V C h hh Mh hMh B S e
      (insertion volume BF c v))

omit C h hh Mh hMh B S e in
theorem reference_mem_of_insertion
    (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2 (volume : Measure (Position I)))
    (u : Reference I V) (hu : inclusion I V u = insertion volume BF c v) :
    ∀ᵐ x ∂volume, inclusion I V u x ∈ generatedFockSubspace (hardOnePhoton c) := by
  rw [hu]
  filter_upwards [insertion_ae volume BF c v] with x hx
  rw [hx]
  exact (v x).property

end HardForm

attribute [local irreducible] hardEnergy PositiveForm.expectation

section NormalComparison

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k h s : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ Mk)
  (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsplit : ∀ i, ∀ᵐ x ∂volume, k i x = h i x + s i x)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (c e : ℝ)
  (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ hardOnePhoton c)
  (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ (hardOnePhoton c)ᗮ)

include hs Ms hMs hsplit hhard hsoft

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
/-- Finite hard form energy gives the physical vacuum-insertion energy bound. -/
theorem inserted_energy_le
    (σ : ℝ) (hσ0 : 0 ≤ σ)
    (hσ : ∀ᵐ x ∂volume, ∑ i, ‖(s i x).val.1‖ ^ 2 ≤ σ)
    (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2 (volume : Measure (Position I)))
    (hv : (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
      ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
        (volume : Measure (Position I)))).rank.rankOne v) < ⊤) :
    (normalEnergy I V C k hk Mk hMk B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne (insertion volume BF c v)) ≤
      (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I)))).rank.rankOne v) +
        ENNReal.ofReal ((e ^ 2 / 2 * σ) * ‖v‖ ^ 2) := by
  have hdom : ∃ u : Reference I V, inclusion I V u = insertion volume BF c v :=
    (hardEnergy_finite_iff I V C h hh Mh hMh B S BF c e v).mp hv
  obtain ⟨u, hu⟩ := hdom
  have hsupport := reference_mem_of_insertion I V BF c v u hu
  have hmass : ‖inclusion I V u‖ = ‖v‖ :=
    (congrArg norm hu).trans ((insertion volume BF c).norm_map v)
  have henergy := reference_energy_le I V C (hardOnePhoton c) k h s hk hh hs
    Mk Mh Ms hMk hMh hMs hsplit hhard hsoft u hsupport e σ hσ
  have henergy' : energy I V C k hk Mk hMk e u ≤
      energy I V C h hh Mh hMh e u + (e ^ 2 / 2 * σ) * ‖v‖ ^ 2 :=
    henergy.trans_eq (congrArg (fun r : ℝ =>
      energy I V C h hh Mh hMh e u + (e ^ 2 / 2 * σ) * r ^ 2) hmass)
  have hfull : (normalEnergy I V C k hk Mk hMk B S e).expectation
      ((B.realization (WaveSpace I)).rank.rankOne (insertion volume BF c v)) =
      ENNReal.ofReal (energy I V C k hk Mk hMk e u) :=
    (congrArg (fun w : WaveSpace I =>
      (normalEnergy I V C k hk Mk hMk B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne w)) hu.symm).trans
      (normalEnergy_rankOne I V C k hk Mk hMk B S e u)
  have hhardEnergy : (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
      ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
        (volume : Measure (Position I)))).rank.rankOne v) =
      ENNReal.ofReal (energy I V C h hh Mh hMh e u) :=
    (hardEnergy_rankOne I V C h hh Mh hMh B S BF c e v).trans
        ((congrArg (fun w : WaveSpace I =>
          (normalEnergy I V C h hh Mh hMh B S e).expectation
            ((B.realization (WaveSpace I)).rank.rankOne w)) hu.symm).trans
          (normalEnergy_rankOne I V C h hh Mh hMh B S e u))
  exact hfull.trans_le ((ENNReal.ofReal_le_ofReal henergy').trans_eq
    ((ENNReal.ofReal_add (energy_nonneg I V C h hh Mh hMh e u)
      (by positivity : 0 ≤ (e ^ 2 / 2 * σ) * ‖v‖ ^ 2)).trans
        (congrArg (fun z : ℝ≥0∞ => z + ENNReal.ofReal ((e ^ 2 / 2 * σ) * ‖v‖ ^ 2))
          hhardEnergy.symm)))

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
omit hhard in
/-- Every tested physical current agrees with the hard-kernel current after insertion. -/
theorem inserted_current_eq
    (a : Position I → ℝ) (ha : AEStronglyMeasurable a volume)
    (A : ℝ) (hA : ∀ᵐ x ∂volume, |a x| ≤ A) (i : I)
    (v : Lp (generatedFockSubspace (hardOnePhoton c)) 2 (volume : Measure (Position I)))
    (hv : (hardEnergy I V C h hh Mh hMh B S BF c e).expectation
      ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
        (volume : Measure (Position I)))).rank.rankOne v) < ⊤) :
    (observable I V C k hk Mk hMk B S e (inclusion I V)
        ((PhotonLocalization.realL2Multiplier a ha A hA).comp
          (covariant I V C k hk Mk hMk e i))).value
        ((B.realization (WaveSpace I)).rank.rankOne (insertion volume BF c v)) =
      (observable I V C h hh Mh hMh B S e (inclusion I V)
        ((PhotonLocalization.realL2Multiplier a ha A hA).comp
          (covariant I V C h hh Mh hMh e i))).value
        (B.push (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I))) (K := WaveSpace I)
          (insertion volume BF c).toContinuousLinearMap
          ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
            (volume : Measure (Position I)))).rank.rankOne v)) := by
  have hdom : ∃ u : Reference I V, inclusion I V u = insertion volume BF c v :=
    (hardEnergy_finite_iff I V C h hh Mh hMh B S BF c e v).mp hv
  obtain ⟨u, hu⟩ := hdom
  have hsupport := reference_mem_of_insertion I V BF c v u hu
  let D : WaveSpace I →L[ℂ] WaveSpace I := PhotonLocalization.realL2Multiplier a ha A hA
  let Ofull := observable I V C k hk Mk hMk B S e (inclusion I V)
    (D.comp (covariant I V C k hk Mk hMk e i))
  let Ohard := observable I V C h hh Mh hMh B S e (inclusion I V)
    (D.comp (covariant I V C h hh Mh hMh e i))
  have hfull : Ofull.value
      ((B.realization (WaveSpace I)).rank.rankOne (insertion volume BF c v)) =
      (⟪inclusion I V u, D (covariant I V C k hk Mk hMk e i u)⟫_ℂ).re :=
    (congrArg (fun w : WaveSpace I =>
      Ofull.value ((B.realization (WaveSpace I)).rank.rankOne w)) hu.symm).trans
        (observable_rankOne I V C k hk Mk hMk B S e (inclusion I V)
          (D.comp (covariant I V C k hk Mk hMk e i)) u)
  have hhard : Ohard.value
      (B.push (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I))) (K := WaveSpace I)
          (insertion volume BF c).toContinuousLinearMap
        ((B.realization (Lp (generatedFockSubspace (hardOnePhoton c)) 2
          (volume : Measure (Position I)))).rank.rankOne v)) =
      (⟪inclusion I V u, D (covariant I V C h hh Mh hMh e i u)⟫_ℂ).re :=
    (congrArg Ohard.value (B.push_rankOne
      (H := Lp (generatedFockSubspace (hardOnePhoton c)) 2
        (volume : Measure (Position I))) (K := WaveSpace I)
      (insertion volume BF c).toContinuousLinearMap v)).trans
      ((congrArg (fun w : WaveSpace I =>
        Ohard.value ((B.realization (WaveSpace I)).rank.rankOne w)) hu.symm).trans
          (observable_rankOne I V C h hh Mh hMh B S e (inclusion I V)
            (D.comp (covariant I V C h hh Mh hMh e i)) u))
  have hpoint := reference_current_eq I V C (hardOnePhoton c) k h s hk hh hs
    Mk Mh Ms hMk hMh hMs hsplit hsoft u hsupport e i
  have hint :
      (∫ x, a x * (⟪inclusion I V u x, covariant I V C k hk Mk hMk e i u x⟫_ℂ).re) =
      ∫ x, a x * (⟪inclusion I V u x, covariant I V C h hh Mh hMh e i u x⟫_ℂ).re :=
    integral_congr_ae (hpoint.mono fun x hx =>
      congrArg (fun z : ℂ => a x * z.re) hx)
  exact hfull.trans
    ((multiplier_tested_inner a ha A hA (inclusion I V u)
      (covariant I V C k hk Mk hMk e i u)).trans
        (hint.trans
          ((multiplier_tested_inner a ha A hA (inclusion I V u)
            (covariant I V C h hh Mh hMh e i u)).symm.trans hhard.symm)))

end NormalComparison

end GptLean.PhysicalPFVacuumEnergy
