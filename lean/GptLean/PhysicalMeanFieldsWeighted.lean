import GptLean.PhysicalMeanFieldsZero

/-!
`prop-optimizer-mean-fields` (iii) at zero current, for all coherent amplitudes.

Let `Γ` minimize the energy at `(ρ, 0)`. For every `h` with `h/√ω ∈ L²`,
`Tr(a(h) Γ) = 0`. The truncation `h_m = 1_{1/(m+1) ≤ ω ≤ m+1} h` has
`h_m = ω f_m` with `f_m = h_m / ω ∈ L²`, so `Tr(a(h_m) Γ) = 0` by the zero-current
theorem for directions in `D(ω)`. The amplitude is bounded by
`‖h/√ω‖ ∑ₙ (E(uₙ) + ‖uₙ‖²)`, and `(h - h_m)/√ω → 0` in `L²` by dominated
convergence.

Taking `h = G^a_y` gives a vanishing mean vector potential,
`Tr(A^a(y) Γ) = 2 Re Tr(a(G^a_y) Γ) = 0` at every point `y`. The mean magnetic
field is the distributional curl of the mean vector potential, so it vanishes
as well.
-/

noncomputable section

namespace GptLean.PhysicalWeyl

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference PhysicalPFSoftTag
  PhysicalNormalTrace PhysicalPairSpace Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Window

/-- The frequency window `1/(m+1) ≤ ω ≤ m+1`. -/
def windowSet (m : ℕ) : Set PhotonMode := {p | 1 / ((m : ℝ) + 1) ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ (m : ℝ) + 1}

theorem windowSet_measurable (m : ℕ) : MeasurableSet (windowSet m) :=
  (measurableSet_le measurable_const measurable_fst.norm).inter
    (measurableSet_le measurable_fst.norm measurable_const)

def window (m : ℕ) (p : PhotonMode) : ℝ := (windowSet m).indicator (fun _ => 1) p

def windowInv (m : ℕ) (p : PhotonMode) : ℝ := (windowSet m).indicator (fun p => 1 / ‖p.1‖) p

theorem window_measurable (m : ℕ) : Measurable (window m) :=
  measurable_const.indicator (windowSet_measurable m)

theorem windowInv_measurable (m : ℕ) : Measurable (windowInv m) :=
  (measurable_const.div measurable_fst.norm).indicator (windowSet_measurable m)

theorem window_bound (m : ℕ) (p : PhotonMode) : |window m p| ≤ 1 := by
  unfold window
  by_cases h : p ∈ windowSet m
  · rw [Set.indicator_of_mem h]; simp
  · rw [Set.indicator_of_notMem h]; simp

theorem windowInv_bound (m : ℕ) (p : PhotonMode) : |windowInv m p| ≤ (m : ℝ) + 1 := by
  unfold windowInv
  by_cases h : p ∈ windowSet m
  · rw [Set.indicator_of_mem h]
    have h1 : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hp : 0 < ‖p.1‖ := h1.trans_le h.1
    rw [abs_of_pos (one_div_pos.mpr hp), one_div_le hp (by positivity)]
    exact h.1
  · rw [Set.indicator_of_notMem h]; simp; positivity

/-- Multiplication by the window. -/
def windowCut (m : ℕ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  PhotonLocalization.realL2Multiplier (window m) (window_measurable m).aestronglyMeasurable 1
    (ae_of_all _ (window_bound m))

/-- Multiplication by the window divided by the frequency. -/
def windowInvCut (m : ℕ) : Lp ℂ 2 photonMeasure →L[ℂ] Lp ℂ 2 photonMeasure :=
  PhotonLocalization.realL2Multiplier (windowInv m) (windowInv_measurable m).aestronglyMeasurable
    ((m : ℝ) + 1) (ae_of_all _ (windowInv_bound m))

theorem windowCut_ae (m : ℕ) (y : Lp ℂ 2 photonMeasure) :
    windowCut m y =ᵐ[photonMeasure] fun p => window m p • y p :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ y

theorem windowInvCut_ae (m : ℕ) (y : Lp ℂ 2 photonMeasure) :
    windowInvCut m y =ᵐ[photonMeasure] fun p => windowInv m p • y p :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ y

theorem norm_sub_window_sq (x : ℂ) (w : ℝ) : ‖x - w • x‖ ^ 2 = (1 - w) ^ 2 * ‖x‖ ^ 2 := by
  rw [show x - w • x = (1 - w) • x by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- The truncated weighted kernel. -/
def truncKernel (m : ℕ) (k : WeightedPhotonKernel) : WeightedPhotonKernel :=
  ⟨(windowCut m k.val.1, windowCut m k.val.2), by
    change ∀ᵐ p ∂photonMeasure, windowCut m k.val.1 p =
      (Real.sqrt ‖p.1‖ : ℂ) * windowCut m k.val.2 p
    filter_upwards [windowCut_ae m k.val.1, windowCut_ae m k.val.2, k.property] with p h₁ h₂ h₃
    rw [h₁, h₂, h₃, Complex.real_smul, Complex.real_smul]
    ring⟩

/-- The direction `f_m = h_m / ω` of the truncated kernel. -/
def truncDirection (m : ℕ) (k : WeightedPhotonKernel) : Lp ℂ 2 photonMeasure :=
  windowInvCut m k.val.1

theorem truncKernel_direction (m : ℕ) (k : WeightedPhotonKernel) :
    ∀ᵐ p ∂photonMeasure, (truncKernel m k).val.2 p =
      (Real.sqrt ‖p.1‖ : ℂ) * truncDirection m k p := by
  filter_upwards [windowCut_ae m k.val.2, windowInvCut_ae m k.val.1, k.property] with p h₁ h₂ h₃
  change windowCut m k.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * windowInvCut m k.val.1 p
  rw [h₁, h₂, h₃, Complex.real_smul, Complex.real_smul]
  unfold window windowInv
  by_cases h : p ∈ windowSet m
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    have h1 : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hp : 0 < ‖p.1‖ := h1.trans_le h.1
    have hs : (Real.sqrt ‖p.1‖ : ℂ) * (Real.sqrt ‖p.1‖ : ℂ) = (‖p.1‖ : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
    have hne : (‖p.1‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_div]
    rw [← mul_assoc, ← mul_assoc, mul_comm _ (1 / (‖p.1‖ : ℂ)), mul_assoc (1 / (‖p.1‖ : ℂ)),
      hs, one_div_mul_cancel hne, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

theorem truncKernel_tendsto (k : WeightedPhotonKernel) :
    Tendsto (fun m => ‖k.val.2 - (truncKernel m k).val.2‖) atTop (𝓝 0) := by
  have hae : ∀ᵐ p ∂photonMeasure, ∀ m : ℕ, ‖(k.val.2 - (truncKernel m k).val.2) p‖ ^ 2 =
      (1 - window m p) ^ 2 * ‖k.val.2 p‖ ^ 2 := by
    rw [ae_all_iff]
    intro m
    filter_upwards [Lp.coeFn_sub k.val.2 (truncKernel m k).val.2,
      windowCut_ae m k.val.2] with p h₁ h₂
    have h₁' : (k.val.2 - (truncKernel m k).val.2) p = k.val.2 p - windowCut m k.val.2 p := h₁
    rw [h₁', h₂]
    exact norm_sub_window_sq _ _
  have hsq : Tendsto (fun m => ‖k.val.2 - (truncKernel m k).val.2‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := photonMeasure)
      (F := fun (m : ℕ) p => ‖(k.val.2 - (truncKernel m k).val.2) p‖ ^ 2) (f := fun _ => 0)
      (fun p => ‖k.val.2 p‖ ^ 2)
      (fun m => (Lp.aestronglyMeasurable _).norm.pow 2) (integrable_norm_sq k.val.2)
      (fun m => by
        filter_upwards [hae] with p hp
        rw [hp m, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hw := window_bound m p
        have h1 : (1 - window m p) ^ 2 ≤ 1 := by
          unfold window at hw ⊢
          by_cases h : p ∈ windowSet m
          · rw [Set.indicator_of_mem h]; norm_num
          · rw [Set.indicator_of_notMem h]; norm_num
        nlinarith [sq_nonneg ‖k.val.2 p‖])
      (by
        filter_upwards [hae, NormalPhoton.frequency_positive] with p hp hpos
        have hev : ∀ᶠ m : ℕ in atTop, p ∈ windowSet m := by
          obtain ⟨n, hn⟩ := exists_nat_ge (max ‖p.1‖ (1 / ‖p.1‖))
          refine Filter.eventually_atTop.mpr ⟨n, fun m hm => ⟨?_, ?_⟩⟩
          · have hm' : (n : ℝ) ≤ m := by exact_mod_cast hm
            have hq : 1 / ‖p.1‖ ≤ (m : ℝ) + 1 := by
              linarith [le_max_right ‖p.1‖ (1 / ‖p.1‖)]
            have hpos' : 0 < ‖p.1‖ := hpos
            rw [one_div_le (by positivity) hpos']
            exact hq
          · have hm' : (n : ℝ) ≤ m := by exact_mod_cast hm
            linarith [le_max_left ‖p.1‖ (1 / ‖p.1‖)]
        refine tendsto_const_nhds.congr' (hev.mono fun m hm => ?_)
        change (0 : ℝ) = ‖(k.val.2 - (truncKernel m k).val.2) p‖ ^ 2
        rw [hp m]
        unfold window
        rw [Set.indicator_of_mem hm]
        simp)
    simp only [integral_zero] at h
    exact h.congr fun m => (norm_sq_eq_integral _).symm
  have hs := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hs
  exact hs.congr fun m => Real.sqrt_sq (norm_nonneg _)

end Window

section Amplitude

variable {N : ℕ} (V : Position (Fin N × Fin 3) → ℝ)

theorem annihilationRef_add (k l : WeightedPhotonKernel) (u : Reference (Fin N × Fin 3) V) :
    annihilationRef V (k + l) u = annihilationRef V k u + annihilationRef V l u := by
  apply Lp.ext
  filter_upwards [(kernelAnnihilation (k + l)).coeFn_compLpL (radiationSource _ V u),
    (kernelAnnihilation k).coeFn_compLpL (radiationSource _ V u),
    (kernelAnnihilation l).coeFn_compLpL (radiationSource _ V u),
    Lp.coeFn_add (annihilationRef V k u) (annihilationRef V l u)] with x h₁ h₂ h₃ h₄
  have h₁' : annihilationRef V (k + l) u x =
      kernelAnnihilation (k + l) (radiationSource _ V u x) := h₁
  have h₂' : annihilationRef V k u x = kernelAnnihilation k (radiationSource _ V u x) := h₂
  have h₃' : annihilationRef V l u x = kernelAnnihilation l (radiationSource _ V u x) := h₃
  have hk : kernelAnnihilation (k + l) (radiationSource _ V u x) =
      kernelAnnihilation k (radiationSource _ V u x) +
        kernelAnnihilation l (radiationSource _ V u x) :=
    congrArg (fun L => L (radiationSource _ V u x)) (kernelAnnihilation_add k l)
  exact h₁'.trans (hk.trans ((congrArg₂ (· + ·) h₂'.symm h₃'.symm).trans h₄.symm))

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ b, AEStronglyMeasurable (κ b) volume)
  (M : ℝ) (hbound : ∀ b, ∀ᵐ x ∂volume, ‖κ b x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ)

theorem sourceAmplitude_summable {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (k : WeightedPhotonKernel) :
    Summable (fun n => ⟪inclusion (Fin N × Fin 3) V (s.vector n),
      annihilationRef V k (s.vector n)⟫_ℂ) :=
  ((amplitude_summable V C κ hκ M hbound B S e s he k).map (starRingEnd ℂ)
    Complex.continuous_conj).congr fun _ => inner_conj_symm _ _

theorem sourceAmplitude_add {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (k l : WeightedPhotonKernel) :
    sourceAmplitude V B s (k + l) = sourceAmplitude V B s k + sourceAmplitude V B s l :=
  (tsum_congr fun n => (congrArg (fun z => ⟪inclusion (Fin N × Fin 3) V (s.vector n), z⟫_ℂ)
    (annihilationRef_add V k l (s.vector n))).trans (inner_add_right _ _ _)).trans
      ((sourceAmplitude_summable V C κ hκ M hbound B S e s he k).tsum_add
        (sourceAmplitude_summable V C κ hκ M hbound B S e s he l))

theorem sourceAmplitude_norm_le {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (k : WeightedPhotonKernel) :
    ‖sourceAmplitude V B s k‖ ≤ ‖k.val.2‖ * ∑' n, (energy (Fin N × Fin 3) V C κ hκ M hbound e
      (s.vector n) + ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2) := by
  have hE := (s.energy_hasSum C κ hκ M hbound S e he).summable.add s.mass_hasSum.summable
  have hpt : ∀ n, ‖⟪inclusion (Fin N × Fin 3) V (s.vector n),
      annihilationRef V k (s.vector n)⟫_ℂ‖ ≤ ‖k.val.2‖ * (energy (Fin N × Fin 3) V C κ hκ M hbound e
        (s.vector n) + ‖inclusion (Fin N × Fin 3) V (s.vector n)‖ ^ 2) := fun n =>
    (norm_inner_symm _ _).trans_le ((amplitude_re_le V k (s.vector n)).trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (radiation_le_energy (Fin N × Fin 3) V C κ hκ M hbound e (s.vector n)) le_rfl)
          (norm_nonneg _)))
  have hS := (Summable.of_norm_bounded (hE.mul_left _) hpt).norm
  exact (norm_tsum_le_tsum_norm hS).trans
    ((Summable.tsum_le_tsum hpt hS (hE.mul_left _)).trans_eq tsum_mul_left)

/-- An amplitude that vanishes on every frequency window vanishes. -/
theorem sourceAmplitude_eq_zero_of_trunc {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) V B x)
    (he : (normalEnergy (Fin N × Fin 3) V C κ hκ M hbound B S e).expectation x < ⊤)
    (k : WeightedPhotonKernel) (hzero : ∀ n, sourceAmplitude V B s (truncKernel n k) = 0) :
    sourceAmplitude V B s k = 0 := by
  have hle : ∀ n, ‖sourceAmplitude V B s k‖ ≤ ‖k.val.2 - (truncKernel n k).val.2‖ *
      ∑' j, (energy (Fin N × Fin 3) V C κ hκ M hbound e (s.vector j) +
        ‖inclusion (Fin N × Fin 3) V (s.vector j)‖ ^ 2) := fun n => by
    have hsplit := sourceAmplitude_add V C κ hκ M hbound B S e s he (truncKernel n k)
      (k - truncKernel n k)
    have hk : truncKernel n k + (k - truncKernel n k) = k := by abel
    have h' : sourceAmplitude V B s k = sourceAmplitude V B s (k - truncKernel n k) :=
      (congrArg (sourceAmplitude V B s) hk).symm.trans (hsplit.trans
        ((congrArg (· + sourceAmplitude V B s (k - truncKernel n k)) (hzero n)).trans
          (zero_add _)))
    exact (congrArg norm h').trans_le
      (sourceAmplitude_norm_le V C κ hκ M hbound B S e s he (k - truncKernel n k))
  have htend := (truncKernel_tendsto k).mul_const (∑' j, (energy (Fin N × Fin 3) V C κ hκ M
    hbound e (s.vector j) + ‖inclusion (Fin N × Fin 3) V (s.vector j)‖ ^ 2))
  exact norm_le_zero_iff.mp ((ge_of_tendsto' htend hle).trans_eq (zero_mul _))

end Amplitude

section Physical

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (e : ℝ) (W : ConcreteWeylLaw photonMeasure)
  (BF : StandardSymmetricFockExponential) (BW : StandardWienerSegal)
  (core : Gaussian.CountableSpatialTestCore) (smooth : Gaussian.SmoothSobolevBackground)
  (C₀ : ℝ) (scaled : Gaussian.ScaledGradientSobolevBackground (6 + 12 * (N : ℝ)) C₀)
  (B₀ : SymmetricLift.TensorBackground Repair.SixTag) (B₁ : SymmetricLift.TensorMultilinearData B₀)
  {ι : Type*} (basis : HilbertBasis ι ℂ (SymmetricLift.recursiveLiftCandidate B₀ N).target)
  (index : ι ↪ ℕ) (Sob : PhysicalSobolevRealization.StandardHomogeneousSobolev)
  (Rellich : PhysicalRellichFourier.StandardSupportedHalfRellich)
  (Hardy : PhysicalPhotonLocalizedNumber.StandardFractionalHardy)
  (hLp : PhysicalPairDuality.StandardFiniteDimensionalLpRepresentation)
  (hFM : PhysicalPairDuality.StandardDualFenchelMoreau)

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **Every coherent amplitude of an optimizer at zero current vanishes**:
`Tr(a(h) Γ) = 0` for every `h` with `h/√ω ∈ L²`, in every fermionic spectral source. -/
theorem optimizer_zero_current_weighted (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (ρ, 0))
    (k : WeightedPhotonKernel)
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    sourceAmplitude (PhysicalRemoval.potential N 1) B s.toSource k = 0 :=
  sourceAmplitude_eq_zero_of_trunc (PhysicalRemoval.potential N 1) C
    (PhysicalRemovalKernels.full F χ N) (PhysicalRemovalKernels.full_measurable F χ N)
    (PhysicalRemovalKernels.bound F χ) (PhysicalRemovalKernels.full_bound F χ N) B S e
    s.toSource m.val.property.2.2 k fun n =>
      optimizer_zero_current_amplitude i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁ basis
        index Sob Rellich Hardy hLp hFM he hC₀ m hm hopt (truncKernel n k)
        (truncKernel_direction n k) s

/-- The mean vector potential `Tr(A^a(y) Γ) = 2 Re Tr(a(G^a_y) Γ)`. -/
def meanVectorPotential {x : B.Trace (WaveSpace (Fin N × Fin 3))}
    (s : PhysicalPFSource.Source (Fin N × Fin 3) (PhysicalRemoval.potential N 1) B x)
    (a : Fin 3) (y : Position) : ℝ :=
  2 * (sourceAmplitude (PhysicalRemoval.potential N 1) B s (fieldKernel F χ (a, y))).re

include W BF BW core smooth scaled B₀ B₁ basis index Sob Rellich Hardy hLp hFM in
/-- **The mean vector potential and the mean magnetic field of an optimizer at
zero current vanish**: `Tr(A(y) Γ) = 0` at every point, and
`∫ g · Tr(A Γ) = 0` for every vector field `g`, in particular for `g = ∇ × v`. -/
theorem optimizer_zero_current_fields (he : 0 ≤ e) (hC₀ : 0 ≤ C₀)
    (m : PhysicalAttainmentFunctionals.MixedState F χ C B S e (N := N)) {ρ : Density}
    (hm : (PhysicalRemoval.model i F χ 1 C B S e).density m = (ρ, 0))
    (hopt : ((PhysicalRemoval.model i F χ 1 C B S e).energy m : EReal) =
      PhysicalAttainmentFunctionals.mixedFunctional i F χ C B S e (ρ, 0))
    (s : PhysicalPFSource.SupportedSource N (PhysicalRemoval.potential N 1) B m.val.val) :
    (∀ a y, meanVectorPotential F χ B s.toSource a y = 0) ∧
      ∀ g : Position → Vector,
        ∫ y, ∑ a, g y a * meanVectorPotential F χ B s.toSource a y = 0 := by
  have h : ∀ a y, meanVectorPotential F χ B s.toSource a y = 0 := fun a y => by
    unfold meanVectorPotential
    rw [optimizer_zero_current_weighted i F χ C B S e W BF BW core smooth C₀ scaled B₀ B₁ basis
      index Sob Rellich Hardy hLp hFM he hC₀ m hm hopt _ s, Complex.zero_re, mul_zero]
  refine ⟨h, fun g => ?_⟩
  simp only [h, mul_zero, Finset.sum_const_zero, integral_zero]

end Physical

end GptLean.PhysicalWeyl
