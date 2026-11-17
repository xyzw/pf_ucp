import GptLean.WeylCoherentSobolevLocal
import GptLean.WeylCoherentOverlap
import GptLean.PhysicalFockRealStructure

/-! Real fixed-space coherent fields, their Lipschitz estimate, and their
weak H1 derivative with zero Berry connection. -/

noncomputable section

namespace GptLean.Representability

open MeasureTheory SymmetricLift PhysicalFock
open scoped ENNReal InnerProductSpace ContDiff

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types true

section Linear

variable {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : CoherentBase d → E} {df : Fin d → CoherentBase d → E}

/-- Bounded linear maps preserve the actual distributional H1 derivative. -/
theorem weakH1Local_clm (L : E →L[ℝ] F) (hf : HasWeakH1Local f df) :
    HasWeakH1Local (fun x => L (f x)) (fun i x => L (df i x)) := by
  refine ⟨fun K hK => L.comp_memLp' (hf.function_memLp K hK),
    fun i K hK => L.comp_memLp' (hf.derivative_memLp i K hK), ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  have hK : IsCompact K := hs
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmφ : MemLp φ 2 (volume.restrict K) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hmφ' : MemLp φ' 2 (volume.restrict K) :=
    (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hz : ∀ x, x ∉ K → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hz' : ∀ x, x ∉ K → φ' x = 0 := fun x hx => by simp [φ', fderiv_of_notMem_tsupport ℝ hx]
  have hdint := integrable_smul_of_memLp_on_support hmφ (hf.derivative_memLp i K hK) hz
  have hfint := integrable_smul_of_memLp_on_support hmφ' (hf.function_memLp K hK) hz'
  calc
    (∫ x, φ x • L (df i x)) = ∫ x, L (φ x • df i x) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (L.map_smul (φ x) (df i x)).symm
    _ = L (∫ x, φ x • df i x) := L.integral_comp_comm hdint
    _ = L (-(∫ x, φ' x • f x)) := congrArg L (hf.weak i φ hφ hs)
    _ = -(∫ x, φ' x • L (f x)) := by
      rw [map_neg, ← L.integral_comp_comm hfint]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => L.map_smul (φ' x) (f x)

theorem localH1Extension_clm {O : Set (CoherentBase d)} (L : E →L[ℝ] F)
    (hf : HasLocalH1Extension O f df) :
    HasLocalH1Extension O (fun x => L (f x)) (fun i x => L (df i x)) := by
  refine ⟨hf.isOpen, fun K hK hKO => L.comp_memLp' (hf.function_memLp K hK hKO),
    fun i K hK hKO => L.comp_memLp' (hf.derivative_memLp i K hK hKO), ?_⟩
  intro x hx
  obtain ⟨U, g, dg, hU, hxU, hUO, hg, he, hde⟩ := hf.extension x hx
  exact ⟨U, (fun y => L (g y)), (fun i y => L (dg i y)), hU, hxU, hUO,
    weakH1Local_clm L hg, he.fun_comp L, fun i => (hde i).fun_comp L⟩

end Linear

private theorem zero_weakH1Local (d : ℕ) :
    HasWeakH1Local (fun _ : CoherentBase d => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun _ _ => MemLp.zero', fun _ _ _ => MemLp.zero', ?_⟩
  intro i φ hφ hs
  simp

private theorem zero_localH1Extension {d : ℕ} {O : Set (CoherentBase d)} (hO : IsOpen O) :
    HasLocalH1Extension O (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨hO, fun _ _ _ => MemLp.zero', fun _ _ _ _ => MemLp.zero', ?_⟩
  intro x hx
  exact ⟨O, (fun _ => 0), (fun _ _ => 0), hO, hx, Set.Subset.rfl,
    zero_weakH1Local d, Filter.EventuallyEq.rfl, fun _ => Filter.EventuallyEq.rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

omit [SigmaFinite μ] in
/-- Pairings of vectors fixed by any conjugation are real. -/
theorem realStructure_fixed_inner_im (J : RealStructure (Lp ℂ 2 μ))
    (f g : J.fixedSpace) : (⟪(f : Lp ℂ 2 μ), (g : Lp ℂ 2 μ)⟫_ℂ).im = 0 := by
  have h := J.realIsometry.inner_map_map (f : Lp ℂ 2 μ) (Complex.I • (g : Lp ℂ 2 μ))
  change inner ℝ (J.conjugation (f : Lp ℂ 2 μ))
    (J.conjugation (Complex.I • (g : Lp ℂ 2 μ))) =
      inner ℝ (f : Lp ℂ 2 μ) (Complex.I • (g : Lp ℂ 2 μ)) at h
  rw [J.conjugation_fixed, map_smulₛₗ, Complex.conj_I, J.conjugation_fixed] at h
  have hreal (u v : Lp ℂ 2 μ) : ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
    change (∫ p, (⟪u p, v p⟫_ℂ).re ∂μ) = (∫ p, ⟪u p, v p⟫_ℂ ∂μ).re
    exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)
  simp only [neg_smul, inner_neg_right, hreal, inner_smul_right,
    Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
  linarith

namespace ConcreteWeylLaw

variable (W : ConcreteWeylLaw μ) (J : RealStructure (Lp ℂ 2 μ))

/-- The real fixed-space coherent map has global Lipschitz constant one. -/
theorem coherent_lipschitz_fixed :
    LipschitzWith 1 (fun f : J.fixedSpace => W.coherent μ (f : Lp ℂ 2 μ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have h := W.coherent_dist_le_of_real μ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)
    (realStructure_fixed_inner_im μ J f g)
  have he : ‖(f : Lp ℂ 2 μ) - (g : Lp ℂ 2 μ)‖ = ‖f - g‖ := rfl
  rw [he] at h
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using h

theorem coherent_dist_sq_fixed (f g : J.fixedSpace) :
    dist (W.coherent μ (f : Lp ℂ 2 μ)) (W.coherent μ (g : Lp ℂ 2 μ)) ^ 2 =
      2 * (1 - Real.exp (-(‖(f : Lp ℂ 2 μ) - (g : Lp ℂ 2 μ)‖ ^ 2) / 2)) :=
  by
    have h := W.coherent_dist_sq_of_real μ (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)
      (realStructure_fixed_inner_im μ J f g)
    simpa only [dist_eq_norm, neg_div] using h

instance coherentFixedNormedSpace : NormedSpace ℝ J.fixedSpace where
  norm_smul_le r g := by
    change ‖r • (g.val : Lp ℂ 2 μ)‖ ≤ ‖r‖ * ‖g.val‖
    exact norm_smul_le r _

variable {d : ℕ} {O : Set (CoherentBase d)}
  {f : CoherentBase d → J.fixedSpace} {df : Fin d → CoherentBase d → J.fixedSpace}

/-- The weak derivative of a conjugation-real coherent field has no Berry term. -/
theorem coherent_weakH1_fixed (hf : HasLocalH1Extension O f df) :
    HasWeakH1On O (fun x => W.coherent μ (f x : Lp ℂ 2 μ))
      (fun i x => W.coherentDerivative μ (f x : Lp ℂ 2 μ) (df i x : Lp ℂ 2 μ)) := by
  let L : J.fixedSpace →L[ℝ] Lp ℂ 2 μ := J.fixedSpace.subtypeL
  have hL (g : J.fixedSpace) : L g = (g : Lp ℂ 2 μ) := rfl
  have h := W.phaseCoherent_weakH1_on μ
    (localH1Extension_clm L hf) (zero_localH1Extension hf.isOpen)
    (fun i K hK hKO => by
      simpa only [hL, zero_add, realStructure_fixed_inner_im] using
        (MemLp.zero' : MemLp (fun _ : CoherentBase d => (0 : ℝ)) 2 (volume.restrict K)))
  simpa only [hL, phaseCoherent, phaseCoherentDerivative, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_smul, zero_smul, add_zero] using h

theorem coherent_fixed_connection (x : CoherentBase d) (i : Fin d) :
    ⟪W.coherent μ (f x : Lp ℂ 2 μ),
      W.coherentDerivative μ (f x : Lp ℂ 2 μ) (df i x : Lp ℂ 2 μ)⟫_ℂ = 0 := by
  rw [W.coherent_connection, realStructure_fixed_inner_im, Complex.ofReal_zero, mul_zero]

theorem coherent_fixed_metric (x : CoherentBase d) (i : Fin d) :
    ‖W.coherentDerivative μ (f x : Lp ℂ 2 μ) (df i x : Lp ℂ 2 μ)‖ ^ 2 = ‖df i x‖ ^ 2 := by
  rw [W.coherent_metric, realStructure_fixed_inner_im, zero_pow (by decide), add_zero]
  rfl

end ConcreteWeylLaw

end GptLean.Representability
