import GptLean.Repair.WeightedFormDomain
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The real electronic localization and the actual exponential gauge
phase on the PF reference domain. Their weak product rules apply to
arbitrary source vectors in that domain. -/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal ContDiff

variable {I E H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem smooth_compact_memLp {f : EuclideanSpace ℝ I → E}
    (hf : Continuous f) {K : Set (EuclideanSpace ℝ I)} (hK : IsCompact K) :
    MemLp f 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

private theorem smooth_test_integrable {f : EuclideanSpace ℝ I → E}
    (hf : Continuous f) {φ : EuclideanSpace ℝ I → ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) :=
  integrable_smul_of_memLp_on_support
    ((hφ.memLp_of_hasCompactSupport hs).restrict (tsupport φ))
    (smooth_compact_memLp hf hs) (fun x hx => image_eq_zero_of_notMem_tsupport hx)

/-- Smooth functions have their actual weak derivatives without any
global derivative bound. Compact tests supply all required integrability. -/
theorem weakH1Local_of_contDiff {f : EuclideanSpace ℝ I → E}
    (hf : ContDiff ℝ ∞ f) :
    HasWeakH1Local f (fun i x => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hd (i : I) : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun _ hK => smooth_compact_memLp hf.continuous hK,
    fun i _ hK => smooth_compact_memLp (hd i) hK, ?_⟩
  intro i φ hφ hs
  have hdφ : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (smooth_test_integrable hf.continuous hdφ (hs.fderiv_apply ℝ _))
    (smooth_test_integrable (hd i) hφ.continuous hs)
    (smooth_test_integrable hf.continuous hφ.continuous hs)
    (fun x _ => hφ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)

/-- Real localization is a special case of the derived complex product
rule, including nonsmooth localization multipliers at their zero sets. -/
theorem real_localization_pf_reference
    (R : H →ₗ.[ℂ] H) {η : EuclideanSpace ℝ I → ℝ}
    {dη : I → EuclideanSpace ℝ I → ℝ} {ψ : EuclideanSpace ℝ I → H}
    (hη : HasWeakH1Local η dη) {C : ℝ} (hbound : ∀ᵐ x ∂volume, |η x| ≤ C)
    (hψ : InPFReferenceDomain R ψ)
    (hweight : ∀ i, MemLp (fun x => dη i x • ψ x) 2 volume) :
    InPFReferenceDomain R (fun x => η x • ψ x) := by
  have hk := weakH1Local_map Complex.ofRealCLM hη
  have hb : ∀ᵐ x ∂volume, ‖Complex.ofRealCLM (η x)‖ ≤ C := by simpa using hbound
  have hw : ∀ i, MemLp (fun x => Complex.ofRealCLM (dη i x) • ψ x) 2 volume := by
    intro i
    simpa only [Complex.ofRealCLM_apply, Complex.coe_smul] using hweight i
  simpa only [Complex.ofRealCLM_apply, Complex.coe_smul] using
    pf_reference_mem_of_weighted R hk hb hψ hw

def gaugePhase (φ : EuclideanSpace ℝ I → ℝ) (x : EuclideanSpace ℝ I) : ℂ :=
  Complex.exp ((φ x : ℂ) * Complex.I)

theorem gaugePhase_norm (φ : EuclideanSpace ℝ I → ℝ) (x : EuclideanSpace ℝ I) :
    ‖gaugePhase φ x‖ = 1 := Complex.norm_exp_ofReal_mul_I (φ x)

theorem gaugePhase_contDiff {φ : EuclideanSpace ℝ I → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (gaugePhase φ) :=
  ((Complex.ofRealCLM.contDiff.comp hφ).mul contDiff_const).cexp

theorem gaugePhase_fderiv {φ : EuclideanSpace ℝ I → ℝ}
    (hφ : Differentiable ℝ φ) (x : EuclideanSpace ℝ I) (v : EuclideanSpace ℝ I) :
    fderiv ℝ (gaugePhase φ) x v = gaugePhase φ x * (fderiv ℝ φ x v : ℂ) * Complex.I := by
  have h := (((Complex.ofRealCLM.hasFDerivAt).comp x (hφ x).hasFDerivAt).mul_const
    Complex.I).cexp
  change HasFDerivAt (gaugePhase φ) _ x at h
  rw [h.fderiv]
  simp [gaugePhase, mul_assoc]
  ring

/-- The actual exponential phase preserves the PF form domain when the
phase gradient times the source is square integrable. This covers the
smooth cluster phase, whose gradient is bounded for each measured field. -/
theorem gaugePhase_pf_reference
    (R : H →ₗ.[ℂ] H) {φ : EuclideanSpace ℝ I → ℝ}
    {ψ : EuclideanSpace ℝ I → H} (hφ : ContDiff ℝ ∞ φ)
    (hψ : InPFReferenceDomain R ψ)
    (hweight : ∀ i, MemLp (fun x =>
      fderiv ℝ φ x (EuclideanSpace.single i 1) • ψ x) 2 volume) :
    InPFReferenceDomain R (fun x => gaugePhase φ x • ψ x) := by
  have hw := weakH1Local_of_contDiff (gaugePhase_contDiff hφ)
  apply pf_reference_mem_of_weighted R hw
    (Eventually.of_forall fun x => (gaugePhase_norm φ x).le) hψ
  intro i
  have hgrad : Continuous (fun x => fderiv ℝ (gaugePhase φ) x (EuclideanSpace.single i 1)) :=
    ((gaugePhase_contDiff hφ).continuous_fderiv (by simp)).clm_apply continuous_const
  apply (hweight i).mono (hgrad.aestronglyMeasurable.smul hψ.1.1)
  exact Eventually.of_forall fun x => by
    change ‖fderiv ℝ (gaugePhase φ) x (EuclideanSpace.single i 1) • ψ x‖ ≤
      ‖fderiv ℝ φ x (EuclideanSpace.single i 1) • ψ x‖
    rw [gaugePhase_fderiv (hφ.differentiable (by simp))]
    simp only [norm_smul, norm_mul, gaugePhase_norm, Complex.norm_real,
      Complex.norm_I, one_mul, mul_one]
    exact le_rfl

/-- Electronic localization lies in the physical fermionic form domain.
The canonical domain equality is standard Hamiltonian background. -/
theorem real_localization_physical_form_domain {G : Type*}
    (R : H →ₗ.[ℂ] H)
    (Q : Submodule ℂ (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))))
    (T : G → EuclideanSpace ℝ I → EuclideanSpace ℝ I) (χ : G → ℂ)
    (hcanonical : ∀ (f : EuclideanSpace ℝ I → H) (hf : MemLp f 2 volume),
      hf.toLp f ∈ Q ↔ HasElectronicCharacter T χ f ∧ InPFReferenceDomain R f)
    {η : EuclideanSpace ℝ I → ℝ} {dη : I → EuclideanSpace ℝ I → ℝ}
    {ψ : EuclideanSpace ℝ I → H}
    (hη : HasWeakH1Local η dη) {C : ℝ} (hbound : ∀ᵐ x ∂volume, |η x| ≤ C)
    (hinv : ∀ g, ∀ᵐ x ∂volume, η (T g x) = η x)
    (hψ : MemLp ψ 2 volume) (hQ : hψ.toLp ψ ∈ Q)
    (hweight : ∀ i, MemLp (fun x => dη i x • ψ x) 2 volume) :
    ∃ hout : MemLp (fun x => η x • ψ x) 2 volume,
      hout.toLp (fun x => η x • ψ x) ∈ Q := by
  obtain ⟨hsym, href⟩ := (hcanonical ψ hψ).mp hQ
  have hout := real_localization_pf_reference R hη hbound href hweight
  have hs : HasElectronicCharacter T χ (fun x => η x • ψ x) := by
    intro g
    filter_upwards [hinv g, hsym g] with x hx hψx
    rw [hx, hψx, smul_comm]
  exact ⟨hout.1, (hcanonical _ hout.1).mpr ⟨hs, hout⟩⟩

/-- A permutation-invariant smooth gauge phase lies in the physical
fermionic form domain, with its weighted derivative checked on the source. -/
theorem gaugePhase_physical_form_domain {G : Type*}
    (R : H →ₗ.[ℂ] H)
    (Q : Submodule ℂ (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))))
    (T : G → EuclideanSpace ℝ I → EuclideanSpace ℝ I) (χ : G → ℂ)
    (hcanonical : ∀ (f : EuclideanSpace ℝ I → H) (hf : MemLp f 2 volume),
      hf.toLp f ∈ Q ↔ HasElectronicCharacter T χ f ∧ InPFReferenceDomain R f)
    {φ : EuclideanSpace ℝ I → ℝ} {ψ : EuclideanSpace ℝ I → H}
    (hφ : ContDiff ℝ ∞ φ)
    (hinv : ∀ g, ∀ᵐ x ∂volume, φ (T g x) = φ x)
    (hψ : MemLp ψ 2 volume) (hQ : hψ.toLp ψ ∈ Q)
    (hweight : ∀ i, MemLp (fun x =>
      fderiv ℝ φ x (EuclideanSpace.single i 1) • ψ x) 2 volume) :
    ∃ hout : MemLp (fun x => gaugePhase φ x • ψ x) 2 volume,
      hout.toLp (fun x => gaugePhase φ x • ψ x) ∈ Q := by
  obtain ⟨hsym, href⟩ := (hcanonical ψ hψ).mp hQ
  have hout := gaugePhase_pf_reference R hφ href hweight
  have hk : ∀ g, ∀ᵐ x ∂volume, gaugePhase φ (T g x) = gaugePhase φ x := by
    intro g
    filter_upwards [hinv g] with x hx
    simp only [gaugePhase, hx]
  exact ⟨hout.1, (hcanonical _ hout.1).mpr
    ⟨electronicCharacter_smul T χ hk hsym, hout⟩⟩

end GptLean.Repair
