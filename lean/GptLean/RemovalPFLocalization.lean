import GptLean.RemovalPhysicalSource

/-! Localization of original WIS reference-domain data. The standard WIS
decomposition is needed only for the original source. The localized weak
derivative and all radiation, hard-field and rest graphs are constructed.
Representative equalities connect the construction to the actual unitary
images used by `localizedConditionedSource`. -/

noncomputable section

set_option maxHeartbeats 1000000

namespace GptLean.RemovalEnergy.ConditionedSource

open MeasureTheory MeasureTheory.Measure Filter GptLean.Repair GptLean.SymmetricLift
open scoped ENNReal

variable {Q I H F : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [IsProbabilityMeasure μ] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private theorem complex_spatial_multiplier_memLp
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {η : SourceSpace I → ℝ} (hη : AEStronglyMeasurable η volume)
    {C : ℝ} (hb : ∀ x, |η x| ≤ C)
    (v : Lp K 2 (μ.prod (volume : Measure (SourceSpace I)))) :
    MemLp (fun p => (η p.2 : ℂ) • v p) 2 (μ.prod volume) := by
  apply (Lp.memLp v).smul
    (memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable hη.comp_snd) C _)
  exact Eventually.of_forall fun p => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb p.2

/-- Source-only PF data are stable under the actual localization product.
The three representative identities are the ordinary commutation of WIS
with spatial multiplication and the localized covariant product formula.
They contain no localized weak derivative or operator-domain premise. -/
def PFData.localize
    {S₀ S : ConditionedSource μ (volume : Measure (SourceSpace I)) I H F}
    {R : H →ₗ.[ℂ] H} {A : I → SourceSpace I → H →ₗ.[ℂ] H}
    {B : SourceSpace I → H →ₗ.[ℂ] F} {e : ℝ}
    {soft₀ : ℕ → I → Q × SourceSpace I → ℝ}
    (P₀ : S₀.PFData R A B e soft₀)
    (sourceIndex : ℕ → ℕ) (η : ℕ → SourceSpace I → ℝ)
    (dη : ℕ → I → SourceSpace I → ℝ)
    (hη : ∀ n, HasWeakH1Local (η n) (dη n))
    (C D : ℕ → ℝ)
    (hC : ∀ n x, |η n x| ≤ C n) (hD : ∀ n j x, |dη n j x| ≤ D n)
    (hsource : ∀ n, ∀ᵐ p ∂μ.prod volume,
      S.source n p = (η n p.2 : ℂ) • S₀.source (sourceIndex n) p)
    (hcovariant : ∀ n j, ∀ᵐ p ∂μ.prod volume,
      S.covariant n j p = (η n p.2 : ℂ) • S₀.covariant (sourceIndex n) j p -
        Complex.I • ((dη n j p.2 : ℂ) • S₀.source (sourceIndex n) p))
    (hrest : ∀ n, ∀ᵐ p ∂μ.prod volume,
      S.rest n p = (η n p.2 : ℂ) • S₀.rest (sourceIndex n) p) :
    S.PFData R A B e (fun n => soft₀ (sourceIndex n)) := by
  have hm (n) : AEStronglyMeasurable (η n) volume :=
    (finite_localMemLp_two_locallyIntegrable (hη n).function_memLp).aestronglyMeasurable
  have hdm (n j) : AEStronglyMeasurable (dη n j) volume :=
    (finite_localMemLp_two_locallyIntegrable ((hη n).derivative_memLp j)).aestronglyMeasurable
  let drv (n j) : Q × SourceSpace I → H := fun p =>
    (η n p.2 : ℂ) • P₀.derivative (sourceIndex n) j p +
      (dη n j p.2 : ℂ) • S₀.source (sourceIndex n) p
  have hd (n j) : MemLp (drv n j) 2 (μ.prod volume) :=
    (complex_spatial_multiplier_memLp (hm n) (hC n) (P₀.derivative (sourceIndex n) j)).add
      (complex_spatial_multiplier_memLp (hdm n j) (hD n j) (S₀.source (sourceIndex n)))
  let rad (n) : Q × SourceSpace I → H := fun p =>
    (η n p.2 : ℂ) • P₀.radiation (sourceIndex n) p
  have hr (n) : MemLp (rad n) 2 (μ.prod volume) :=
    complex_spatial_multiplier_memLp (hm n) (hC n) (P₀.radiation (sourceIndex n))
  let hard (n j) : Q × SourceSpace I → H := fun p =>
    (η n p.2 : ℂ) • P₀.hardField (sourceIndex n) j p
  have ha (n j) : MemLp (hard n j) 2 (μ.prod volume) :=
    complex_spatial_multiplier_memLp (hm n) (hC n) (P₀.hardField (sourceIndex n) j)
  refine {
    derivative := fun n j => (hd n j).toLp (drv n j)
    radiation := fun n => (hr n).toLp (rad n)
    hardField := fun n j => (ha n j).toLp (hard n j)
    weak := ?_
    radiation_graph := ?_
    hard_graph := ?_
    rest_graph := ?_
    covariant_eq := ?_
  }
  · intro n
    filter_upwards [P₀.weak (sourceIndex n), lp_sections_memLp (S₀.source (sourceIndex n)),
      ae_all_iff.mpr (fun j => lp_sections_memLp (P₀.derivative (sourceIndex n) j)),
      ae_ae_of_ae_prod (hsource n),
      ae_all_iff.mpr (fun j => ae_ae_of_ae_prod (hd n j).coeFn_toLp)]
      with q hw hψ hder hsrc hdrep
    have hk := weakH1Local_map Complex.ofRealCLM (hη n)
    have hkTop : MemLp (fun x => (η n x : ℂ)) ∞ volume :=
      memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable (hm n)) (C n)
        (Eventually.of_forall fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC n x)
    have hdkTop (j) : MemLp (fun x => (dη n j x : ℂ)) ∞ volume :=
      memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable (hdm n j)) (D n)
        (Eventually.of_forall fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hD n j x)
    have hout := weakH1Local_complex_smul_of_weighted hk hw
      (fun K _ => (hψ.smul hkTop).restrict K)
      (fun j K _ => ((hder j).smul hkTop).restrict K)
      (fun j K _ => (hψ.smul (hdkTop j)).restrict K)
    apply hout.congr
    · filter_upwards [hsrc] with x hx
      exact hx.symm
    · intro j
      filter_upwards [hdrep j] with x hx
      exact hx.symm
  · intro n
    filter_upwards [P₀.radiation_graph (sourceIndex n), hsource n, (hr n).coeFn_toLp]
      with p hp hs hrp
    rw [hs, hrp]
    exact R.graph.smul_mem (η n p.2 : ℂ) hp
  · intro n j
    filter_upwards [P₀.hard_graph (sourceIndex n) j, hsource n, (ha n j).coeFn_toLp]
      with p hp hs hap
    rw [hs, hap]
    exact (A j p.2).graph.smul_mem (η n p.2 : ℂ) hp
  · intro n
    filter_upwards [P₀.rest_graph (sourceIndex n), hsource n, hrest n] with p hp hs hrp
    rw [hs, hrp]
    exact (B p.2).graph.smul_mem (η n p.2 : ℂ) hp
  · intro n j
    filter_upwards [P₀.covariant_eq (sourceIndex n) j, hsource n, hcovariant n j,
      (hd n j).coeFn_toLp, (ha n j).coeFn_toLp] with p hp hs hc hdrep harep
    rw [hs, hc, hdrep, harep, hp]
    dsimp only [drv, hard]
    simp only [smul_sub, smul_add, smul_smul]
    module

end GptLean.RemovalEnergy.ConditionedSource
