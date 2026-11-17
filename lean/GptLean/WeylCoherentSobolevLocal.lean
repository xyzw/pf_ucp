import GptLean.WeylCoherentSobolev

/-! Open-set versions of the complex coherent Sobolev chain rule.

The input uses local ambient H1 extensions of the field and its specified weak
derivative. The usual cutoff extension theorem identifies this interface with
test-function H1_loc on an open set. That equivalence is not proved here.
The output includes actual ambient weak W1,1 germs and compact-set integrability.
No coherent-state derivative or approximation is assumed in the input. -/

noncomputable section

namespace GptLean.Representability

open MeasureTheory SymmetricLift PhysicalFock
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types true

/-- Local ambient extensions of an H1 field on an open set. -/
structure HasLocalH1Extension {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set (CoherentBase d)) (f : CoherentBase d → E)
    (df : Fin d → CoherentBase d → E) : Prop where
  isOpen : IsOpen O
  function_memLp : ∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K)
  derivative_memLp : ∀ i K, IsCompact K → K ⊆ O → MemLp (df i) 2 (volume.restrict K)
  extension : ∀ x ∈ O, ∃ (U : Set (CoherentBase d)) (F : CoherentBase d → E)
    (dF : Fin d → CoherentBase d → E), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      HasWeakH1Local F dF ∧ f =ᵐ[volume.restrict U] F ∧
        ∀ i, df i =ᵐ[volume.restrict U] dF i

/-- Weak W1,1 membership locally on an open set, using ambient weak germs. -/
structure HasWeakW11On {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set (CoherentBase d)) (f : CoherentBase d → E)
    (df : Fin d → CoherentBase d → E) : Prop where
  isOpen : IsOpen O
  function_integrable : ∀ K, IsCompact K → K ⊆ O → Integrable f (volume.restrict K)
  derivative_integrable : ∀ i K, IsCompact K → K ⊆ O → Integrable (df i) (volume.restrict K)
  weak_extension : ∀ x ∈ O, ∃ (U : Set (CoherentBase d)) (F : CoherentBase d → E)
    (dF : Fin d → CoherentBase d → E), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      HasWeakW11Local F dF ∧ f =ᵐ[volume.restrict U] F ∧
        ∀ i, df i =ᵐ[volume.restrict U] dF i

/-- Local H1 membership as a weak derivative with locally L2 fields. -/
structure HasWeakH1On {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set (CoherentBase d)) (f : CoherentBase d → E)
    (df : Fin d → CoherentBase d → E) : Prop where
  weak_local : HasWeakW11On O f df
  function_memLp : ∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K)
  derivative_memLp : ∀ i K, IsCompact K → K ⊆ O → MemLp (df i) 2 (volume.restrict K)

namespace ConcreteWeylLaw

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (W : ConcreteWeylLaw μ) {d : ℕ} {O : Set (CoherentBase d)}
  {f : CoherentBase d → Lp ℂ 2 μ} {df : Fin d → CoherentBase d → Lp ℂ 2 μ}
  {S : CoherentBase d → ℝ} {dS : Fin d → CoherentBase d → ℝ}
  (hf : HasLocalH1Extension O f df) (hS : HasLocalH1Extension O S dS)

include hf hS

private theorem phase_local_measurable (K : Set (CoherentBase d))
    (hK : IsCompact K) (hKO : K ⊆ O) :
    AEStronglyMeasurable (fun x => W.phaseCoherent μ (S x) (f x)) (volume.restrict K) :=
  (W.phaseCoherent_continuous μ).comp_aestronglyMeasurable (f := fun x => (S x, f x))
    ((hS.function_memLp K hK hKO).1.prodMk (hf.function_memLp K hK hKO).1)

theorem phaseCoherent_memLp_on (K : Set (CoherentBase d)) (hK : IsCompact K) (hKO : K ⊆ O) :
    MemLp (fun x => W.phaseCoherent μ (S x) (f x)) 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.of_bound (phase_local_measurable μ W hf hS K hK hKO) 1
    (ae_of_all _ fun x => (W.phaseCoherent_norm μ (S x) (f x)).le)

private theorem phase_derivative_integrable_on (i : Fin d) (K : Set (CoherentBase d))
    (hK : IsCompact K) (hKO : K ⊆ O) :
    Integrable (fun x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x))
      (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have ha : MemLp (fun x => W.phaseHorizontal μ (S x) (f x) (df i x)) 2 (volume.restrict K) :=
    (hf.derivative_memLp i K hK hKO).mono
      ((W.phaseHorizontal_continuous μ).comp_aestronglyMeasurable (f := fun x => ((S x, f x), df i x))
        (((hS.function_memLp K hK hKO).1.prodMk (hf.function_memLp K hK hKO).1).prodMk
          (hf.derivative_memLp i K hK hKO).1))
      (ae_of_all _ fun x => (W.phaseHorizontal μ (S x) (f x)).norm_map (df i x) |>.le)
  have hb : Integrable (fun x => dS i x + (⟪f x, df i x⟫_ℂ).im) (volume.restrict K) :=
    (hS.derivative_memLp i K hK hKO).integrable (by norm_num) |>.add
      (memLp_one_iff_integrable.mp ((berryBilinear μ).memLp_of_bilin 1
        (hf.function_memLp K hK hKO) (hf.derivative_memLp i K hK hKO)))
  have hc := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Fock μ →L[ℝ] Fock μ).integrable_of_bilin_of_bdd_right
    1 hb ((phase_local_measurable μ W hf hS K hK hKO).const_smul Complex.I)
      (ae_of_all _ fun x => by
        change ‖Complex.I • W.phaseCoherent μ (S x) (f x)‖ ≤ 1
        rw [norm_smul, Complex.norm_I, W.phaseCoherent_norm, mul_one])
  exact (ha.integrable (by norm_num) |>.add hc).congr
    (ae_of_all _ fun x => (W.phaseCoherentDerivative_split μ (S x) (f x) (dS i x) (df i x)).symm)

/-- The complex coherent chain rule on an arbitrary open set in the local
ambient extension convention. -/
theorem phaseCoherent_weakW11_on :
    HasWeakW11On O (fun x => W.phaseCoherent μ (S x) (f x))
      (fun i x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x)) := by
  refine ⟨hf.isOpen, ?_, phase_derivative_integrable_on μ W hf hS, ?_⟩
  · intro K hK hKO
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (phaseCoherent_memLp_on μ W hf hS K hK hKO).integrable (by norm_num)
  · intro x hx
    obtain ⟨U, F, dF, hU, hxU, hUO, hF, heF, hedF⟩ := hf.extension x hx
    obtain ⟨V, T, dT, hV, hxV, hVO, hT, heT, hedT⟩ := hS.extension x hx
    refine ⟨U ∩ V, (fun y => W.phaseCoherent μ (T y) (F y)),
      (fun i y => W.phaseCoherentDerivative μ (T y) (F y) (dT i y) (dF i y)),
      hU.inter hV, ⟨hxU, hxV⟩, (Set.inter_subset_left.trans hUO),
      phaseCoherent_weakW11 μ W hF hT, ?_, ?_⟩
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left heF,
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right heT] with y hyF hyT
      exact congrArg₂ (W.phaseCoherent μ) hyT hyF
    · intro i
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left heF,
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right heT,
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hedF i),
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hedT i)] with y hyF hyT hydF hydT
      rw [hyF, hyT, hydF, hydT]

/-- The total Berry connection is precisely the additional local L2 input
needed to obtain an H1 coherent field. -/
theorem phaseCoherent_weakH1_on
    (hberry : ∀ i K, IsCompact K → K ⊆ O →
      MemLp (fun x => dS i x + (⟪f x, df i x⟫_ℂ).im) 2 (volume.restrict K)) :
    HasWeakH1On O (fun x => W.phaseCoherent μ (S x) (f x))
      (fun i x => W.phaseCoherentDerivative μ (S x) (f x) (dS i x) (df i x)) := by
  refine ⟨phaseCoherent_weakW11_on μ W hf hS, phaseCoherent_memLp_on μ W hf hS, ?_⟩
  intro i K hK hKO
  apply memLp_two_of_sq_norm_le
    (phase_derivative_integrable_on μ W hf hS i K hK hKO).aestronglyMeasurable
    (((hf.derivative_memLp i K hK hKO).integrable_norm_pow (by norm_num)).add
      ((hberry i K hK hKO).integrable_norm_pow (by norm_num)))
  exact ae_of_all _ fun x => by
    simp only [W.phaseCoherentDerivative_metric, Pi.add_apply, Real.norm_eq_abs, sq_abs, le_refl]

end ConcreteWeylLaw

end GptLean.Representability
