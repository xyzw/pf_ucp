import GptLean.Repair.WeightedFormDomain
import GptLean.Repair.ParameterSections

/-!
Physical quadratic-form evaluation of the actual coordinate channel.
The source is an arbitrary electronic H1 vector in the radiation form
domain. The only Hamiltonian background is its usual evaluation on that
reference domain. The multiplied vector's domain, weak derivative,
unbounded field action and remaining form components are all derived.

The rest operator may be the direct sum of the photon square-root energy
and multiplication by the square root of the Coulomb potential. It acts
on each electronic fibre as a partially defined complex-linear map.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal

variable {I : Type*} [Fintype I] [DecidableEq I] {V H F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Standard PF rank-one form evaluation on arbitrary reference-domain
vectors, with the actual partial field and rest operators. This background
does not refer to multipliers, channels or removal. -/
def HasPFFormEvaluation (R : H →ₗ.[ℂ] H)
    (A : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H)
    (B : EuclideanSpace ℝ I → H →ₗ.[ℂ] F)
    (e : ℝ) (q : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)) → ℝ≥0∞) : Prop :=
  ∀ (f : EuclideanSpace ℝ I → H)
    (df af : I → EuclideanSpace ℝ I → H)
    (bf : EuclideanSpace ℝ I → F) (hf : MemLp f 2 volume),
    InPFReferenceDomain R f → HasWeakH1Local f df →
    (∀ i, MemLp (df i) 2 volume) → (∀ i, MemLp (af i) 2 volume) →
    (∀ i, ∀ᵐ x ∂volume, (f x, af i x) ∈ (A i x).graph) →
    MemLp bf 2 volume → (∀ᵐ x ∂volume, (f x, bf x) ∈ (B x).graph) →
    q (hf.toLp f) = ENNReal.ofReal
      ((∫ x, 1 / 2 * ∑ i, ‖-Complex.I • df i x - (e : ℂ) • af i x‖ ^ 2) +
        (∫ x, ‖bf x‖ ^ 2))

/-- The usual rank-one PF form formula, applied to the actual coordinate
vector. The global form-evaluation premise concerns arbitrary vectors in
the reference domain, not this channel or its output.

For a positive form `E` and rank-one map `R₁`, take
`q v = E.expectation (R₁.rankOne v)`. The conclusion then supplies the
per-coordinate `rankOne_form` identity of the removal channel. -/
theorem coordinate_channel_form_evaluation
    (R : H →ₗ.[ℂ] H)
    (A : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H)
    (B : EuclideanSpace ℝ I → H →ₗ.[ℂ] F)
    (e : ℝ) (q : Lp H 2 (volume : Measure (EuclideanSpace ℝ I)) → ℝ≥0∞)
    (hform : HasPFFormEvaluation R A B e q)
    (basis : HilbertBasis ℕ ℂ V)
    {z : EuclideanSpace ℝ I → V}
    {dz : I → EuclideanSpace ℝ I → V}
    {ψ rψ : EuclideanSpace ℝ I → H}
    {dψ aψ : I → EuclideanSpace ℝ I → H}
    {rest : EuclideanSpace ℝ I → F}
    (hz : HasWeakH1Local z dz) (hunit : ∀ᵐ x ∂volume, ‖z x‖ ≤ 1)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ i, MemLp (dψ i) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)
    (haψ : ∀ i, MemLp (aψ i) 2 volume)
    (hfield : ∀ i, ∀ᵐ x ∂volume, (ψ x, aψ i x) ∈ (A i x).graph)
    (hrest : MemLp rest 2 volume)
    (hrestgraph : ∀ᵐ x ∂volume, (ψ x, rest x) ∈ (B x).graph)
    (hweight : ∀ i, Integrable (fun x => ‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2) volume)
    (a : ℕ) :
    ∃ hout : MemLp (channelValue basis z ψ a) 2 volume,
      InPFReferenceDomain R (channelValue basis z ψ a) ∧
      q (hout.toLp (channelValue basis z ψ a)) = ENNReal.ofReal
        ((∫ x, 1 / 2 * ∑ i,
          ‖channelDerivative basis z (dz i)
            (fun y => -Complex.I • dψ i y - (e : ℂ) • aψ i y) ψ a x‖ ^ 2) +
          (∫ x, ‖coordinate basis (z x) a • rest x‖ ^ 2)) := by
  let k := fun x => coordinate basis (z x) a
  let dk := fun i x => coordinate basis (dz i x) a
  have hk : HasWeakH1Local k dk :=
    weakH1Local_map ((innerSL ℂ (basis a)).restrictScalars ℝ) hz
  have hb : ∀ᵐ x ∂volume, ‖k x‖ ≤ 1 :=
    hunit.mono (fun x hx => (coordinate_norm_le basis (z x) a).trans hx)
  have hw (i) : MemLp (fun x => dk i x • ψ x) 2 volume :=
    coordinate_weighted_derivative_memLp basis hz hψ hweight a i
  obtain ⟨hv, hprod, hdprod, hrprod, hradprod⟩ :=
    pf_reference_product_of_weighted R hk hb hψ hweak hdψ hrψ hrad hw
  have href : InPFReferenceDomain R (fun x => k x • ψ x) :=
    ⟨hv, _, _, hprod, hdprod, hrprod, hradprod⟩
  have hktop : MemLp k ∞ volume := memLp_top_of_bound
    (finite_localMemLp_two_locallyIntegrable hk.function_memLp).aestronglyMeasurable 1 hb
  have haf (i) : MemLp (fun x => k x • aψ i x) 2 volume := (haψ i).smul hktop
  have hfg (i) : ∀ᵐ x ∂volume, (k x • ψ x, k x • aψ i x) ∈ (A i x).graph := by
    filter_upwards [hfield i] with x hx
    exact (A i x).graph.smul_mem (k x) hx
  have hr : MemLp (fun x => k x • rest x) 2 volume := hrest.smul hktop
  have hrg : ∀ᵐ x ∂volume, (k x • ψ x, k x • rest x) ∈ (B x).graph := by
    filter_upwards [hrestgraph] with x hx
    exact (B x).graph.smul_mem (k x) hx
  have hvalue := hform _ _ _ _ hv href hprod hdprod haf hfg hr hrg
  refine ⟨hv, href, hvalue.trans ?_⟩
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    dsimp [channelDerivative, k, dk]
    simp only [smul_add, smul_sub, neg_smul, smul_smul]
    module

/-- The parameter-section convention is the proved L2 vector whenever the
actual coordinate product is square integrable. This includes every
nonexceptional conditional parameter supplied to the theorem above. -/
theorem coordinate_toL2Section_eq {P : Type*}
    (basis : HilbertBasis ℕ ℂ V)
    (z : P → EuclideanSpace ℝ I → V)
    (ψ : P → EuclideanSpace ℝ I → H) (p : P) (a : ℕ)
    (h : MemLp (channelValue basis (z p) (ψ p) a) 2 volume) :
    toL2Section (μ := volume)
      (fun p x => coordinate basis (z p x) a • ψ p x) p =
      h.toLp (channelValue basis (z p) (ψ p) a) :=
  toL2Section_eq h

end GptLean.Repair
