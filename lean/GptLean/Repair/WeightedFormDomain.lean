import GptLean.Repair.WeakMultiplierProduct
import GptLean.Repair.ClosedCovariant
import GptLean.SymmetricLift.L2Dominated

/-!
Multiplication on the Pauli--Fierz reference form domain.

The photon operator is a partially defined complex-linear operator on the
actual fibre Hilbert space. Its graph, rather than an everywhere-defined
linear surrogate, specifies the radiation derivative. The reference
domain is the ordinary electronic weak H1 space intersected with this
operator domain in Bochner L2. The standard canonical PF form-domain
identity can then identify it with the physical form domain.

The product theorem proves the target's weak derivative and radiation
graph membership. Only the weighted multiplier derivative is required in
L2. No bounded derivative or weighted source-core approximation is used.
The final theorem identifies the actual unbounded field action and the
covariant derivative of the multiplied vector.
-/

noncomputable section

namespace GptLean.Repair

open MeasureTheory Filter GptLean.SymmetricLift
open scoped ENNReal Topology

section WeightedClosure

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A graph limit with a separately convergent commutator term allows an
unbounded commutator. It does not require a bounded map on the source L2
space. The weak-product theorem below avoids even this approximation
premise when the weighted derivative is square integrable. -/
theorem closed_covariant_product_of_weighted_graph_limit
    (D : E →ₗ.[𝕜] F) (hD : D.IsClosed)
    (M : E →L[𝕜] E) (N : F →L[𝕜] F)
    {u : E} {du c : F} (un : ℕ → D.domain) (cn : ℕ → F)
    (hu : Tendsto (fun n => (un n : E)) atTop (𝓝 u))
    (hdu : Tendsto (fun n => D (un n)) atTop (𝓝 du))
    (hc : Tendsto cn atTop (𝓝 c))
    (hcore : ∀ n, (M (un n : E), N (D (un n)) + cn n) ∈ D.graph) :
    ∃ v : D.domain, (v : E) = M u ∧ D v = N du + c := by
  change IsClosed (D.graph : Set (E × F)) at hD
  exact (D.mem_graph_iff).mp
    (hD.mem_of_tendsto (((M.continuous.tendsto u).comp hu).prodMk_nhds
      (((N.continuous.tendsto du).comp hdu).add hc)) (Eventually.of_forall hcore))

end WeightedClosure

section Reference

variable {I : Type*} [Fintype I] [DecidableEq I] {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical PF reference domain, written for raw representatives.
`R` is the photon square-root energy operator. The derivative identities
are tested against compact smooth functions. -/
def InPFReferenceDomain (R : H →ₗ.[ℂ] H)
    (ψ : EuclideanSpace ℝ I → H) : Prop :=
  MemLp ψ 2 volume ∧ ∃ (dψ : I → EuclideanSpace ℝ I → H)
    (rψ : EuclideanSpace ℝ I → H),
    HasWeakH1Local ψ dψ ∧ (∀ i, MemLp (dψ i) 2 volume) ∧
    MemLp rψ 2 volume ∧ (∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)

/-- Scalar multiplication preserves the domain of an actual unbounded
fibre operator and commutes with its action. -/
theorem scalar_smul_mem_unbounded_graph {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (R : H →ₗ.[ℂ] H) (k : X → ℂ) {ψ rψ : X → H}
    (h : ∀ᵐ x ∂μ, (ψ x, rψ x) ∈ R.graph) :
    ∀ᵐ x ∂μ, (k x • ψ x, k x • rψ x) ∈ R.graph := by
  filter_upwards [h] with x hx
  exact R.graph.smul_mem (k x) hx

/-- Finiteness of the actual weighted derivative integral is exactly what
is needed. Singular derivatives need not define a bounded L2 multiplier. -/
theorem weighted_derivative_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {k : X → ℂ} {ψ : X → H}
    (hk : AEStronglyMeasurable k μ) (hψ : AEStronglyMeasurable ψ μ)
    (hweight : Integrable (fun x => ‖k x‖ ^ 2 * ‖ψ x‖ ^ 2) μ) :
    MemLp (fun x => k x • ψ x) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (hk.smul hψ)).mpr
  change Integrable (fun x => ‖k x • ψ x‖ ^ 2) μ
  simpa only [norm_smul, mul_pow] using hweight

/-- A bounded weak multiplier with a square-integrable weighted gradient
maps a PF reference-domain vector into the same domain. Its derivatives
and radiation action are explicitly identified. -/
theorem pf_reference_product_of_weighted
    (R : H →ₗ.[ℂ] H)
    {k : EuclideanSpace ℝ I → ℂ}
    {dk : I → EuclideanSpace ℝ I → ℂ}
    {ψ rψ : EuclideanSpace ℝ I → H}
    {dψ : I → EuclideanSpace ℝ I → H}
    (hk : HasWeakH1Local k dk) {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖k x‖ ≤ C)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ i, MemLp (dψ i) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)
    (hweight : ∀ i, MemLp (fun x => dk i x • ψ x) 2 volume) :
    MemLp (fun x => k x • ψ x) 2 volume ∧
    HasWeakH1Local (fun x => k x • ψ x)
      (fun i x => k x • dψ i x + dk i x • ψ x) ∧
    (∀ i, MemLp (fun x => k x • dψ i x + dk i x • ψ x) 2 volume) ∧
    MemLp (fun x => k x • rψ x) 2 volume ∧
    (∀ᵐ x ∂volume, (k x • ψ x, k x • rψ x) ∈ R.graph) := by
  have hkm := (finite_localMemLp_two_locallyIntegrable hk.function_memLp).aestronglyMeasurable
  have hktop : MemLp k ∞ volume := memLp_top_of_bound hkm C hbound
  have hv : MemLp (fun x => k x • ψ x) 2 volume := hψ.smul hktop
  have hd (i) : MemLp (fun x => k x • dψ i x) 2 volume := (hdψ i).smul hktop
  refine ⟨hv, weakH1Local_complex_smul_of_weighted hk hweak
    (fun _ _ => hv.restrict _) (fun i _ _ => (hd i).restrict _)
    (fun i _ _ => (hweight i).restrict _), fun i => (hd i).add (hweight i),
    hrψ.smul hktop, scalar_smul_mem_unbounded_graph R k hrad⟩

/-- Domain membership follows from the explicit product theorem. -/
theorem pf_reference_mem_of_weighted
    (R : H →ₗ.[ℂ] H)
    {k : EuclideanSpace ℝ I → ℂ}
    {dk : I → EuclideanSpace ℝ I → ℂ}
    {ψ : EuclideanSpace ℝ I → H}
    (hk : HasWeakH1Local k dk) {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖k x‖ ≤ C)
    (hψ : InPFReferenceDomain R ψ)
    (hweight : ∀ i, MemLp (fun x => dk i x • ψ x) 2 volume) :
    InPFReferenceDomain R (fun x => k x • ψ x) := by
  obtain ⟨hψ, dψ, rψ, hweak, hdψ, hrψ, hrad⟩ := hψ
  obtain ⟨hv, hw, hd, hr, hg⟩ :=
    pf_reference_product_of_weighted R hk hbound hψ hweak hdψ hrψ hrad hweight
  exact ⟨hv, _, _, hw, hd, hr, hg⟩

/-- Permutation-invariant scalar multipliers preserve the fermionic
transformation law. The same statement handles any unit-modulus character. -/
theorem scalar_multiplier_preserves_character {X G : Type*}
    (T : G → X → X) (χ : G → ℂ) {k : X → ℂ} {ψ : X → H}
    (hk : ∀ g x, k (T g x) = k x)
    (hψ : ∀ g x, ψ (T g x) = χ g • ψ x) :
    ∀ g x, k (T g x) • ψ (T g x) = χ g • (k x • ψ x) := by
  intro g x
  rw [hk, hψ, smul_comm]

/-- The almost-everywhere electronic transformation law. For fermions,
`G` is the permutation group, `T` permutes the electronic coordinates and
`χ` is the sign character. -/
def HasElectronicCharacter {G : Type*}
    (T : G → EuclideanSpace ℝ I → EuclideanSpace ℝ I) (χ : G → ℂ)
    (ψ : EuclideanSpace ℝ I → H) : Prop :=
  ∀ g, ∀ᵐ x ∂volume, ψ (T g x) = χ g • ψ x

theorem electronicCharacter_smul {G : Type*}
    (T : G → EuclideanSpace ℝ I → EuclideanSpace ℝ I) (χ : G → ℂ)
    {k : EuclideanSpace ℝ I → ℂ} {ψ : EuclideanSpace ℝ I → H}
    (hk : ∀ g, ∀ᵐ x ∂volume, k (T g x) = k x)
    (hψ : HasElectronicCharacter T χ ψ) :
    HasElectronicCharacter T χ (fun x => k x • ψ x) := by
  intro g
  filter_upwards [hk g, hψ g] with x hkx hψx
  rw [hkx, hψx, smul_comm]

/-- With the standard canonical fermionic PF reference-domain identity,
the actual L2 vector lies in the physical form domain. The identity is
background about the Hamiltonian, independent of the multiplier being
constructed. Antisymmetry is derived from scalar permutation invariance. -/
theorem physical_pf_form_domain_of_weighted {G : Type*}
    (R : H →ₗ.[ℂ] H) (Q : Submodule ℂ (Lp H 2 (volume : Measure (EuclideanSpace ℝ I))))
    (T : G → EuclideanSpace ℝ I → EuclideanSpace ℝ I) (χ : G → ℂ)
    (hcanonical : ∀ (f : EuclideanSpace ℝ I → H) (hf : MemLp f 2 volume),
      hf.toLp f ∈ Q ↔ HasElectronicCharacter T χ f ∧ InPFReferenceDomain R f)
    {k : EuclideanSpace ℝ I → ℂ}
    {dk : I → EuclideanSpace ℝ I → ℂ}
    {ψ : EuclideanSpace ℝ I → H}
    (hk : HasWeakH1Local k dk) {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖k x‖ ≤ C)
    (hinv : ∀ g, ∀ᵐ x ∂volume, k (T g x) = k x)
    (hψ : MemLp ψ 2 volume) (hQ : hψ.toLp ψ ∈ Q)
    (hweight : ∀ i, MemLp (fun x => dk i x • ψ x) 2 volume) :
    ∃ hout : MemLp (fun x => k x • ψ x) 2 volume,
      hout.toLp (fun x => k x • ψ x) ∈ Q := by
  obtain ⟨hsym, href⟩ := (hcanonical ψ hψ).mp hQ
  have h := pf_reference_mem_of_weighted R hk hbound href hweight
  exact ⟨h.1, (hcanonical _ h.1).mpr ⟨electronicCharacter_smul T χ hinv hsym, h⟩⟩

/-- The physical field bound converts radiation-domain control into L2
control of the unbounded vector-potential action. -/
theorem pf_field_action_memLp {ψ rψ aψ : EuclideanSpace ℝ I → H}
    (hψ : MemLp ψ 2 volume) (hrψ : MemLp rψ 2 volume)
    (haψ : AEStronglyMeasurable aψ volume) (C : ℝ)
    (hbound : ∀ᵐ x ∂volume, ‖aψ x‖ ^ 2 ≤ C * (‖ψ x‖ ^ 2 + ‖rψ x‖ ^ 2)) :
    MemLp aψ 2 volume := by
  have h₁ := (memLp_two_iff_integrable_sq_norm hψ.1).mp hψ
  have h₂ := (memLp_two_iff_integrable_sq_norm hrψ.1).mp hrψ
  exact memLp_two_of_sq_norm_le haψ ((h₁.add h₂).const_mul C) hbound

/-- The value of a partially defined fibre operator, with zero only
outside its domain. Domain membership is proved before this convention is
used in any form formula. -/
def fibreOperatorValue {X : Type*} (A : X → H →ₗ.[ℂ] H) (ψ : X → H) (x : X) : H := by
  classical
  exact if h : ψ x ∈ (A x).domain then A x ⟨ψ x, h⟩ else 0

/-- The usual radiation-relative field bound supplies both the actual
field graph membership and global L2 control, starting only from the
radiation graph of the source. -/
theorem pf_source_field_of_radiation_bound
    (R : H →ₗ.[ℂ] H) (A : EuclideanSpace ℝ I → H →ₗ.[ℂ] H)
    (hdom : ∀ x, R.domain ≤ (A x).domain)
    (C : ℝ)
    (hbound : ∀ x (u : R.domain),
      ‖A x ⟨u, hdom x u.property⟩‖ ^ 2 ≤ C * (‖(u : H)‖ ^ 2 + ‖R u‖ ^ 2))
    {ψ rψ : EuclideanSpace ℝ I → H}
    (hψ : MemLp ψ 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)
    (hmeas : AEStronglyMeasurable (fibreOperatorValue A ψ) volume) :
    (∀ᵐ x ∂volume, (ψ x, fibreOperatorValue A ψ x) ∈ (A x).graph) ∧
    MemLp (fibreOperatorValue A ψ) 2 volume := by
  have hg : ∀ᵐ x ∂volume, (ψ x, fibreOperatorValue A ψ x) ∈ (A x).graph ∧
      ‖fibreOperatorValue A ψ x‖ ^ 2 ≤ C * (‖ψ x‖ ^ 2 + ‖rψ x‖ ^ 2) := by
    filter_upwards [hrad] with x hx
    obtain ⟨u, hu, hRu⟩ := R.mem_graph_iff.mp hx
    change (u : H) = ψ x at hu
    change R u = rψ x at hRu
    have hm : ψ x ∈ (A x).domain := by rw [← hu]; exact hdom x u.property
    have he : fibreOperatorValue A ψ x = A x ⟨u, hdom x u.property⟩ := by
      simp only [fibreOperatorValue, dite_eq_left hm]
      apply congrArg (A x)
      exact Subtype.ext hu.symm
    refine ⟨(A x).mem_graph_iff.mpr ⟨⟨u, hdom x u.property⟩, hu, he.symm⟩, ?_⟩
    simpa only [he, hu, hRu] using hbound x u
  exact ⟨hg.mono (fun _ h => h.1),
    pf_field_action_memLp hψ hrψ hmeas C (hg.mono (fun _ h => h.2))⟩

/-- On the proved weak-product domain, the candidate derivative used by
the repair energy formula is the actual covariant derivative. The field
operators are partially defined and their target graph memberships are
proved by scalar linearity. -/
theorem pf_covariant_product_of_weighted
    (R : H →ₗ.[ℂ] H)
    (A : I → EuclideanSpace ℝ I → H →ₗ.[ℂ] H) (e : ℝ)
    {k : EuclideanSpace ℝ I → ℂ}
    {dk : I → EuclideanSpace ℝ I → ℂ}
    {ψ rψ : EuclideanSpace ℝ I → H}
    {dψ aψ : I → EuclideanSpace ℝ I → H}
    (hk : HasWeakH1Local k dk) {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖k x‖ ≤ C)
    (hψ : MemLp ψ 2 volume) (hweak : HasWeakH1Local ψ dψ)
    (hdψ : ∀ i, MemLp (dψ i) 2 volume) (hrψ : MemLp rψ 2 volume)
    (hrad : ∀ᵐ x ∂volume, (ψ x, rψ x) ∈ R.graph)
    (hweight : ∀ i, MemLp (fun x => dk i x • ψ x) 2 volume)
    (haψ : ∀ i, MemLp (aψ i) 2 volume)
    (hfield : ∀ i, ∀ᵐ x ∂volume, (ψ x, aψ i x) ∈ (A i x).graph) :
    InPFReferenceDomain R (fun x => k x • ψ x) ∧
    HasWeakH1Local (fun x => k x • ψ x)
      (fun i x => k x • dψ i x + dk i x • ψ x) ∧
    (∀ i, ∀ᵐ x ∂volume, (k x • ψ x, k x • aψ i x) ∈ (A i x).graph) ∧
    (∀ i, MemLp (fun x => -Complex.I • (k x • dψ i x + dk i x • ψ x) -
      (e : ℂ) • (k x • aψ i x)) 2 volume) ∧
    (∀ i x, -Complex.I • (k x • dψ i x + dk i x • ψ x) -
      (e : ℂ) • (k x • aψ i x) =
      k x • (-Complex.I • dψ i x - (e : ℂ) • aψ i x) -
        Complex.I • dk i x • ψ x) := by
  obtain ⟨hv, hw, hd, hr, hg⟩ :=
    pf_reference_product_of_weighted R hk hbound hψ hweak hdψ hrψ hrad hweight
  have hktop : MemLp k ∞ volume := memLp_top_of_bound
    (finite_localMemLp_two_locallyIntegrable hk.function_memLp).aestronglyMeasurable C hbound
  refine ⟨⟨hv, _, _, hw, hd, hr, hg⟩, hw, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hfield i] with x hx
    exact (A i x).graph.smul_mem (k x) hx
  · intro i
    exact ((hd i).const_smul (-Complex.I)).sub (((haψ i).smul hktop).const_smul (e : ℂ))
  · intro i x
    simp only [smul_add, smul_sub, neg_smul, smul_smul]
    module

end Reference

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I] {ι V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The weighted Hilbert-valued lift metric controls every coordinate
multiplier derivative. No bound on its essential supremum is needed. -/
theorem coordinate_weighted_derivative_memLp
    (b : HilbertBasis ι ℂ V)
    {z : EuclideanSpace ℝ I → V}
    {dz : I → EuclideanSpace ℝ I → V}
    {ψ : EuclideanSpace ℝ I → H}
    (hz : HasWeakH1Local z dz) (hψ : MemLp ψ 2 volume)
    (hweight : ∀ i, Integrable (fun x => ‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2) volume)
    (a : ι) (i : I) :
    MemLp (fun x => coordinate b (dz i x) a • ψ x) 2 volume := by
  have hdz := (finite_localMemLp_two_locallyIntegrable (hz.derivative_memLp i)).aestronglyMeasurable
  apply memLp_two_of_sq_norm_le ((coordinate_aestronglyMeasurable b hdz a).smul hψ.1)
    (hweight i)
  exact Eventually.of_forall fun x => by
    change ‖coordinate b (dz i x) a • ψ x‖ ^ 2 ≤ ‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (coordinate_norm_le b (dz i x) a) 2) (sq_nonneg _)

/-- Every coordinate of the actual weak tensor lift maps a general PF
reference-domain source into that domain under the weighted metric bound. -/
theorem coordinate_channel_pf_reference
    (R : H →ₗ.[ℂ] H) (b : HilbertBasis ι ℂ V)
    {z : EuclideanSpace ℝ I → V}
    {dz : I → EuclideanSpace ℝ I → V}
    {ψ : EuclideanSpace ℝ I → H}
    (hz : HasWeakH1Local z dz) (hunit : ∀ᵐ x ∂volume, ‖z x‖ ≤ 1)
    (hψ : InPFReferenceDomain R ψ)
    (hweight : ∀ i, Integrable (fun x => ‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2) volume)
    (a : ι) :
    InPFReferenceDomain R (fun x => coordinate b (z x) a • ψ x) := by
  apply pf_reference_mem_of_weighted R
    (weakH1Local_map ((innerSL ℂ (b a)).restrictScalars ℝ) hz)
    (hunit.mono (fun x hx => (coordinate_norm_le b (z x) a).trans hx)) hψ
  exact coordinate_weighted_derivative_memLp b hz hψ.1 hweight a

/-- In exact removal the local metric bound is finite for each measured
parameter. It proves every weighted derivative integral from the source
mass, so the coordinate-domain theorem adds no new integrability premise. -/
theorem weighted_lift_integrable_of_metric_bound
    {z : EuclideanSpace ℝ I → V}
    {dz : I → EuclideanSpace ℝ I → V}
    {ψ : EuclideanSpace ℝ I → H}
    (hz : HasWeakH1Local z dz) (hψ : MemLp ψ 2 volume) (M : ℝ)
    (hmetric : ∀ᵐ x ∂volume, ∑ i, ‖dz i x‖ ^ 2 ≤ M) (i : I) :
    Integrable (fun x => ‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2) volume := by
  have hmass := (memLp_two_iff_integrable_sq_norm hψ.1).mp hψ
  have hdz := (finite_localMemLp_two_locallyIntegrable (hz.derivative_memLp i)).aestronglyMeasurable
  apply (hmass.const_mul M).mono' ((hdz.norm.pow 2).mul (hψ.1.norm.pow 2))
  filter_upwards [hmetric] with x hx
  change ‖‖dz i x‖ ^ 2 * ‖ψ x‖ ^ 2‖ ≤ M * ‖ψ x‖ ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    ((Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (I))) =>
      sq_nonneg ‖dz j x‖) (Finset.mem_univ i)).trans hx) (sq_nonneg _)

end Coordinates

end GptLean.Repair
