import GptLean.PhotonLocalizationSharpKinetic

/-!
The sharp kinetic estimate attached to one common normal channel.

Each source consists of its actual derivative and field vectors. The
localized derivatives are the coordinates evaluated by the positive
kinetic form on the actual Kraus vectors. The energy estimate, output
finiteness and normal-state summation are derived here. Constructing these
vectors from the physical arbitrary-split covariant graph remains an
explicit obligation, rather than an assumed completed energy bound.
-/

namespace GptLean.PhotonLocalization

open PhotonLocalizationChannel
open scoped InnerProductSpace ENNReal

variable {H T ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T] [Fintype ι]
  {A : Gaussian.RankOneData H T} {Tr : RemovalState.PositiveTraceData T}

/-- Covariant graph and field vectors for one source and one dilation.
The source energy and every Kraus energy are evaluated by the same form.
The field conditions are the annihilation, creation and vacuum relations
with one bound for the physical cutoff kernels. -/
structure KineticDilationSource (kinetic controlForm : RemovalState.PositiveForm Tr)
    (U : KrausIsometry H) (v : H) (charge ε B K : ℝ) where
  control : ℝ
  control_nonneg : 0 ≤ control
  control_eq : controlForm.expectation (A.rankOne v) = ENNReal.ofReal control
  derivative : ι → H
  annihilated : ι → H
  created : ι → H
  noise : ι → lp (fun _ : ℕ => H) 2
  localized : ι → lp (fun _ : ℕ => H) 2
  radiationNorm : ℝ
  massNorm : ℝ
  radiationNorm_nonneg : 0 ≤ radiationNorm
  massNorm_nonneg : 0 ≤ massNorm
  annihilation : ∀ i, ‖annihilated i‖ ≤ ε * radiationNorm
  creation : ∀ i, ‖created i‖ ^ 2 ≤ ‖annihilated i‖ ^ 2 + ε ^ 2 * massNorm ^ 2
  scale_le : 2 * radiationNorm + massNorm ≤ B * Real.sqrt control
  mass_le : massNorm ^ 2 ≤ control
  derivative_le : ∑ i, ‖derivative i‖ ≤ K * Real.sqrt control
  noise_le : ∀ i, ‖noise i‖ ^ 2 ≤ charge ^ 2 * ε ^ 2 * massNorm ^ 2
  intertwining : ∀ i,
    localized i = U (derivative i + (charge : ℂ) • (annihilated i + created i)) + noise i
  orthogonality : ∀ i,
    ⟪U (derivative i + (charge : ℂ) • (annihilated i + created i)), noise i⟫_ℂ = 0
  original_form : kinetic.expectation (A.rankOne v) =
    ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖derivative i‖ ^ 2)
  coordinate_form : ∀ a, kinetic.expectation (A.rankOne (U v a)) =
    ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, ‖localized i a‖ ^ 2)

/-- The scalar error has no dependence on the spectral source index. -/
noncomputable def kineticError (ι : Type*) [Fintype ι] (charge B K ε : ℝ) : ℝ :=
  |charge| * B * K * ε +
    (Fintype.card ι : ℝ) / 2 * (charge ^ 2 * B ^ 2 + charge ^ 2) * ε ^ 2

theorem kineticError_nonneg {charge B K ε : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    0 ≤ kineticError ι charge B K ε := by
  unfold kineticError
  positivity

/-- The pure output estimate follows from the vector identities and
Kraus Parseval. In particular, its finite kinetic energy is not a field
of `KineticDilationSource`. -/
theorem KineticDilationSource.bound
    {kinetic controlForm : RemovalState.PositiveForm Tr}
    {U : KrausIsometry H} {v : H} {charge ε B K : ℝ}
    (S : KineticDilationSource (A := A) (ι := ι) kinetic controlForm U v charge ε B K)
    (hpositive : A.positive ⊆ Tr.positive) (hε : 0 ≤ ε) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    kinetic.expectation (pure A U v) ≤ kinetic.expectation (A.rankOne v) +
      ENNReal.ofReal (kineticError ι charge B K ε) * controlForm.expectation (A.rankOne v) := by
  have hf i : ‖S.annihilated i + S.created i‖ ≤ ε * (B * Real.sqrt S.control) :=
    (field_norm_le_of_ccr_le_cutoff (S.annihilated i) (S.created i)
      hε hε S.radiationNorm_nonneg S.massNorm_nonneg le_rfl le_rfl
      (S.annihilation i) (S.creation i)).trans
      (mul_le_mul_of_nonneg_left S.scale_le hε)
  have hn i : ‖S.noise i‖ ^ 2 ≤ charge ^ 2 * ε ^ 2 * S.control :=
    (S.noise_le i).trans (mul_le_mul_of_nonneg_left S.mass_le (by positivity))
  have hk := dilation_kinetic_bound U S.derivative
    (fun i => S.annihilated i + S.created i) S.noise S.localized
    hε hB S.control_nonneg hf hn S.derivative_le S.intertwining S.orthogonality
  rw [pure_kinetic_expectation kinetic hpositive U v S.localized S.coordinate_form,
    S.original_form, S.control_eq,
    ← ENNReal.ofReal_mul (kineticError_nonneg hB hK hε),
    ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (kineticError_nonneg hB hK hε) S.control_nonneg)]
  exact ENNReal.ofReal_le_ofReal hk

/-- Sharp kinetic comparison on the actual mixed output. Each source
comes from the original spectral expansion chosen by the normal trace
calculus. The estimate is additive in the controlling form and preserves
coefficient one on the original kinetic energy. -/
theorem channel_kinetic_of_dilations
    (N : NormalTraceData A) (kinetic controlForm : RemovalState.PositiveForm Tr)
    (hpositive : A.positive ⊆ Tr.positive) (U : KrausIsometry H)
    {charge ε B K : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (sources : ∀ v, controlForm.expectation (A.rankOne v) < ⊤ →
      Nonempty (KineticDilationSource (A := A) (ι := ι) kinetic controlForm U v charge ε B K))
    {x : T} (hx : x ∈ A.positive) (hfinite : controlForm.expectation x < ⊤) :
    kinetic.expectation (N.extend U x) ≤ kinetic.expectation x +
      ENNReal.ofReal (kineticError ι charge B K ε) * controlForm.expectation x := by
  apply channel_form_add_le_of_finite N kinetic kinetic controlForm hpositive U _ _ hx hfinite
  intro v hv
  obtain ⟨S⟩ := sources v hv
  exact S.bound hpositive hε hB hK

end GptLean.PhotonLocalization
