import PfHk.PhysicalLocalEnergyDiamagnetic
import PfHk.PhysicalLocalEnergyRoughIMS

/-! Transfer of scalar Sobolev multiplication bounds to the physical PF
form. The scalar hypothesis is quantified over every real weak H1
function. In particular it contains no Fock operator, physical state,
covariant derivative or localization estimate. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply
  externalCovariant externalEnergy roughMultiply normGradientEnergy
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier

variable {I : Type} [Fintype I] [DecidableEq I]

theorem real_smul_norm_sq {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (a : ℝ) (u : H) : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

private theorem complex_real_smul_norm {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (a : ℝ) (u : H) : ‖(a : ℂ) • u‖ = |a| * ‖u‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

private theorem covariant_triangle {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (d p f a : H) (e : ℝ)
    (h : (-Complex.I) • d = p + (e : ℂ) • f - a) :
    ‖d‖ ≤ ‖p‖ + |e| * ‖f‖ + ‖a‖ := by
  calc
    ‖d‖ = ‖(-Complex.I) • d‖ := (norm_negI_smul d).symm
    _ = ‖p + (e : ℂ) • f - a‖ := congrArg norm h
    _ ≤ ‖p + (e : ℂ) • f‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ (‖p‖ + ‖(e : ℂ) • f‖) + ‖a‖ := add_le_add (norm_add_le p ((e : ℂ) • f)) le_rfl
    _ = _ := congrArg (fun z : ℝ => (‖p‖ + z) + ‖a‖) (complex_real_smul_norm e f)

private theorem three_square_bound (a b c d e : ℝ) (hd : 0 ≤ d)
    (h : d ≤ a + |e| * b + c) : d ^ 2 ≤ 3 * a ^ 2 + 3 * e ^ 2 * b ^ 2 + 3 * c ^ 2 := by
  have hs := pow_le_pow_left₀ hd h 2
  have habs : (|e| * b) ^ 2 = e ^ 2 * b ^ 2 := by rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg (a - |e| * b), sq_nonneg (a - c), sq_nonneg (|e| * b - c)]

/-- The ordinary scalar Sobolev multiplication bound, stated independently
of any physical model. Coordinatewise L3/2+L∞ form bounds and L3+L∞
multiplier bounds have this form after Fubini. -/
def ScalarMultiplierBound (w : Position I → ℝ) (ε C : ℝ) : Prop :=
  ∀ (f : Position I → ℝ) (g : I → Position I → ℝ),
    SymmetricLift.HasWeakH1Local f g → MemLp f 2 volume →
    (∀ i, MemLp (g i) 2 volume) →
    (∫ x, w x ^ 2 * f x ^ 2) ≤
      ε * (∑ i, ∫ x, g i x ^ 2) + C * ∫ x, f x ^ 2

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

theorem roughMultiply_norm_sq (w : Position I → ℝ)
    (u : WaveSpace I) (hu : HasMultiplier w u) :
    ‖roughMultiply w u hu‖ ^ 2 = ∫ x, w x ^ 2 * ‖u x‖ ^ 2 := by
  apply (l2_norm_sq (roughMultiply w u hu)).trans
  apply integral_congr_ae
  filter_upwards [roughMultiply_ae w u hu] with x hx
  exact (congrArg (fun z : PhotonFock => ‖z‖ ^ 2) hx).trans (real_smul_norm_sq _ _)

/-- A scalar Sobolev estimate acts on the norm of the actual PF vector. -/
theorem scalar_bound_on_physical_norm (w : Position I → ℝ) (ε C₀ : ℝ)
    (hSob : ScalarMultiplierBound w ε C₀) (u : Reference I V)
    (hu : HasMultiplier w (inclusion I V u)) :
    ‖roughMultiply w (inclusion I V u) hu‖ ^ 2 ≤
      ε * normGradientEnergy V u + C₀ * ‖inclusion I V u‖ ^ 2 := by
  have hb : (∫ x, w x ^ 2 * ‖inclusion I V u x‖ ^ 2) ≤
      ε * normGradientEnergy V u + C₀ * ∫ x, ‖inclusion I V u x‖ ^ 2 := by
    unfold normGradientEnergy
    exact hSob (fun x => ‖inclusion I V u x‖) (normGradient V u)
      (normGradient_weak V u) (Lp.memLp (inclusion I V u)).norm (normGradient_memLp V u)
  exact (roughMultiply_norm_sq w (inclusion I V u) hu).le.trans
    (hb.trans_eq (congrArg (fun z : ℝ => ε * normGradientEnergy V u + C₀ * z)
      (l2_norm_sq (inclusion I V u)).symm))

/-- The quarter-kinetic lower bound is derived from diamagnetism and
the ordinary scalar form bound with coefficient one quarter. -/
theorem external_form_lower_bound (C₀ : ℝ)
    (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    (u : Reference I V) (hu : ExternalDomain V A positive negative u) :
    (1 / 4 : ℝ) * (∑ i,
      ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2) +
      ‖radiation I V u‖ ^ 2 - C₀ * ‖inclusion I V u‖ ^ 2 ≤
        externalEnergy V C κ hκ M hbound e A positive negative u hu := by
  have hn := scalar_bound_on_physical_norm V negative (1 / 4) C₀ hSob u hu.negative
  have hd := diamagnetic_integrated V C κ hκ M hbound e A positive negative u hu
  unfold externalEnergy
  linarith [sq_nonneg ‖potential I V u‖,
    sq_nonneg ‖roughMultiply positive (inclusion I V u) hu.positive‖]

/-- Localization plus the lower form bound controls the full localized
covariant, radiation and norm-gradient energies. -/
theorem localized_covariant_energy {E : ℝ} {u : Reference I V}
    {hu : ExternalDomain V A positive negative u}
    (heigen : IsExternalWeakEigenstate V C κ hκ M hbound e A positive negative E u hu)
    (C₀ : ℝ) (hSob : ScalarMultiplierBound negative (1 / 4) C₀)
    (a : DifferentiableMultiplier I) :
    (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) i‖ ^ 2) +
      ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a u)‖ ^ 2 +
      normGradientEnergy V (PhysicalPFScalarMultiplier.multiply V a u) ≤
      8 * ((|E| + |C₀|) * ‖a.multiplier (inclusion I V u)‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ i, ‖a.derivativeMultiplier i (inclusion I V u)‖ ^ 2) := by
  have hl := external_form_lower_bound V C κ hκ M hbound e A positive negative
    C₀ hSob (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a)
  have he := external_eigenstate_ims V C κ hκ M hbound e A positive negative heigen a
  have hd := diamagnetic_integrated V C κ hκ M hbound e A positive negative
    (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a)
  have hl' := hl.trans_eq he
  have hv := congrArg (fun z : WaveSpace I => C₀ * ‖z‖ ^ 2)
    (PhysicalPFScalarMultiplier.value_multiply V a u)
  have hkin : 0 ≤ ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr := sq_nonneg ‖radiation I V (PhysicalPFScalarMultiplier.multiply V a u)‖
  have hE := mul_le_mul_of_nonneg_right (le_abs_self E)
    (sq_nonneg ‖a.multiplier (inclusion I V u)‖)
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C₀)
    (sq_nonneg ‖a.multiplier (inclusion I V u)‖)
  linarith only [hl', hv, hd, hkin, hr, hE, hC]

theorem ordinary_norm_le_external (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (i : I) :
    ‖ordinary I V i u‖ ≤
      ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ +
      |e| * ‖field I V C κ hκ M hbound i u‖ +
      ‖roughMultiply (A i) (inclusion I V u) (hu.vector i)‖ := by
  have hid : (-Complex.I) • ordinary I V i u =
      externalCovariant V C κ hκ M hbound e A positive negative u hu i +
      (e : ℂ) • field I V C κ hκ M hbound i u -
      roughMultiply (A i) (inclusion I V u) (hu.vector i) := by
    have he : externalCovariant V C κ hκ M hbound e A positive negative u hu i =
        (-Complex.I) • ordinary I V i u - (e : ℂ) • field I V C κ hκ M hbound i u +
        roughMultiply (A i) (inclusion I V u) (hu.vector i) := by
      unfold externalCovariant
      exact congrArg (fun z : WaveSpace I => z +
        roughMultiply (A i) (inclusion I V u) (hu.vector i))
        (covariant_apply I V C κ hκ M hbound e i u)
    have halg (p f a : WaveSpace I) : p = (p - f + a) + f - a := by abel
    exact (halg _ _ _).trans
      (congrArg (fun z : WaveSpace I => z +
        (e : ℂ) • field I V C κ hκ M hbound i u -
        roughMultiply (A i) (inclusion I V u) (hu.vector i)) he.symm)
  exact covariant_triangle (H := WaveSpace I) _ _ _ _ e hid

theorem ordinary_sq_le_external (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (i : I) :
    ‖ordinary I V i u‖ ^ 2 ≤
      3 * ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 +
      3 * e ^ 2 * ‖field I V C κ hκ M hbound i u‖ ^ 2 +
      3 * ‖roughMultiply (A i) (inclusion I V u) (hu.vector i)‖ ^ 2 := by
  exact three_square_bound _ _ _ _ e (norm_nonneg _)
    (ordinary_norm_le_external V C κ hκ M hbound e A positive negative u hu i)

theorem uniform_field_bound (u : Reference I V) (i : I) :
    ‖field I V C κ hκ M hbound i u‖ ^ 2 ≤
      8 * (max M 0) ^ 2 * ‖radiation I V u‖ ^ 2 +
        2 * (max M 0) ^ 2 * ‖inclusion I V u‖ ^ 2 := by
  apply field_radiation_bound I V C κ hκ M hbound i
    (max M 0) (max M 0) (le_max_right _ _) (le_max_right _ _)
  · filter_upwards [hbound i] with x hx
    exact (norm_snd_le (κ i x).val).trans (hx.trans (le_max_left _ _))
  · filter_upwards [hbound i] with x hx
    exact (norm_fst_le (κ i x).val).trans (hx.trans (le_max_left _ _))

/-- Ordinary electronic derivatives are controlled through the actual
annihilation/creation bound and the scalar Sobolev bound for A. -/
theorem ordinary_energy_bound (C_A : ℝ)
    (hA : ∀ i, ScalarMultiplierBound (A i) 1 C_A)
    (u : Reference I V) (hu : ExternalDomain V A positive negative u) :
    (∑ i, ‖ordinary I V i u‖ ^ 2) ≤
      3 * (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2) +
      3 * (Fintype.card I) * normGradientEnergy V u +
      24 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I) * ‖radiation I V u‖ ^ 2 +
      (6 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I) + 3 * C_A * (Fintype.card I)) *
        ‖inclusion I V u‖ ^ 2 := by
  have hb (i : I) := scalar_bound_on_physical_norm V (A i) 1 C_A (hA i) u (hu.vector i)
  have hi (i : I) : ‖ordinary I V i u‖ ^ 2 ≤
      3 * ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 +
      3 * normGradientEnergy V u +
      24 * e ^ 2 * (max M 0) ^ 2 * ‖radiation I V u‖ ^ 2 +
      (6 * e ^ 2 * (max M 0) ^ 2 + 3 * C_A) * ‖inclusion I V u‖ ^ 2 := by
    have ho := ordinary_sq_le_external V C κ hκ M hbound e A positive negative u hu i
    have hf := mul_le_mul_of_nonneg_left
      (uniform_field_bound V C κ hκ M hbound u i) (by positivity : 0 ≤ 3 * e ^ 2)
    linarith [hb i]
  calc
    _ ≤ ∑ i, (3 * ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 +
        3 * normGradientEnergy V u +
        24 * e ^ 2 * (max M 0) ^ 2 * ‖radiation I V u‖ ^ 2 +
        (6 * e ^ 2 * (max M 0) ^ 2 + 3 * C_A) * ‖inclusion I V u‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
                ring

def derivativeRecoveryFactor (d : ℕ) (e M : ℝ) : ℝ :=
  4 + 3 * d + 24 * e ^ 2 * (max M 0) ^ 2 * d

def derivativeMassFactor (d : ℕ) (e M C_A : ℝ) : ℝ :=
  6 * e ^ 2 * (max M 0) ^ 2 * d + 3 * |C_A| * d

theorem derivativeRecoveryFactor_nonneg (d : ℕ) (e M : ℝ) :
    0 ≤ derivativeRecoveryFactor d e M := by unfold derivativeRecoveryFactor; positivity

theorem derivativeMassFactor_nonneg (d : ℕ) (e M C_A : ℝ) :
    0 ≤ derivativeMassFactor d e M C_A := by unfold derivativeMassFactor; positivity

theorem full_energy_bound (C_A : ℝ) (hA : ∀ i, ScalarMultiplierBound (A i) 1 C_A)
    (u : Reference I V) (hu : ExternalDomain V A positive negative u) :
    (∑ i, ‖ordinary I V i u‖ ^ 2) +
      (∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2) +
      ‖radiation I V u‖ ^ 2 ≤
    derivativeRecoveryFactor (Fintype.card I) e M *
      ((∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2) +
        ‖radiation I V u‖ ^ 2 + normGradientEnergy V u) +
      derivativeMassFactor (Fintype.card I) e M C_A * ‖inclusion I V u‖ ^ 2 := by
  have ho := ordinary_energy_bound V C κ hκ M hbound e A positive negative C_A hA u hu
  have hk : 0 ≤ ∑ i, ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h₁ := mul_nonneg
    (by positivity : 0 ≤ 3 * ((Fintype.card I) : ℝ) + 24 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I)) hk
  have h₂ := mul_nonneg (by positivity : 0 ≤ 3 + 3 * ((Fintype.card I) : ℝ))
    (sq_nonneg ‖radiation I V u‖)
  have h₃ := mul_nonneg (by positivity : 0 ≤ 4 + 24 * e ^ 2 * (max M 0) ^ 2 * (Fintype.card I))
    (normGradientEnergy_nonneg V u)
  have h₄ := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (sub_nonneg.mpr (le_abs_self C_A))) (Nat.cast_nonneg (Fintype.card I)))
    (sq_nonneg ‖inclusion I V u‖)
  unfold derivativeRecoveryFactor derivativeMassFactor
  linarith only [ho, h₁, h₂, h₃, h₄]

end PfHk.PhysicalLocalEnergy
