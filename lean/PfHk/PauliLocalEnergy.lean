import PfHk.PauliRawForm
import PfHk.PauliSpinMaps
import PfHk.PauliContractionBounds
import PfHk.PhysicalLocalEnergyRoughIMS

/-! Localization of the concrete Pauli form. The spin matrices commute
with scalar electronic cutoffs, and the cutoff error is derived from the
actual weak product rules for the covariant derivatives. -/

noncomputable section
namespace PfHk.PauliLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier GptLean.SymmetricLift
  PfHk.PauliSpin PfHk.PauliCurrentAlgebra PfHk.PauliGroundState
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000

variable {N : ℕ}

attribute [local irreducible] referenceSubspace

theorem contraction_map {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (n : Fin N) (L : H →L[ℂ] K) (d : Fin 3 → SpinIndex N → H) :
    contraction n (fun a s => L (d a s)) = fun s => L (contraction n d s) := by
  funext s
  simp only [contraction, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact congrFun (sigmaFamily_map n a L.toLinearMap (d a)) s

/-- The finite-family cutoff identity uses only the Hilbert-space product rule. -/
theorem finite_singleCutoff {S H : Type*} [Fintype S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : H →L[ℂ] H) (hL : ∀ w z, inner ℂ w (L z) = inner ℂ (L w) z)
    (d d₁ d₂ b b₁ : S → H)
    (h₁ : d₁ = (fun s => L (d s)) + b)
    (h₂ : d₂ = (fun s => L (d₁ s)) + b₁)
    (hb : b₁ = fun s => L (b s)) :
    (∑ s, ‖d₁ s‖ ^ 2) =
      (∑ s, (inner ℂ (d₂ s) (d s)).re) + ∑ s, ‖b s‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply singleCutoff_of_product L hL (d s) (d₁ s) (d₂ s) (b s)
  · exact congrFun h₁ s
  · exact (congrFun h₂ s).trans
      ((congrArg (fun z : H => L (d₁ s) + z) (congrFun hb s)).trans
        (L.map_add (d₁ s) (b s)).symm)

/-- Two applications of a symmetric multiplier move across the inner product. -/
theorem inner_of_symmetric_product {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : H →L[ℂ] H) (hL : ∀ w z, inner ℂ w (L z) = inner ℂ (L w) z)
    (w w₁ w₂ : H) (h₁ : w₁ = L w) (h₂ : w₂ = L w₁) :
    inner ℂ w₂ w = inner ℂ w₁ w₁ :=
  (congrArg (fun z : H => inner ℂ z w) h₂).trans
    ((hL w₁ w).symm.trans
      (congrArg (fun z : H => inner ℂ w₁ z) h₁.symm))

/-- Taking the real part of the finite scalar expression defining the form. -/
theorem finite_form_re {S T : Type*} [Fintype S] [Fintype T]
    (k : T → S → ℂ) (r p m : S → ℂ) :
    ((1 / 2 : ℂ) * (∑ t, ∑ s, k t s) + (∑ s, r s) +
      (∑ s, p s) - ∑ s, m s).re =
      (1 / 2 : ℝ) * (∑ t, ∑ s, (k t s).re) + (∑ s, (r s).re) +
        (∑ s, (p s).re) - ∑ s, (m s).re := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
    Complex.re_sum, Complex.im_sum, zero_div, zero_mul, sub_zero]

/-- Scalar assembly of the localized kinetic, radiation and potential terms. -/
theorem form_localization_algebra {E F K₁ K₂ B R₁ R₂ P₁ P₂ M₁ M₂ : ℝ}
    (hE : E = (1 / 2 : ℝ) * K₁ + R₁ + P₁ - M₁)
    (hK : K₁ = K₂ + B) (hR : R₁ = R₂) (hP : P₁ = P₂) (hM : M₁ = M₂)
    (hF : F = (1 / 2 : ℝ) * K₂ + R₂ + P₂ - M₂) :
    E = F + (1 / 2 : ℝ) * B := by
  linarith only [hE, hK, hR, hP, hM, hF]


def localize (a : DifferentiableMultiplier (Fin N × Fin 3)) (u : Ref N) : Ref N :=
  fun s => PhysicalPFScalarMultiplier.multiply (fun _ => 0) a (u s)

theorem domain_localize {A : (Fin N × Fin 3) → Configuration N → ℝ}
    {positive negative : Configuration N → ℝ} {u : Ref N}
    (hu : Domain A positive negative u) (a : DifferentiableMultiplier (Fin N × Fin 3)) :
    Domain A positive negative (localize (N := N) a u) :=
  fun s => (hu s).localize (fun _ => 0) a

/-- The actual first-order Pauli localization error. -/
def error (a : DifferentiableMultiplier (Fin N × Fin 3)) (u : Ref N) (n : Fin N) :
    SpinIndex N → WaveSpace (Fin N × Fin 3) :=
  contraction n (fun μ s => (-Complex.I) •
    a.derivativeMultiplier (H := PhotonFock) (n, μ) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))

theorem error_norm_sq_le (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (n : Fin N) :
    (∑ s, ‖error (N := N) a u n s‖ ^ 2) ≤
      3 * ∑ μ : Fin 3, ∑ s, ‖a.derivativeMultiplier (H := PhotonFock) (n, μ)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))‖ ^ 2 := by
  have h := PauliContractionBounds.contraction_norm_sq_le n
    (fun μ s => (-Complex.I) • a.derivativeMultiplier (H := PhotonFock) (n, μ)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
  simpa only [error, norm_negI_smul] using h

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Configuration N → ℝ)
  (positive negative : Configuration N → ℝ)

attribute [local irreducible] rawCovariant rawContraction inclusion
  externalCovariant PhysicalPFScalarMultiplier.multiply
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  rawForm rawEnergy mass normSquared


theorem contraction_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u) (n : Fin N) :
    rawContraction C κ hκ M hκbound e A positive negative (localize (N := N) a u)
      (domain_localize hu a) n =
      (fun s => a.multiplier (H := PhotonFock) (rawContraction C κ hκ M hκbound e A positive negative u hu n s)) +
        error (N := N) a u n := by
  have hp : (fun μ => rawCovariant C κ hκ M hκbound e A positive negative
      (localize (N := N) a u) (domain_localize hu a) (n, μ)) =
      (fun μ s => a.multiplier (H := PhotonFock) (rawCovariant C κ hκ M hκbound e A positive negative u hu (n, μ) s)) +
      (fun μ s => (-Complex.I) • a.derivativeMultiplier (H := PhotonFock) (n, μ)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) := by
    funext μ s
    simp only [rawCovariant, localize, Pi.add_apply]
    exact externalCovariant_localize (fun _ => 0) C κ hκ M hκbound e
      A positive negative (u s) (hu s) a (n, μ)
  unfold rawContraction
  exact (congrArg (contraction (H := WaveSpace (Fin N × Fin 3)) n) hp).trans
    ((contraction_add n _ _).trans
      (congrArg (· + error (N := N) a u n)
        (contraction_map n (a.multiplier (H := PhotonFock)) _)))


theorem error_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (n : Fin N) :
    error (N := N) a (localize (N := N) a u) n = fun s => a.multiplier (H := PhotonFock) (error (N := N) a u n s) := by
  have hp : (fun μ s => (-Complex.I) • a.derivativeMultiplier (H := PhotonFock) (n, μ)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (localize (N := N) a u s))) =
      fun μ s => a.multiplier (H := PhotonFock) ((-Complex.I) • a.derivativeMultiplier (H := PhotonFock) (n, μ)
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) := by
    funext μ s
    have hv := PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (u s)
    have hd := multiplier_derivative_commute a (n, μ)
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    exact (congrArg (fun z : WaveSpace (Fin N × Fin 3) =>
      (-Complex.I) • a.derivativeMultiplier (H := PhotonFock) (n, μ) z) hv).trans
      ((congrArg (fun z : WaveSpace (Fin N × Fin 3) => (-Complex.I) • z) hd).trans
        ((a.multiplier (H := PhotonFock)).map_smul (-Complex.I)
          (a.derivativeMultiplier (H := PhotonFock) (n, μ)
            (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))).symm)
  unfold error
  exact (congrArg (contraction (H := WaveSpace (Fin N × Fin 3)) n) hp).trans
    (contraction_map n (a.multiplier (H := PhotonFock)) _)

attribute [local irreducible] error


theorem kinetic_localize (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u) (n : Fin N) :
    (∑ s, ‖rawContraction C κ hκ M hκbound e A positive negative (localize (N := N) a u)
      (domain_localize hu a) n s‖ ^ 2) =
      (∑ s, (inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hκbound e A positive negative (localize (N := N) a (localize (N := N) a u))
          (domain_localize (domain_localize hu a) a) n s)
        (rawContraction C κ hκ M hκbound e A positive negative u hu n s)).re) +
      ∑ s, ‖error (N := N) a u n s‖ ^ 2 := by
  exact finite_singleCutoff (S := SpinIndex N) (H := WaveSpace (Fin N × Fin 3))
    (a.multiplier (H := PhotonFock)) (a.multiplier_symmetric (H := PhotonFock))
    (rawContraction C κ hκ M hκbound e A positive negative u hu n)
    (rawContraction C κ hκ M hκbound e A positive negative
      (localize (N := N) a u) (domain_localize hu a) n)
    (rawContraction C κ hκ M hκbound e A positive negative
      (localize (N := N) a (localize (N := N) a u))
      (domain_localize (domain_localize hu a) a) n)
    (error (N := N) a u n) (error (N := N) a (localize (N := N) a u) n)
    (contraction_localize C κ hκ M hκbound e A positive negative a u hu n)
    (contraction_localize C κ hκ M hκbound e A positive negative a
      (localize (N := N) a u) (domain_localize hu a) n)
    (error_localize (N := N) a u n)


theorem raw_ims (a : DifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u) :
    rawEnergy C κ hκ M hκbound e A positive negative (localize (N := N) a u) (domain_localize hu a) =
      (rawForm C κ hκ M hκbound e A positive negative (localize (N := N) a (localize (N := N) a u)) u
        (domain_localize (domain_localize hu a) a) hu).re +
      (1 / 2 : ℝ) * ∑ n, ∑ s, ‖error (N := N) a u n s‖ ^ 2 := by
  have he := rawEnergy_eq C κ hκ M hκbound e A positive negative
    (localize (N := N) a u) (domain_localize hu a)
  have hk := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun n _ => kinetic_localize C κ hκ M hκbound e A positive negative a u hu n)
  rw [Finset.sum_add_distrib] at hk
  have hr := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun s _ => radiation_singleCutoff (fun _ => 0) a (u s))
  have hp := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun s _ => roughMultiply_singleCutoff (fun _ => 0) a positive (u s)
      (hu s).positive ((domain_localize hu a) s).positive
      ((domain_localize (domain_localize hu a) a) s).positive)
  have hn := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun s _ => roughMultiply_singleCutoff (fun _ => 0) a negative (u s)
      (hu s).negative ((domain_localize hu a) s).negative
      ((domain_localize (domain_localize hu a) a) s).negative)
  have hf : (rawForm C κ hκ M hκbound e A positive negative
      (localize (N := N) a (localize (N := N) a u)) u (domain_localize (domain_localize hu a) a) hu).re =
      (1 / 2 : ℝ) * (∑ n, ∑ s, (inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hκbound e A positive negative
          (localize (N := N) a (localize (N := N) a u)) (domain_localize (domain_localize hu a) a) n s)
        (rawContraction C κ hκ M hκbound e A positive negative u hu n s)).re) +
      (∑ s, (inner ℂ (E := WaveSpace (Fin N × Fin 3)) (radiation (Fin N × Fin 3) (fun _ => 0)
        (localize (N := N) a (localize (N := N) a u) s)) (radiation (Fin N × Fin 3) (fun _ => 0) (u s))).re) +
      (∑ s, (inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0)
          (localize (N := N) a (localize (N := N) a u) s)) ((domain_localize (domain_localize hu a) a) s).positive)
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive)).re) -
      (∑ s, (inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0)
          (localize (N := N) a (localize (N := N) a u) s)) ((domain_localize (domain_localize hu a) a) s).negative)
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative)).re) := by
    unfold rawForm
    exact finite_form_re (S := SpinIndex N) (T := Fin N)
      (fun n s => inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (rawContraction C κ hκ M hκbound e A positive negative
          (localize (N := N) a (localize (N := N) a u))
          (domain_localize (domain_localize hu a) a) n s)
        (rawContraction C κ hκ M hκbound e A positive negative u hu n s))
      (fun s => inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (radiation (Fin N × Fin 3) (fun _ => 0)
          (localize (N := N) a (localize (N := N) a u) s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)))
      (fun s => inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0)
          (localize (N := N) a (localize (N := N) a u) s))
          ((domain_localize (domain_localize hu a) a) s).positive)
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
          (hu s).positive))
      (fun s => inner ℂ (E := WaveSpace (Fin N × Fin 3))
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0)
          (localize (N := N) a (localize (N := N) a u) s))
          ((domain_localize (domain_localize hu a) a) s).negative)
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
          (hu s).negative))
  exact form_localization_algebra he hk hr hp hn hf


theorem mass_localize (a : DifferentiableMultiplier (Fin N × Fin 3)) (u : Ref N) :
    mass (N := N) (localize (N := N) a (localize (N := N) a u)) u = mass (N := N) (localize (N := N) a u) (localize (N := N) a u) := by
  unfold mass
  apply Finset.sum_congr rfl
  intro s _
  exact inner_of_symmetric_product (H := WaveSpace (Fin N × Fin 3))
    (a.multiplier (H := PhotonFock)) (a.multiplier_symmetric (H := PhotonFock))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (inclusion (Fin N × Fin 3) (fun _ => 0) (localize (N := N) a u s))
    (inclusion (Fin N × Fin 3) (fun _ => 0)
      (localize (N := N) a (localize (N := N) a u) s))
    (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (u s))
    (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a (localize (N := N) a u s))


theorem eigenstate_ims (a : DifferentiableMultiplier (Fin N × Fin 3))
    {E : ℝ} (u : Ref N) (hu : Domain A positive negative u)
    (heigen : IsWeakEigenstate C κ hκ M hκbound e A positive negative E u hu) :
    rawEnergy C κ hκ M hκbound e A positive negative (localize (N := N) a u) (domain_localize hu a) =
      E * normSquared (N := N) (localize (N := N) a u) + (1 / 2 : ℝ) * ∑ n, ∑ s, ‖error (N := N) a u n s‖ ^ 2 := by
  have hform := heigen (localize (N := N) a (localize (N := N) a u))
    (domain_localize (domain_localize hu a) a)
  have hre₀ := congrArg Complex.re hform
  have hm := mass_localize (N := N) a u
  have hre₁ : ((E : ℂ) * mass (N := N)
      (localize (N := N) a (localize (N := N) a u)) u).re =
      E * normSquared (N := N) (localize (N := N) a u) := by
    apply (congrArg (fun z : ℂ => ((E : ℂ) * z).re) hm).trans
    simp only [mass, normSquared, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.re_sum,
      PhysicalLocalEnergy.re_inner_self (H := WaveSpace (Fin N × Fin 3))]
  exact (raw_ims C κ hκ M hκbound e A positive negative a u hu).trans
    (congrArg (fun q : ℝ => q + (1 / 2 : ℝ) *
      ∑ n, ∑ s, ‖error (N := N) a u n s‖ ^ 2) (hre₀.trans hre₁))

end PfHk.PauliLocalEnergy

