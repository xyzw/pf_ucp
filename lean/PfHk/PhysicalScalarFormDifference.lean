import PfHk.ScalarFormLp
import PfHk.PhysicalCommonFormDomain
import GptLean.PhysicalSourceTests

/-! Subtraction of the actual external forms when the vector potentials
agree almost everywhere. The remaining signed scalar form is its physical
configuration integral. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PhysicalScalarFormDifference

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace externalCovariant externalForm

variable {N : ℕ}

abbrev Ref (N : ℕ) := Reference (Fin N × Fin 3) (fun _ => 0)

/-- The physical sum of one-body scalar-potential differences. -/
def scalarDifference (v₁ v₂ : ScalarPotential)
    (X : PhysicalSourceCoordinates.Configuration N) : ℝ :=
  ∑ n : Fin N, CoordinateSobolev.coordinateCoefficient n
    (fun x => v₁.val x - v₂.val x) X

theorem scalarDifference_eq_sum_particle (v₁ v₂ : ScalarPotential)
    (X : PhysicalSourceCoordinates.Configuration N) :
    scalarDifference (N := N) v₁ v₂ X =
      ∑ n : Fin N, (v₁.val (SymmetricLift.particle X n) -
        v₂.val (SymmetricLift.particle X n)) := by
  simp only [scalarDifference, CoordinateSobolev.coordinateCoefficient,
    PhysicalSourcePair.split_fst_eq_particle]

theorem scalar_sub (v₁ v₂ : ScalarPotential) (c : ℝ)
    (X : PhysicalSourceCoordinates.Configuration N) :
    scalar v₁ c X - scalar v₂ c X = scalarDifference (N := N) v₁ v₂ X := by
  simp only [scalar, scalarDifference, CoordinateSobolev.coordinateCoefficient,
    Finset.sum_sub_distrib]
  ring

theorem vector_ae (A₁ A₂ : VectorPotential) (hA : A₁.val =ᵐ[volume] A₂.val)
    (j : Fin N × Fin 3) : vector (N := N) A₁ j =ᵐ[volume] vector A₂ j := by
  have h := ScalarCoordinateFormBound.coordinate_ae (N := N) j.1 hA
  exact h.mono fun X hX => congrArg (fun a : PhysicalPairSpace.Vector => a j.2) hX

theorem roughMultiply_congr {I : Type} [Fintype I] [DecidableEq I]
    (a b : PhysicalPFReference.Position I → ℝ) (hab : a =ᵐ[volume] b)
    (u : WaveSpace I) (ha : HasMultiplier a u) (hb : HasMultiplier b u) :
    roughMultiply a u ha = roughMultiply b u hb := by
  apply Lp.ext
  filter_upwards [roughMultiply_ae a u ha, roughMultiply_ae b u hb, hab] with X h₁ h₂ h₃
  exact h₁.trans ((congrArg (fun r : ℝ => r • u X) h₃).trans h₂.symm)

section Scalar

variable (v : ScalarPotential) (c : ℝ) (z u : Ref N)
  (hzp : HasMultiplier (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) z))
  (hup : HasMultiplier (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u))
  (hzn : HasMultiplier (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) z))
  (hun : HasMultiplier (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u))

include hzp hup hzn hun

theorem scalar_pair_integrable :
    Integrable (fun X => scalar (N := N) v c X *
      (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
        inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re) volume :=
  ScalarFormLp.signed_pair_integrable
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (roughMultiply (positive v c) _ hzp) (roughMultiply (positive v c) _ hup)
    (roughMultiply (negative v c) _ hzn) (roughMultiply (negative v c) _ hun)
    (positive v c) (negative v c) (scalar v c)
    (roughMultiply_ae _ _ hzp) (roughMultiply_ae _ _ hup)
    (roughMultiply_ae _ _ hzn) (roughMultiply_ae _ _ hun)
    (Filter.Eventually.of_forall (SignedScalarMultiplier.amplitude_difference (scalar v c)))

theorem scalar_pair_re :
    (⟪roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) z) hzp,
      roughMultiply (positive v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hup⟫_ℂ).re -
    (⟪roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) z) hzn,
      roughMultiply (negative v c) (inclusion (Fin N × Fin 3) (fun _ => 0) u) hun⟫_ℂ).re =
      ∫ X, scalar (N := N) v c X *
        (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
          inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re :=
  ScalarFormLp.signed_pair_re
    (inclusion (Fin N × Fin 3) (fun _ => 0) z)
    (inclusion (Fin N × Fin 3) (fun _ => 0) u)
    (roughMultiply (positive v c) _ hzp) (roughMultiply (positive v c) _ hup)
    (roughMultiply (negative v c) _ hzn) (roughMultiply (negative v c) _ hun)
    (positive v c) (negative v c) (scalar v c)
    (roughMultiply_ae _ _ hzp) (roughMultiply_ae _ _ hup)
    (roughMultiply_ae _ _ hzn) (roughMultiply_ae _ _ hun)
    (Filter.Eventually.of_forall (SignedScalarMultiplier.amplitude_difference (scalar v c)))

end Scalar

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ j, AEStronglyMeasurable (κ j) volume)
  (M : ℝ) (hb : ∀ j, ∀ᵐ X ∂volume, ‖κ j X‖ ≤ M) (e : ℝ)
  (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "D₁" => externalDomain (N := N) A₁ v₁ c hc
set_option hygiene false in
local notation "D₂" => externalDomain (N := N) A₂ v₂ c hc

theorem externalCovariant_congr (hA : A₁.val =ᵐ[volume] A₂.val)
    (u : Ref N) (j : Fin N × Fin 3) :
    externalCovariant (fun _ => 0) C κ hκ M hb e
      (vector A₁) (positive v₁ c) (negative v₁ c) u (D₁ u) j =
    externalCovariant (fun _ => 0) C κ hκ M hb e
      (vector A₂) (positive v₂ c) (negative v₂ c) u (D₂ u) j := by
  unfold externalCovariant
  exact congrArg (fun w : WaveSpace (Fin N × Fin 3) =>
    covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e j u + w)
    (roughMultiply_congr (vector A₁ j) (vector A₂ j) (vector_ae A₁ A₂ hA j)
      (inclusion (Fin N × Fin 3) (fun _ => 0) u) ((D₁ u).vector j) ((D₂ u).vector j))

private theorem form_accounting {J : Type*} [Fintype J]
    (k₁ k₂ : J → ℂ) (r t p₁ n₁ p₂ n₂ : ℂ) (hk : ∀ j, k₁ j = k₂ j) :
    ((1 / 2 : ℂ) * ∑ j, k₁ j + r + t + p₁ - n₁).re -
      ((1 / 2 : ℂ) * ∑ j, k₂ j + r + t + p₂ - n₂).re =
        (p₁.re - n₁.re) - (p₂.re - n₂.re) := by
  have hsum : (∑ j, k₁ j) = ∑ j, k₂ j := Finset.sum_congr rfl (fun j _ => hk j)
  rw [hsum]
  simp only [Complex.add_re, Complex.sub_re]
  ring

include A₁ A₂ c hc in
theorem difference_integrable (z u : Ref N) :
    Integrable (fun X => scalarDifference (N := N) v₁ v₂ X *
      (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
        inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re) volume := by
  have h₁ := scalar_pair_integrable v₁ c z u
    ((D₁ z).positive) ((D₁ u).positive) ((D₁ z).negative) ((D₁ u).negative)
  have h₂ := scalar_pair_integrable v₂ c z u
    ((D₂ z).positive) ((D₂ u).positive) ((D₂ z).negative) ((D₂ u).negative)
  apply (h₁.sub h₂).congr
  exact Filter.Eventually.of_forall fun X =>
    (sub_mul _ _ _).symm.trans (congrArg
      (fun r : ℝ => r * (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
        inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re) (scalar_sub v₁ v₂ c X))

theorem difference (hA : A₁.val =ᵐ[volume] A₂.val) (z u : Ref N) :
    (externalForm (fun _ => 0) C κ hκ M hb e
      (vector A₁) (positive v₁ c) (negative v₁ c) z u (D₁ z) (D₁ u)).re -
    (externalForm (fun _ => 0) C κ hκ M hb e
      (vector A₂) (positive v₂ c) (negative v₂ c) z u (D₂ z) (D₂ u)).re =
      ∫ X, scalarDifference (N := N) v₁ v₂ X *
        (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
          inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re := by
  have hk (j : Fin N × Fin 3) := congrArg₂
    (fun a b : WaveSpace (Fin N × Fin 3) => ⟪a, b⟫_ℂ)
    (externalCovariant_congr C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA z j)
    (externalCovariant_congr C κ hκ M hb e A₁ A₂ v₁ v₂ c hc hA u j)
  have hp₁ := scalar_pair_re v₁ c z u
    ((D₁ z).positive) ((D₁ u).positive) ((D₁ z).negative) ((D₁ u).negative)
  have hp₂ := scalar_pair_re v₂ c z u
    ((D₂ z).positive) ((D₂ u).positive) ((D₂ z).negative) ((D₂ u).negative)
  have hi₁ := scalar_pair_integrable v₁ c z u
    ((D₁ z).positive) ((D₁ u).positive) ((D₁ z).negative) ((D₁ u).negative)
  have hi₂ := scalar_pair_integrable v₂ c z u
    ((D₂ z).positive) ((D₂ u).positive) ((D₂ z).negative) ((D₂ u).negative)
  unfold externalForm
  refine (form_accounting _ _ _ _ _ _ _ _ hk).trans
    ((congrArg₂ (· - ·) hp₁ hp₂).trans ((integral_sub hi₁ hi₂).symm.trans ?_))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun X =>
    (sub_mul _ _ _).symm.trans (congrArg
      (fun r : ℝ => r * (⟪inclusion (Fin N × Fin 3) (fun _ => 0) z X,
        inclusion (Fin N × Fin 3) (fun _ => 0) u X⟫_ℂ).re) (scalar_sub v₁ v₂ c X))

/-- The scalar difference times the actual configuration density is L1. -/
theorem density_integrable (u : Ref N) :
    Integrable (fun X => scalarDifference (N := N) v₁ v₂ X *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2) volume := by
  have h := difference_integrable (A₁ := (0 : VectorPotential))
    (A₂ := (0 : VectorPotential)) v₁ v₂ 0 le_rfl u u
  simpa only [re_inner_self] using h

end PfHk.PhysicalScalarFormDifference
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
