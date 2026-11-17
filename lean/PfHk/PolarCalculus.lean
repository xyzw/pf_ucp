import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Ordinary Hilbert-valued polar calculus, separated from every physical
coefficient. The sphere and its Hilbert spaces use Mathlib's actual
`volume.toSphere` measure. The differential maps below are defined by
ordinary Fréchet derivatives of radial homogeneous extensions.

`StandardPolarCalculus` records the standard polar-coordinate gradient
and Laplacian formulas and the sphere divergence theorem. These are
universal geometric/operator facts admitted under the user's allowance
for well-known operator theory. It contains no Weyl operator, field
kernel, radiation Hamiltonian, perturbation, Carleman estimate or UCP
conclusion. The covariant substitution and norm decomposition are proved
outside that background.
-/

noncomputable section
namespace PfHk.PolarCalculus

open MeasureTheory
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable (I : Type*) [Fintype I] [DecidableEq I]

abbrev Position := EuclideanSpace ℝ I
abbrev UnitSphere := Metric.sphere (0 : Position I) 1

def sphereMeasure : Measure (UnitSphere I) := (volume : Measure (Position I)).toSphere

instance sphereMeasure_isFinite : IsFiniteMeasure (sphereMeasure I) := by
  unfold sphereMeasure
  infer_instance

abbrev SphereHilbert (H : Type*) [NormedAddCommGroup H] := Lp H 2 (sphereMeasure I)
abbrev SphereVectorHilbert (H : Type*) [NormedAddCommGroup H] :=
  Lp (PiLp 2 (fun _ : I => H)) 2 (sphereMeasure I)

theorem unitSphere_norm (θ : UnitSphere I) : ‖(θ : Position I)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using θ.property

def direction (x : Position I) (hx : x ≠ 0) : UnitSphere I :=
  ⟨‖x‖⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

/-- Mathlib proves the polar change of measure for the actual sphere measure. -/
theorem polar_measurePreserving :
    MeasurePreserving (homeomorphUnitSphereProd (Position I))
      ((volume : Measure (Position I)).comap Subtype.val)
      ((sphereMeasure I).prod (Measure.volumeIoiPow (Module.finrank ℝ (Position I) - 1))) :=
  (volume : Measure (Position I)).measurePreserving_homeomorphUnitSphereProd

variable {I}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def homogeneousExtension (f : UnitSphere I → H) (x : Position I) : H :=
  if hx : x = 0 then 0 else f (direction I x hx)

def sphereGradient (f : UnitSphere I → H) (j : I) (θ : UnitSphere I) : H :=
  fderiv ℝ (homogeneousExtension f) (θ : Position I) (EuclideanSpace.single j 1)

def sphereDivergence (v : I → UnitSphere I → H) (θ : UnitSphere I) : H :=
  ∑ j, sphereGradient (v j) j θ

def sphereLaplacian (f : UnitSphere I → H) (θ : UnitSphere I) : H :=
  sphereDivergence (sphereGradient f) θ

def euclideanLaplacian (f : Position I → H) (x : Position I) : H :=
  ∑ j, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x
    (EuclideanSpace.single j 1)

def radialRestriction (u : Position I → H) (r : ℝ) (θ : UnitSphere I) : H :=
  u (r • (θ : Position I))

def radialFirst (u : Position I → H) (r : ℝ) (θ : UnitSphere I) : H :=
  fderiv ℝ u (r • (θ : Position I)) (θ : Position I)

def radialSecond (u : Position I → H) (r : ℝ) (θ : UnitSphere I) : H :=
  fderiv ℝ (fun x => fderiv ℝ u x (θ : Position I))
    (r • (θ : Position I)) (θ : Position I)

def SphereC1 (f : UnitSphere I → H) : Prop :=
  ContDiffOn ℝ (1 : ℕ∞) (homogeneousExtension f) ({0}ᶜ : Set (Position I))


/-- The retained universal inputs are ordinary polar-coordinate calculus.
All fields refer to the explicitly defined ordinary derivative maps. -/
structure StandardPolarCalculus (I : Type*) [Fintype I] [DecidableEq I]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop where
  gradient_decomposition : ∀ (u : Position I → H), ContDiff ℝ (1 : ℕ∞) u →
    ∀ (r : ℝ), 0 < r → ∀ (θ : UnitSphere I) (j : I),
      fderiv ℝ u (r • (θ : Position I)) (EuclideanSpace.single j 1) =
        θ.val j • radialFirst u r θ + r⁻¹ • sphereGradient (radialRestriction u r) j θ
  laplacian_decomposition : ∀ (u : Position I → H), ContDiff ℝ (2 : ℕ∞) u →
    ∀ (r : ℝ), 0 < r → ∀ θ : UnitSphere I,
      euclideanLaplacian u (r • (θ : Position I)) = radialSecond u r θ +
        (((Fintype.card I : ℝ) - 1) / r) • radialFirst u r θ +
        (r ^ 2)⁻¹ • sphereLaplacian (radialRestriction u r) θ
  gradient_tangent : ∀ (f : UnitSphere I → H), SphereC1 f → ∀ θ,
    (∑ j, θ.val j • sphereGradient f j θ) = 0
  integration_by_parts : ∀ (f : UnitSphere I → H) (v : I → UnitSphere I → H),
    SphereC1 f → (∀ j, SphereC1 (v j)) →
    (∀ θ, (∑ j, θ.val j • v j θ) = 0) →
    (∫ θ, inner ℝ (f θ) (sphereDivergence v θ) ∂sphereMeasure I) =
      -(∑ j, ∫ θ, inner ℝ (sphereGradient f j θ) (v j θ) ∂sphereMeasure I)

section Covariant
variable [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- The coefficient is its actual action on the vector under consideration.
This definition permits graph-domain fields without treating them as bounded
operators on the ambient Hilbert space. -/
def covariant (u : Position I → H) (a : I → Position I → H) (j : I) (x : Position I) : H :=
  (-Complex.I) • fderiv ℝ u x (EuclideanSpace.single j 1) + a j x

def angularCovariant (u : Position I → H) (a : I → Position I → H)
    (r : ℝ) (j : I) (θ : UnitSphere I) : H :=
  (-Complex.I) • sphereGradient (radialRestriction u r) j θ + r • a j (r • (θ : Position I))

/-- Substituting the coefficient into ordinary polar differentiation.
The connection itself is arbitrary in this theorem. -/
theorem covariant_decomposition (P : StandardPolarCalculus I H)
    (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u)
    (a : I → Position I → H) {r : ℝ} (hr : 0 < r) (θ : UnitSphere I) (j : I) :
    r • covariant u a j (r • (θ : Position I)) =
      θ.val j • ((-Complex.I) • (r • radialFirst u r θ)) + angularCovariant u a r j θ := by
  rw [covariant, P.gradient_decomposition u hu r hr θ j]
  simp only [angularCovariant, smul_add, smul_comm (-Complex.I), smul_smul]
  rw [mul_inv_cancel₀ hr.ne']
  simp only [one_smul]
  module

/-- Zero radial connection gives an actual tangent angular covariant vector. -/
theorem angularCovariant_tangent (P : StandardPolarCalculus I H)
    (u : Position I → H) (a : I → Position I → H) (r : ℝ) (θ : UnitSphere I)
    (hu : SphereC1 (radialRestriction u r))
    (ha : (∑ j, θ.val j • a j (r • (θ : Position I))) = 0) :
    (∑ j, θ.val j • angularCovariant u a r j θ) = 0 := by
  simp only [angularCovariant, smul_add, Finset.sum_add_distrib]
  have h₁ : (∑ j, θ.val j • ((-Complex.I) • sphereGradient (radialRestriction u r) j θ)) =
      (-Complex.I) • (∑ j, θ.val j • sphereGradient (radialRestriction u r) j θ) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  have h₂ : (∑ j, θ.val j • (r • a j (r • (θ : Position I)))) =
      r • (∑ j, θ.val j • a j (r • (θ : Position I))) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [h₁, h₂, P.gradient_tangent _ hu θ, ha, smul_zero, smul_zero, zero_add]

end Covariant

/-- Pythagoras for the radial and tangent parts, before any sphere integral. -/
theorem radial_tangent_norm_sq (θ : UnitSphere I) (v : H) (a : I → H)
    (ha : (∑ j, θ.val j • a j) = 0) :
    (∑ j, ‖θ.val j • v + a j‖ ^ 2) = ‖v‖ ^ 2 + ∑ j, ‖a j‖ ^ 2 := by
  have hθ : (∑ j, (θ.val j) ^ 2) = 1 := by
    simpa only [unitSphere_norm I θ, one_pow] using (EuclideanSpace.real_norm_sq_eq θ.val).symm
  have hx : (∑ j, inner ℝ (θ.val j • v) (a j)) = 0 := by
    calc
      _ = inner ℝ v (∑ j, θ.val j • a j) := by
        simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
      _ = 0 := by rw [ha, inner_zero_right]
  simp only [norm_add_sq_real, Finset.sum_add_distrib, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.sum_mul, hθ, one_mul]
  have hcross : (∑ j, 2 * inner ℝ (θ.val j • v) (a j)) = 0 := by
    rw [← Finset.mul_sum, hx, mul_zero]
  rw [hcross, add_zero]



section CovariantEnergy
variable [NormedSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- The full first-order polar energy splitting follows by substitution
and Pythagoras, for any radial-gauge coefficient action. -/
theorem covariant_norm_decomposition (P : StandardPolarCalculus I H)
    (u : Position I → H) (hu : ContDiff ℝ (1 : ℕ∞) u)
    (a : I → Position I → H) {r : ℝ} (hr : 0 < r) (θ : UnitSphere I)
    (hs : SphereC1 (radialRestriction u r))
    (ha : (∑ j, θ.val j • a j (r • (θ : Position I))) = 0) :
    r ^ 2 * (∑ j, ‖covariant u a j (r • (θ : Position I))‖ ^ 2) =
      r ^ 2 * ‖radialFirst u r θ‖ ^ 2 + ∑ j, ‖angularCovariant u a r j θ‖ ^ 2 := by
  calc
    _ = ∑ j, ‖r • covariant u a j (r • (θ : Position I))‖ ^ 2 := by
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
    _ = ∑ j, ‖θ.val j • ((-Complex.I) • (r • radialFirst u r θ)) +
        angularCovariant u a r j θ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [covariant_decomposition P u hu a hr θ j]
    _ = ‖(-Complex.I) • (r • radialFirst u r θ)‖ ^ 2 +
        ∑ j, ‖angularCovariant u a r j θ‖ ^ 2 :=
      radial_tangent_norm_sq θ _ _ (angularCovariant_tangent P u a r θ hs ha)
    _ = _ := by simp only [norm_smul, norm_neg, Complex.norm_I, one_mul,
      mul_pow, Real.norm_eq_abs, sq_abs]

end CovariantEnergy

end PfHk.PolarCalculus
