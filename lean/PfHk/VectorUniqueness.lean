import PfHk.FourierSource
import PfHk.FourierDivergence
import PfHk.FourierUniqueness

/-!
The cutoff-kernel proposition and the first alternative of vector-potential
uniqueness in `pf_ucp.tex`, on the physical Pauli--Fierz model.
The proof combines the actual common-ground-state and Weyl identities,
Fourier transversality, the complete polarization frame, and L¹ Fourier
injectivity. No positivity of the density is used until the last theorem.
-/

noncomputable section

namespace PfHk

open MeasureTheory Filter GptLean GptLean.PhysicalPairSpace
  GptLean.PhysicalPairDuality GptLean.PhysicalGroundState
  GptLean.PhysicalFock GptLean.PhysicalPolarization GptLean.Gaussian
  GptLean.TransformationsGauge GptLean.Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Fubini converts the two-polarization photon-space identity into a
simultaneous identity for both polarizations at almost every momentum. -/
theorem fourierSource_polarizations_ae (F : Frame) (χ : ArticleCutoff)
    (b : Position → Vector) (hsource : fourierSource F χ b =ᵐ[photonMeasure] 0) :
    ∀ᵐ k ∂volume, ∀ l : Fin 2, fourierSource F χ b (k, l) = 0 := by
  change ∀ᵐ p ∂volume.prod (Measure.count : Measure (Fin 2)),
    fourierSource F χ b p = 0 at hsource
  exact (Measure.ae_ae_of_ae_prod hsource).mono fun k hk => Measure.ae_count_iff.mp hk

/-- Removing the transverse projector from the photon-source identity.
The longitudinal identity is exactly Fourier-space divergence freedom. -/
theorem cutoff_mul_fourier_zero_of_source (F : Frame) (χ : ArticleCutoff)
    {b : Position → Vector} (hb : Integrable b volume)
    (hsource : currentSource F χ b = 0)
    (hlong : ∀ k : Position, (∑ a : Fin 3,
      (k a : ℂ) * PhysicalGroundState.fourierCoeff (fun x => b x a) k) = 0) :
    ∀ᵐ k ∂volume, ∀ a : Fin 3,
      χ.value (-k) * PhysicalGroundState.fourierCoeff (fun x => b x a) k = 0 := by
  have hfourier := fourierSource_ae_zero_of_currentSource_zero F χ hb hsource
  have hpol := fourierSource_polarizations_ae F χ b hfourier
  have hroot : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  filter_upwards [hpol, (volume : Measure Position).ae_ne 0] with k hk hkn
  apply frame_complex_zero_of_components F k
    (fun a => χ.value (-k) * PhysicalGroundState.fourierCoeff (fun x => b x a) k) hkn
  · intro l
    calc
      _ = (Real.sqrt 2 : ℂ) * fourierSource F χ b (k, l) := by
        simp only [fourierSource, sourceComponent, base, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        field_simp
      _ = 0 := by rw [hk l, mul_zero]
  · calc
      _ = χ.value (-k) * (∑ a : Fin 3,
          (k a : ℂ) * PhysicalGroundState.fourierCoeff (fun x => b x a) k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by rw [hlong k, mul_zero]

variable {N : ℕ} (i : Fin N) (F : Frame) (χ : ArticleCutoff)
  (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)
  (W : ConcreteWeylLaw photonMeasure)

include W in
/-- `prop-cutoff-kernel`. Both conclusions hold on the actual physical
model. The divergence assertion is stated for all bounded-gradient gauges,
which includes smooth compactly supported scalar tests. -/
theorem cutoff_kernel
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0) :
    (∀ g : SpatialGauge, ∫ x, inner ℝ (g.gradientVector x)
      (vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x) = 0) ∧
    (∀ᵐ k ∂volume, ∀ a : Fin 3,
      χ.value (-k) * PhysicalGroundState.fourierCoeff
        (fun x => vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) x a) k = 0) := by
  refine ⟨vectorDifference_divergence i F χ C B S e h₁ h₂ hd, ?_⟩
  exact cutoff_mul_fourier_zero_of_source F χ (vectorDifference_integrable a₁ a₂ _)
    (currentSource_zero i F χ C B S e W h₁ h₂ hd he)
    (vectorDifference_fourier_transverse i F χ C B S e h₁ h₂ hd)

/-- The cutoff reality condition transfers almost-everywhere nonvanishing
to reflected momenta, as required by the physical field kernel convention. -/
theorem cutoff_nonzero_neg_ae (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0) :
    ∀ᵐ k ∂volume, χ.value (-k) ≠ 0 := by
  filter_upwards [hχ, χ.reality] with k hk hr
  intro hz
  apply hk
  rw [hr, hz, map_zero]

include W in
/-- `thm-vector-uniqueness`, alternative (i). The common density times the
vector-potential difference vanishes almost everywhere. The cutoff is only
required to be nonzero almost everywhere, and the density may have zeros. -/
theorem vector_uniqueness_nonvanishing_cutoff
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0)
    (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0) :
    vectorDifference a₁ a₂ ((model i F χ C B S e).density p₁) =ᵐ[volume] 0 := by
  have hkernel := (cutoff_kernel i F χ C B S e W h₁ h₂ hd he).2
  apply FourierUniqueness.vector_ae_eq_zero_of_fourierCoeff_ae_zero
  · intro a
    exact (EuclideanSpace.proj a : Vector →L[ℝ] ℝ).integrable_comp
      (vectorDifference_integrable a₁ a₂ _)
  · filter_upwards [hkernel, cutoff_nonzero_neg_ae χ hχ] with k hk hkn
    intro a
    exact (mul_eq_zero.mp (hk a)).resolve_left hkn

include W in
/-- Literal equality of external vector potentials follows when the common
density is positive almost everywhere. Density positivity is explicit in
this helper and is derived from UCP in `PhysicalHohenbergKohn`. -/
theorem vector_potential_eq_of_density_positive
    {a₁ a₂ : Potential} {p₁ p₂ : State F χ C B S e (N := N)}
    (h₁ : IsGroundState i F χ C B S e a₁ p₁)
    (h₂ : IsGroundState i F χ C B S e a₂ p₂)
    (hd : (model i F χ C B S e).density p₁ =
      (model i F χ C B S e).density p₂) (he : e ≠ 0)
    (hχ : ∀ᵐ k ∂volume, χ.value k ≠ 0)
    (hρ : ∀ᵐ x ∂volume, 0 < densityL1 ((model i F χ C B S e).density p₁) x) :
    a₁.2.val =ᵐ[volume] a₂.2.val := by
  have hzero := vector_uniqueness_nonvanishing_cutoff i F χ C B S e W h₁ h₂ hd he hχ
  filter_upwards [hzero, hρ] with x hx hρx
  change densityL1 ((model i F χ C B S e).density p₁) x •
    (a₁.2.val x - a₂.2.val x) = 0 at hx
  exact sub_eq_zero.mp ((smul_eq_zero.mp hx).resolve_left (ne_of_gt hρx))

end PfHk
