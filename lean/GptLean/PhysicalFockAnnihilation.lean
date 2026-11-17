import GptLean.PhysicalFockSectorEnergy

/-!
Radiation bounds for the actual symmetric-sector annihilation operators.

The inverse-frequency kernel is represented by an actual L² function.
Moving its square-root frequency into the input wave function reduces
the estimate to Cauchy–Schwarz and the equal-coordinate energy identity.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- Moving a real frequency weight between the two sides of the L² pairing. -/
theorem tensorInsertion_weighted_inner (n : ℕ) (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (v : FullSector photonMeasure n) (u z : FullSector photonMeasure (n + 1))
    (hz : ∀ᵐ k ∂SectorMeasure photonMeasure (n + 1),
      z k = (Real.sqrt (‖(k 0).1‖) : ℂ) * u k) :
    ⟪tensorInsertion photonMeasure n f v, u⟫_ℂ =
      ⟪tensorInsertion photonMeasure n g v, z⟫_ℂ := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => photonMeasure) 0
  have hhead : ∀ᵐ k ∂SectorMeasure photonMeasure (n + 1),
      f (k 0) = (Real.sqrt ‖(k 0).1‖ : ℂ) * g (k 0) :=
    hp.quasiMeasurePreserving.ae
      ((Measure.quasiMeasurePreserving_fst (ν := SectorMeasure photonMeasure n)).ae hfg)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorInsertion_ae photonMeasure n f v,
    tensorInsertion_ae photonMeasure n g v, hz, hhead] with k hf hg hzk hfk
  rw [hf, hg, hzk, hfk]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem annihilationSector_tensor_duality (n : ℕ) (f : Lp ℂ 2 photonMeasure)
    (v : Sector photonMeasure n) (u : Sector photonMeasure (n + 1)) :
    ⟪v, annihilationSector photonMeasure n f u⟫_ℂ =
      (Real.sqrt (n + 1 : ℝ) : ℂ) * ⟪tensorInsertion photonMeasure n f v.val, u.val⟫_ℂ := by
  rw [← annihilationSector_duality]
  change ⟪(Real.sqrt (n + 1 : ℝ) : ℂ) •
    (symmetricSubspace photonMeasure (n + 1)).orthogonalProjectionOnto
      (tensorInsertion photonMeasure n f v.val), u⟫_ℂ = _
  rw [inner_smul_left, Complex.conj_ofReal,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

theorem annihilationSector_coordinateRoot_bound (n : ℕ) (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (u : Sector photonMeasure (n + 1)) (z : FullSector photonMeasure (n + 1))
    (hz : ∀ᵐ k ∂SectorMeasure photonMeasure (n + 1),
      z k = (Real.sqrt (‖(k 0).1‖) : ℂ) * u.val k) :
    ‖annihilationSector photonMeasure n f u‖ ≤ Real.sqrt (n + 1 : ℝ) * ‖g‖ * ‖z‖ := by
  let a := annihilationSector photonMeasure n f u
  have hi : ‖a‖ ^ 2 ≤ (Real.sqrt (n + 1 : ℝ) * ‖g‖ * ‖z‖) * ‖a‖ := by
    calc
      ‖a‖ ^ 2 = ‖⟪a, a⟫_ℂ‖ := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt (n + 1 : ℝ) *
          ‖⟪tensorInsertion photonMeasure n g a.val, z⟫_ℂ‖ := by
        rw [annihilationSector_tensor_duality n f a u,
          tensorInsertion_weighted_inner n f g hfg a.val u.val z hz,
          norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (n + 1 : ℝ) * (‖tensorInsertion photonMeasure n g a.val‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt (n + 1 : ℝ) * ‖g‖ * ‖z‖) * ‖a‖ := by
        rw [tensorInsertion_norm]
        change Real.sqrt (n + 1 : ℝ) * (‖g‖ * ‖a‖ * ‖z‖) = _
        ring
  by_cases ha : ‖a‖ = 0
  · change ‖a‖ ≤ _
    rw [ha]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha))).mp
      (by simpa only [pow_two] using hi)

theorem annihilationSector_radiation_bound (n : ℕ) (f g : Lp ℂ 2 photonMeasure)
    (hfg : ∀ᵐ p ∂photonMeasure, f p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (u : Sector photonMeasure (n + 1)) (hE : sectorRadiationForm (n + 1) u < ⊤) :
    ENNReal.ofReal (‖annihilationSector photonMeasure n f u‖ ^ 2) ≤
      ENNReal.ofReal (‖g‖ ^ 2) * sectorRadiationForm (n + 1) u := by
  obtain ⟨z, hz⟩ := exists_coordinateRoot_of_finite (0 : Fin (n + 1)) u hE
  rw [sectorRadiationForm_eq_coordinateRoot_norm (0 : Fin (n + 1)) u z hz,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖annihilationSector photonMeasure n f u‖ ^ 2 ≤
        (Real.sqrt (n + 1 : ℝ) * ‖g‖ * ‖z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (annihilationSector_coordinateRoot_bound n f g hfg u z hz) 2
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ))]
      push_cast
      ring

end GptLean.PhysicalFock
