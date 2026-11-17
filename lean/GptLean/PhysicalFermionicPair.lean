import GptLean.PhysicalSourceTests
import GptLean.PhysicalH1Permutation

/-!
The constructed marginal pair represents the summed physical particle
tests on the fermionic sector. Ordinary derivative covariance is proved
from the actual H1 graph. A field contribution can be added through its
own coordinate covariance law.
-/

noncomputable section

namespace GptLean.PhysicalFermionicPair

open MeasureTheory GptLean.SymmetricLift GptLean.ElectronicH1Complex
open GptLean.PhysicalPairSpace GptLean.PhysicalSourcePair

set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem tested_density (i : Fin N) (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (d : Fin 3 → PhysicalElectronicFermions.FullSpace N H)
    (f : Position → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x * densityL1 (ofWaveFunction i (realEquiv u) d) x) =
      ∫ z, (∑ j : Fin N, f (particle z j)) * ‖value u z‖ ^ 2 := by
  have hm := tested_density_ofWaveFunction i (realEquiv u) d f
    hf.aestronglyMeasurable (ae_of_all _ hb)
  simp only [split_fst_eq_particle, value_realEquiv] at hm
  exact hm.trans (PhysicalElectronicFermions.density_sum_integral N H
    ⟨value u, hu⟩ i hf hb).symm

theorem tested_current (i : Fin N) (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (d : Fin N × Fin 3 → PhysicalElectronicFermions.FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (j : Fin N) (b : Fin 3),
      ∀ᵐ x ∂volume, d (j, b) (permuteConfiguration π x) =
        PhysicalElectronicFermions.signCharacter N π • d (π.symm j, b) x)
    (b : Fin 3) (f : Position → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x * currentL1 (ofWaveFunction i (realEquiv u) (fun a => d (i, a))) x b) =
      ∫ z, ∑ j : Fin N, f (particle z j) *
        PhysicalPairIntegrability.currentComponent (value u z) (d (j, b) z) := by
  have hm := tested_current_ofWaveFunction i (realEquiv u) (fun a => d (i, a)) b f
    hf.aestronglyMeasurable (ae_of_all _ hb)
  simp only [split_fst_eq_particle, value_realEquiv] at hm
  exact hm.trans (PhysicalElectronicFermions.current_sum_integral N H
    ⟨value u, hu⟩ d hd i b hf hb).symm

omit [TopologicalSpace.SeparableSpace H] in
theorem scaled_derivative_covariance (c : ℂ) (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume, (c • derivative (i, a) u : PhysicalElectronicFermions.FullSpace N H)
        (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π •
        (c • derivative (π.symm i, a) u : PhysicalElectronicFermions.FullSpace N H) x := by
  have hp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul c (derivative (i, a) u))
  filter_upwards [hp, Lp.coeFn_smul c (derivative (π.symm i, a) u),
    PhysicalH1Permutation.fermionic_derivative_ae u hu π i a] with x hp hs hd
  simp only [Function.comp_apply, Pi.smul_apply] at hp hs
  rw [hp, hd, hs, smul_comm c (PhysicalElectronicFermions.signCharacter N π)]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem covariance_add
    (d e : Fin N × Fin 3 → PhysicalElectronicFermions.FullSpace N H)
    (hd : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, d (i, a) (permuteConfiguration π x) =
        PhysicalElectronicFermions.signCharacter N π • d (π.symm i, a) x)
    (he : ∀ (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3),
      ∀ᵐ x ∂volume, e (i, a) (permuteConfiguration π x) =
        PhysicalElectronicFermions.signCharacter N π • e (π.symm i, a) x)
    (π : Equiv.Perm (Fin N)) (i : Fin N) (a : Fin 3) :
    ∀ᵐ x ∂volume, (d (i, a) + e (i, a)) (permuteConfiguration π x) =
      PhysicalElectronicFermions.signCharacter N π • (d (π.symm i, a) + e (π.symm i, a)) x := by
  have hp := (permuteConfiguration π).measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_add (d (i, a)) (e (i, a)))
  filter_upwards [hp, Lp.coeFn_add (d (π.symm i, a)) (e (π.symm i, a)), hd π i a, he π i a]
    with x hp hs hd he
  simp only [Function.comp_apply, Pi.add_apply] at hp hs
  rw [hp, hd, he, hs, smul_add]

/-- The ordinary momentum current is represented by the actual summed
particle current, with covariance proved from the fermionic H1 state. -/
theorem tested_paramagnetic_current (i : Fin N) (u : ComplexH1 H (Fin N × Fin 3))
    (hu : value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (b : Fin 3) (f : Position → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x * currentL1 (ofWaveFunction i (realEquiv u)
      (fun a => -Complex.I • derivative (i, a) u)) x b) =
      ∫ z, ∑ j : Fin N, f (particle z j) * PhysicalPairIntegrability.currentComponent
        (value u z) ((-Complex.I • derivative (j, b) u : PhysicalElectronicFermions.FullSpace N H) z) :=
  tested_current i u hu (fun q => -Complex.I • derivative q u)
    (scaled_derivative_covariance (-Complex.I) u hu) b f hf hb

end GptLean.PhysicalFermionicPair
