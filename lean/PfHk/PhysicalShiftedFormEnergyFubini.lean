import GptLean.PhysicalPFParticle

/-! Unbounded tests of actual particle marginals.

The only integrability input is the corresponding configuration-space
product. Thus the identities apply to form-domain scalar and vector
potentials, without replacing them by bounded coefficients.
-/

noncomputable section
namespace PfHk.PhysicalShiftedFormEnergyFubini

open MeasureTheory GptLean GptLean.PhysicalSourceFubini
  GptLean.PhysicalSourceCoordinates GptLean.PhysicalSourceMarginal
  GptLean.ElectronicH1Space GptLean.PhysicalPairSpace
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

section Product

variable {X Y H : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsSeparable ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

theorem curry_weighted_norm_sq (u : Lp H 2 (μ.prod ν)) (a : X → ℝ)
    (hi : Integrable (fun z => a z.1 * ‖u z‖ ^ 2) (μ.prod ν)) :
    (∫ x, a x * ‖curry u x‖ ^ 2 ∂μ) =
      ∫ z, a z.1 * ‖u z‖ ^ 2 ∂μ.prod ν := by
  calc
    _ = ∫ x, a x * (∫ y, ‖u (x, y)‖ ^ 2 ∂ν) ∂μ := by
      apply integral_congr_ae
      filter_upwards [curry_norm_sq_ae u] with x hx
      exact congrArg (fun t : ℝ => a x * t) hx
    _ = ∫ x, ∫ y, a x * ‖u (x, y)‖ ^ 2 ∂ν ∂μ := by
      simp only [integral_const_mul]
    _ = _ := (integral_prod _ hi).symm

theorem curry_weighted_re_inner (u v : Lp H 2 (μ.prod ν)) (a : X → ℝ)
    (hi : Integrable (fun z => a z.1 * (⟪u z, v z⟫_ℂ).re) (μ.prod ν)) :
    (∫ x, a x * (⟪curry u x, curry v x⟫_ℂ).re ∂μ) =
      ∫ z, a z.1 * (⟪u z, v z⟫_ℂ).re ∂μ.prod ν := by
  have he : (fun x => (⟪curry u x, curry v x⟫_ℂ).re) =ᵐ[μ]
      fun x => ∫ y, (⟪u (x, y), v (x, y)⟫_ℂ).re ∂ν := by
    filter_upwards [curry_inner_ae u v, (L2.integrable_inner (𝕜 := ℂ) u v).prod_right_ae]
      with x hx hix
    exact (congrArg Complex.re hx).trans (integral_re hix).symm
  calc
    _ = ∫ x, a x * (∫ y, (⟪u (x, y), v (x, y)⟫_ℂ).re ∂ν) ∂μ :=
      integral_congr_ae (he.mono fun x hx => congrArg (fun t : ℝ => a x * t) hx)
    _ = ∫ x, ∫ y, a x * (⟪u (x, y), v (x, y)⟫_ℂ).re ∂ν ∂μ := by
      simp only [integral_const_mul]
    _ = _ := (integral_prod _ hi).symm

end Product

section Particle

variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem particleMap_weighted_norm_sq (i : Fin N) (u : L2 H (Fin N × Fin 3))
    (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : Integrable (fun z => a ((split i) z).1 * ‖u z‖ ^ 2) volume) :
    (∫ x, a x * ‖particleMap i u x‖ ^ 2) =
      ∫ z, a ((split i) z).1 * ‖u z‖ ^ 2 := by
  let U := productMap (split i) (split_symm_measurePreserving i) u
  have he : (fun p => a p.1 * ‖U p‖ ^ 2) =ᵐ[volume.prod volume]
      fun p => a ((split i) ((split i).symm p)).1 * ‖u ((split i).symm p)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (split_symm_measurePreserving i)] with p hp
    change a p.1 * ‖Lp.compMeasurePreserving (split i).symm
      (split_symm_measurePreserving i) u p‖ ^ 2 = _
    rw [hp]
    simp only [(split i).apply_symm_apply, Function.comp_apply]
  have hprod : Integrable (fun p => a p.1 * ‖U p‖ ^ 2) (volume.prod volume) :=
    ((split_symm_measurePreserving i).integrable_comp_of_integrable hi).congr he.symm
  exact (curry_weighted_norm_sq U a hprod).trans
    ((integral_congr_ae he).trans ((split_symm_measurePreserving i).integral_comp
      (split i).symm.toHomeomorph.measurableEmbedding
      (fun z => a ((split i) z).1 * ‖u z‖ ^ 2)))

theorem particleMap_weighted_re_inner (i : Fin N) (u v : L2 H (Fin N × Fin 3))
    (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : Integrable (fun z => a ((split i) z).1 * (⟪u z, v z⟫_ℂ).re) volume) :
    (∫ x, a x * (⟪particleMap i u x, particleMap i v x⟫_ℂ).re) =
      ∫ z, a ((split i) z).1 * (⟪u z, v z⟫_ℂ).re := by
  let U := productMap (split i) (split_symm_measurePreserving i) u
  let V := productMap (split i) (split_symm_measurePreserving i) v
  have he : (fun p => a p.1 * (⟪U p, V p⟫_ℂ).re) =ᵐ[volume.prod volume]
      fun p => a ((split i) ((split i).symm p)).1 *
        (⟪u ((split i).symm p), v ((split i).symm p)⟫_ℂ).re := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (split_symm_measurePreserving i),
      Lp.coeFn_compMeasurePreserving v (split_symm_measurePreserving i)] with p hu hv
    change a p.1 * (⟪Lp.compMeasurePreserving (split i).symm
      (split_symm_measurePreserving i) u p,
      Lp.compMeasurePreserving (split i).symm (split_symm_measurePreserving i) v p⟫_ℂ).re = _
    rw [hu, hv]
    simp only [(split i).apply_symm_apply, Function.comp_apply]
  have hprod : Integrable (fun p => a p.1 * (⟪U p, V p⟫_ℂ).re) (volume.prod volume) :=
    ((split_symm_measurePreserving i).integrable_comp_of_integrable hi).congr he.symm
  exact (curry_weighted_re_inner U V a hprod).trans
    ((integral_congr_ae he).trans ((split_symm_measurePreserving i).integral_comp
      (split i).symm.toHomeomorph.measurableEmbedding
      (fun z => a ((split i) z).1 * (⟪u z, v z⟫_ℂ).re)))

theorem density_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : Integrable (fun z => a ((split i) z).1 * ‖value u z‖ ^ 2) volume) :
    (∫ x, a x * densityL1 (PhysicalSourcePair.ofWaveFunction i u d) x) =
      (N : ℝ) * ∫ z, a ((split i) z).1 * ‖value u z‖ ^ 2 := by
  calc
    _ = ∫ x, (N : ℝ) * (a x * ‖particleMap i (value u) x‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [PhysicalPairRealization.density_ofSource_ae N (particleMap i (value u))
        (fun b => particleMap i (d b)) (Lp.memLp _) (particleSource_memLp_six i u)
        (fun _ => Lp.memLp _)] with x hx
      change a x * densityL1 (PhysicalPairRealization.ofSource N _ _ _ _ _) x = _
      rw [hx]
      simp only [PhysicalPairIntegrability.density]
      ring
    _ = (N : ℝ) * ∫ x, a x * ‖particleMap i (value u) x‖ ^ 2 := integral_const_mul _ _
    _ = _ := congrArg (fun t : ℝ => (N : ℝ) * t)
      (particleMap_weighted_norm_sq i (value u) a hi)

theorem current_ofWaveFunction (i : Fin N) (u : H1 H (Fin N × Fin 3))
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (b : Fin 3) (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : Integrable (fun z => a ((split i) z).1 *
      (⟪value u z, d b z⟫_ℂ).re) volume) :
    (∫ x, a x * currentL1 (PhysicalSourcePair.ofWaveFunction i u d) x b) =
      (N : ℝ) * ∫ z, a ((split i) z).1 * (⟪value u z, d b z⟫_ℂ).re :=
  (PhysicalSourcePair.tested_current_ofSource (particleMap i (value u))
    (fun c => particleMap i (d c)) (Lp.memLp _) (particleSource_memLp_six i u)
    (fun _ => Lp.memLp _) b a).trans
    (congrArg (fun t : ℝ => (N : ℝ) * t)
      (particleMap_weighted_re_inner i (value u) (d b) a hi))

theorem fermionic_density (i : Fin N) (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3))
    (hu : ElectronicH1Complex.value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (d : Fin 3 → L2 H (Fin N × Fin 3)) (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : ∀ n, Integrable (fun z => a (SymmetricLift.particle z n) *
      ‖ElectronicH1Complex.value u z‖ ^ 2) volume) :
    (∫ x, a x * densityL1
      (PhysicalSourcePair.ofWaveFunction i (ElectronicH1Complex.realEquiv (E := H) (I := Fin N × Fin 3) u) d) x) =
      ∫ z, (∑ n, a (SymmetricLift.particle z n)) * ‖ElectronicH1Complex.value u z‖ ^ 2 := by
  have h := density_ofWaveFunction i (ElectronicH1Complex.realEquiv (E := H) (I := Fin N × Fin 3) u) d a
    (by simpa only [PhysicalSourcePair.split_fst_eq_particle,
      ElectronicH1Complex.value_realEquiv] using hi i)
  simp only [PhysicalSourcePair.split_fst_eq_particle,
    ElectronicH1Complex.value_realEquiv] at h
  refine h.trans ?_
  symm
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ => hi n)]
  simp_rw [PhysicalElectronicFermions.density_particle_integral_eq N H
    ⟨ElectronicH1Complex.value u, hu⟩ _ i a]
  simp

theorem fermionic_current (i : Fin N) (u : ElectronicH1Complex.ComplexH1 H (Fin N × Fin 3))
    (hu : ElectronicH1Complex.value u ∈ PhysicalElectronicFermions.fermionicSubspace N H)
    (d : (Fin N × Fin 3) → L2 H (Fin N × Fin 3))
    (hd : ∀ (π : Equiv.Perm (Fin N)) (n : Fin N) (b : Fin 3),
      ∀ᵐ X ∂volume, d (n, b) (SymmetricLift.permuteConfiguration π X) =
        PhysicalElectronicFermions.signCharacter N π • d (π.symm n, b) X)
    (b : Fin 3) (a : PhysicalSourceCoordinates.Position → ℝ)
    (hi : ∀ n, Integrable (fun z => a (SymmetricLift.particle z n) *
      (⟪ElectronicH1Complex.value u z, d (n, b) z⟫_ℂ).re) volume) :
    (∫ x, a x * currentL1
      (PhysicalSourcePair.ofWaveFunction i (ElectronicH1Complex.realEquiv (E := H) (I := Fin N × Fin 3) u)
        (fun b => d (i, b))) x b) =
      ∫ z, ∑ n, a (SymmetricLift.particle z n) *
        (⟪ElectronicH1Complex.value u z, d (n, b) z⟫_ℂ).re := by
  have h := current_ofWaveFunction i (ElectronicH1Complex.realEquiv (E := H) (I := Fin N × Fin 3) u)
    (fun b => d (i, b)) b a (by
      simpa only [PhysicalSourcePair.split_fst_eq_particle,
        ElectronicH1Complex.value_realEquiv] using hi i)
  simp only [PhysicalSourcePair.split_fst_eq_particle,
    ElectronicH1Complex.value_realEquiv] at h
  refine h.trans ?_
  symm
  rw [integral_finsetSum _ (fun n _ => hi n)]
  change (∑ n, ∫ z, a (SymmetricLift.particle z n) *
    PhysicalPairIntegrability.currentComponent (ElectronicH1Complex.value u z) (d (n, b) z)) = _
  simp_rw [PhysicalElectronicFermions.current_particle_integral_eq N H
    ⟨ElectronicH1Complex.value u, hu⟩ d hd _ i b a]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl

end Particle
end PfHk.PhysicalShiftedFormEnergyFubini
