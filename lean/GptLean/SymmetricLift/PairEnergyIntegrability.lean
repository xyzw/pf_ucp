import GptLean.SymmetricLift.CollisionGeometry
import GptLean.SymmetricLift.MetricGeometry
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Integral.Prod

/-! Local integrability of collision energy in full configuration space.
The proof splits a surjective linear map into an invertible change of
coordinates and a product projection, then uses compact-set Fubini. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift

open MeasureTheory MeasureTheory.Measure Set WithLp Filter
open scoped BigOperators Topology

section LinearPullback

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} {ν : Measure F} [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]

omit [FiniteDimensional ℝ E] in
/-- Invertible linear coordinate changes preserve local integrability of
real-valued functions with respect to Haar measures. -/
theorem locallyIntegrable_comp_linearEquiv (e : E ≃L[ℝ] F) {f : F → ℝ}
    (hf : LocallyIntegrable f ν) : LocallyIntegrable (f ∘ e) μ := by
  apply (locallyIntegrable_map_homeomorph e.toHomeomorph).mp
  change LocallyIntegrable f (μ.map e)
  rw [isAddLeftInvariant_eq_smul (μ.map e) ν]
  intro x
  obtain ⟨s, hs, hint⟩ := hf x
  refine ⟨s, hs, ?_⟩
  rw [IntegrableOn, Measure.restrict_smul]
  exact hint.smul_measure_nnreal

omit [BorelSpace E] [BorelSpace F] in
/-- A locally integrable function stays locally integrable after adjoining
unused finite-dimensional coordinates. -/
theorem locallyIntegrable_comp_snd {f : F → ℝ} (hf : LocallyIntegrable f ν) :
    LocallyIntegrable (fun x : E × F => f x.2) (μ.prod ν) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hfirst : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hsecond : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  have : IsFiniteMeasure (μ.restrict (Prod.fst '' K)) :=
    isFiniteMeasure_restrict.mpr hfirst.measure_lt_top.ne
  have hint := (hf.integrableOn_isCompact hsecond).comp_snd
    (μ.restrict (Prod.fst '' K))
  rw [Measure.prod_restrict] at hint
  change IntegrableOn (fun x : E × F => f x.2)
    ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) (μ.prod ν) at hint
  exact hint.mono_set (fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩)

/-- Pullback by a surjective linear map preserves local integrability.
A complement to its kernel gives the coordinate splitting needed by Fubini. -/
theorem locallyIntegrable_comp_surjective_linearMap (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) {f : F → ℝ} (hf : LocallyIntegrable f ν) :
    LocallyIntegrable (f ∘ L) μ := by
  let S : Submodule ℝ E := LinearMap.ker L
  obtain ⟨T, hT⟩ : ∃ T : Submodule ℝ E, IsCompl S T := Submodule.exists_isCompl S
  let M : (S × T) ≃ₗ[ℝ] E := Submodule.prodEquivOfIsCompl S T hT
  have hbij : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 hT.disjoint.symm,
      (LinearMap.surjective_domRestrict_iff hL).2 hT.symm.codisjoint⟩
  let L' : T ≃ₗ[ℝ] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) hbij
  have heq : ∀ x, L x = L' (M.symm x).2 := by
    intro x
    obtain ⟨y, z, hyz⟩ : ∃ (y : S) (z : T), M.symm x = (y, z) := ⟨_, _, rfl⟩
    have hx : x = M (y, z) := by
      rw [← hyz]
      simp only [LinearEquiv.apply_symm_apply]
    simp [L', M, hx]
  have hcomp : LocallyIntegrable (f ∘ L') (addHaar : Measure T) :=
    locallyIntegrable_comp_linearEquiv L'.toContinuousLinearEquiv hf
  have hprod : LocallyIntegrable (fun p : S × T => f (L' p.2))
      ((addHaar : Measure S).prod (addHaar : Measure T)) :=
    locallyIntegrable_comp_snd hcomp
  have hfinal := locallyIntegrable_comp_linearEquiv
    (μ := μ) M.toContinuousLinearEquiv.symm hprod
  change LocallyIntegrable (fun x => f (L' (M.symm x).2)) μ at hfinal
  simpa only [Function.comp_def, ← heq] using hfinal

omit [FiniteDimensional ℝ F] in
/-- Null exceptional sets pull back to null sets under a surjective linear
map. No measurability of the predicate itself is required. -/
theorem ae_comp_surjective_linearMap (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) {P : F → Prop} (hP : ∀ᵐ y ∂ν, P y) :
    ∀ᵐ x ∂μ, P (L x) := by
  have hq : QuasiMeasurePreserving L μ ν := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    obtain ⟨c, _, hc⟩ := L.exists_map_addHaar_eq_smul_addHaar μ ν hL
    rw [hc]
    exact smul_absolutelyContinuous
  exact hq.ae hP

end LinearPullback

/-- Projection onto the position of one particle, as a linear map. -/
def particleLinear {N : ℕ} (i : Fin N) :
    Configuration N →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := particle x i
  map_add' x y := by ext μ; rfl
  map_smul' c x := by ext μ; rfl

theorem particleLinear_surjective {N : ℕ} (i : Fin N) :
    Function.Surjective (particleLinear i) := by
  intro y
  refine ⟨toLp 2 (fun q : Fin N × Fin 3 => y q.2), ?_⟩
  ext μ
  rfl

/-- One-particle almost-everywhere properties hold at every particle
coordinate for almost every full configuration. -/
theorem ae_all_particles {N : ℕ} {P : EuclideanSpace ℝ (Fin 3) → Prop}
    (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x : Configuration N ∂volume, ∀ i : Fin N, P (particle x i) := by
  rw [ae_all_iff]
  intro i
  exact ae_comp_surjective_linearMap (particleLinear i) (particleLinear_surjective i) hP

/-- Almost-everywhere convergence in one-particle space lifts simultaneously
to all particle coordinates of almost every configuration. -/
theorem ae_particle_tendsto {N : ℕ} {A : Type*} [TopologicalSpace A]
    {u : ℕ → EuclideanSpace ℝ (Fin 3) → A} {v : EuclideanSpace ℝ (Fin 3) → A}
    (hu : ∀ᵐ y ∂volume, Tendsto (fun k => u k y) atTop (𝓝 (v y))) :
    ∀ᵐ x : Configuration N ∂volume, ∀ i : Fin N,
      Tendsto (fun k => u k (particle x i)) atTop (𝓝 (v (particle x i))) :=
  ae_all_particles hu

/-- The relative position of a fixed pair, as a linear map. -/
def pairDifferenceLinear {N : ℕ} (i j : Fin N) :
    Configuration N →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := particle x i - particle x j
  map_add' x y := by
    ext μ
    simp [particle]
    ring
  map_smul' c x := by
    ext μ
    simp [particle]
    ring

theorem pairDifferenceLinear_surjective {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Function.Surjective (pairDifferenceLinear i j) := by
  intro y
  refine ⟨toLp 2 (fun q : Fin N × Fin 3 => if q.1 = i then y q.2 else 0), ?_⟩
  ext μ
  simp [pairDifferenceLinear, particle, Ne.symm hij]

/-- Inverse-square pair distance is locally integrable on the entire
configuration space, including the collision diagonal. -/
theorem locallyIntegrable_inverse_square_pairDistance {N : ℕ} {i j : Fin N}
    (hij : i ≠ j) :
    LocallyIntegrable (fun x : Configuration N => (pairDistance x i j ^ 2)⁻¹) volume := by
  have h := locallyIntegrable_comp_surjective_linearMap
    (μ := volume) (pairDifferenceLinear i j) (pairDifferenceLinear_surjective hij)
    locallyIntegrable_inverse_square_norm_three
  simpa only [Function.comp_def, pairDifferenceLinear, pairDistance] using! h

/-- The finite sum of all unordered inverse-square pair interactions is
locally integrable for every particle number. -/
theorem locallyIntegrable_pairEnergy (N : ℕ) :
    LocallyIntegrable (pairEnergy : Configuration N → ℝ) volume := by
  unfold pairEnergy
  apply locallyIntegrable_finsetSum
  intro i _
  apply locallyIntegrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simpa only [ite_eq_left hij] using
      locallyIntegrable_inverse_square_pairDistance (ne_of_lt hij)
  · simpa only [ite_eq_right hij] using
      (locallyIntegrable_zero : LocallyIntegrable (fun _ : Configuration N => (0 : ℝ)) volume)

end GptLean.SymmetricLift
