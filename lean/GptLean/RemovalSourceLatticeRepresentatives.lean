import GptLean.RemovalSourceLattice

/-!
The original and localized WIS representatives use one spatial scalar
intertwining law, stated for arbitrary bounded measurable multipliers.
Linearity then gives the localized covariant product formula. No source
or derivative representative identity is assumed after localization.
-/

noncomputable section

namespace GptLean.RemovalSource

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open MeasureTheory MeasureTheory.Measure ElectronicLocalization SymmetricLift Filter

section ScalarIntertwining

variable {Q X H K : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  {μ : Measure Q} {ν : Measure X} [SFinite μ] [SFinite ν]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The ordinary WIS action commutes with every bounded spatial scalar.
This universal formulation is independent of any localization family. -/
def SpatialScalarIntertwining (U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)) : Prop :=
  ∀ (g : X → ℝ), AEStronglyMeasurable g ν → ∀ C : ℝ, (∀ x, |g x| ≤ C) →
    ∀ u v : Lp H 2 ν, (v : X → H) =ᵐ[ν] (fun x => (g x : ℂ) • u x) →
      (U v : Q × X → K) =ᵐ[μ.prod ν] (fun qx => (g qx.2 : ℂ) • U u qx)

theorem boundedRealProduct_memLp (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
    (C : ℝ) (hb : ∀ x, |g x| ≤ C) (u : Lp H 2 ν) :
    MemLp (fun x => (g x : ℂ) • u x) 2 ν := by
  apply ((Lp.memLp u).norm.const_mul C).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg).smul (Lp.memLp u).1)
  filter_upwards with x
  change ‖(g x : ℂ) • u x‖ ≤ C * ‖u x‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

def boundedRealProduct (g : X → ℝ) (hg : AEStronglyMeasurable g ν)
    (C : ℝ) (hb : ∀ x, |g x| ≤ C) (u : Lp H 2 ν) : Lp H 2 ν :=
  (boundedRealProduct_memLp g hg C hb u).toLp _

theorem partition_abs_le_one (f : ℕ → X → ℝ)
    (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1) (n : ℕ) (x : X) : |f n x| ≤ 1 := by
  have h := partition_square_le_one f hpart n x
  exact (sq_le_one_iff_abs_le_one _).mp h

theorem SpatialScalarIntertwining.localized_eq_mul
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} (hU : SpatialScalarIntertwining U)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (u : Lp H 2 ν) (n : ℕ) :
    (U (localizedVector f hpart hf u n) : Q × X → K) =ᵐ[μ.prod ν]
      (fun qx => (f n qx.2 : ℂ) • U u qx) :=
  hU (f n) (hf n) 1 (partition_abs_le_one f hpart n) u _
    (localized_memLp f hpart hf u n).coeFn_toLp

theorem SpatialScalarIntertwining.localized_commute
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} (hU : SpatialScalarIntertwining U)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (u : Lp H 2 ν) (n : ℕ) :
    U (localizedVector f hpart hf u n) = productLocalizedVector f hpart hf (U u) n := by
  let g : ℕ → Q × X → ℝ := fun a qx => f a qx.2
  have hgm (a : ℕ) : AEStronglyMeasurable (g a) (μ.prod ν) :=
    (hf a).comp_quasiMeasurePreserving quasiMeasurePreserving_snd
  have hp := (localized_memLp (ν := μ.prod ν) g (fun qx => hpart qx.2) hgm (U u) n).coeFn_toLp
  apply Lp.ext
  exact (hU.localized_eq_mul f hpart hf u n).trans hp.symm

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem SpatialScalarIntertwining.covariant_eq_mul
    {U : Lp H 2 ν ≃ₗᵢ[ℂ] Lp K 2 (μ.prod ν)} (hU : SpatialScalarIntertwining U)
    (f : ℕ → X → ℝ) (hpart : ∀ x, HasSum (fun a => f a x ^ 2) 1)
    (hf : ∀ a, AEStronglyMeasurable (f a) ν) (u du : Lp H 2 ν) (v : X)
    (hm : ∀ a, MemLp (localizedDerivative f du u v a) 2 ν) (n : ℕ)
    (hdf : AEStronglyMeasurable (fun x => fderiv ℝ (f n) x v) ν)
    (C : ℝ) (hb : ∀ x, |fderiv ℝ (f n) x v| ≤ C) :
    (U (localizedDerivativeVector f u du v hm n) : Q × X → K) =ᵐ[μ.prod ν]
      (fun qx => (f n qx.2 : ℂ) • U du qx -
        Complex.I • (fderiv ℝ (f n) qx.2 v : ℂ) • U u qx) := by
  let z := boundedRealProduct (fun x => fderiv ℝ (f n) x v) hdf C hb u
  let w := localizedVector f hpart hf du n
  have hz : (z : X → H) =ᵐ[ν] (fun x => (fderiv ℝ (f n) x v : ℂ) • u x) :=
    (boundedRealProduct_memLp _ hdf C hb u).coeFn_toLp
  have hw : (w : X → H) =ᵐ[ν] (fun x => (f n x : ℂ) • du x) :=
    (localized_memLp f hpart hf du n).coeFn_toLp
  have he : localizedDerivativeVector f u du v hm n = w - Complex.I • z := by
    apply Lp.ext
    filter_upwards [(hm n).coeFn_toLp, Lp.coeFn_sub w (Complex.I • z),
      Lp.coeFn_smul Complex.I z, hz, hw] with x hx hs hi hz hw
    change (hm n).toLp _ x = _
    rw [hx, hs, Pi.sub_apply, hi, Pi.smul_apply, hz, hw]
    rfl
  rw [he, map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (U w) (Complex.I • U z), Lp.coeFn_smul Complex.I (U z),
    hU.localized_eq_mul f hpart hf du n, hU _ hdf C hb u z hz] with qx hs hi hw hz
  rw [hs, Pi.sub_apply, hi, Pi.smul_apply, hw, hz]

end ScalarIntertwining

variable {N : ℕ}

theorem latticeMultiplier_permute (R : ℝ) (n : ℕ) (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    latticeMultiplier R n (permuteConfiguration π x) = latticeMultiplier R n x := by
  rcases zeroPad_cases (latticeIndex N) (latticeLabelMultiplier R) n with hz | ⟨α, he⟩
  · change zeroPad _ _ n _ = zeroPad _ _ n _
    rw [hz]
    rfl
  · change zeroPad _ _ n _ = zeroPad _ _ n _
    rw [he]
    have hP : configurationParticles (permuteConfiguration π x) =
        configurationParticles x ∘ π.symm := by
      funext i
      exact particle_permute π x i
    unfold latticeLabelMultiplier
    rw [hP, symmetricMultiplier_perm]

theorem latticeMultiplier_derivative_bound (R : ℝ) (hR : 0 < R)
    (n : ℕ) (j : Fin N × Fin 3) (x : Configuration N) :
    |fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1)| ≤
      Real.sqrt (LatticePartition.metricConstant / R ^ 2) := by
  have hs : Summable (fun a => fderiv ℝ (latticeMultiplier R a) x
      (EuclideanSpace.single j 1) ^ 2) := by
    apply summable_of_hasFiniteSupport
    apply ((latticeMultiplier_locallyFinite R).point_finite x).subset
    intro a ha hzero
    apply ha
    change fderiv ℝ (latticeMultiplier R a) x (EuclideanSpace.single j 1) ^ 2 = 0
    rw [fderiv_eq_zero_of_nonneg (latticeMultiplier_nonneg R a) hzero]
    simp
  have h := hs.sum_le_tsum {n} (fun _ _ => sq_nonneg _)
  simp only [Finset.sum_singleton] at h
  exact Real.abs_le_sqrt (h.trans (latticeMultiplier_coordinate_metric R hR j x))

theorem latticeMultiplier_weakH1Local (R : ℝ) (hR : 0 < R) (n : ℕ) :
    HasWeakH1Local (latticeMultiplier (N := N) R n)
      (fun j x => fderiv ℝ (latticeMultiplier R n) x (EuclideanSpace.single j 1)) := by
  apply Repair.weakH1Local_of_differentiable_bounded (latticeMultiplier_differentiable R n)
    (Real.sqrt (LatticePartition.metricConstant / R ^ 2))
  intro j x
  rw [Real.norm_eq_abs]
  exact latticeMultiplier_derivative_bound R hR n j x

section Source

variable {Q H K Hr Kr Hs : Type*} [MeasurableSpace Q] {μ : Measure Q} [SFinite μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup Hr] [InnerProductSpace ℂ Hr]
  [NormedAddCommGroup Kr] [InnerProductSpace ℂ Kr]
  [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

namespace LatticeSourceData

variable (D : LatticeSourceData N μ H K Hr Kr Hs)

/-- WIS representation of the original spectral data, before localization. -/
def original : RemovalEnergy.ConditionedSource μ (volume : Measure (Configuration N))
    (Fin N × Fin 3) K Kr where
  source n := D.U (D.ψ n)
  covariant n j := D.U (D.dψ n j)
  rest n := D.Ur (D.rest n)
  normalized := by simpa only [D.U.norm_map] using D.mass
  kinetic_summable := by
    simpa only [D.U.norm_map] using
      (summable_sum (s := Finset.univ) (fun j _ => D.kinetic_summable j)).mul_left (1 / 2 : ℝ)
  rest_summable := by simpa only [D.Ur.norm_map] using D.rest_summable
  soft n := ‖D.soft n‖ ^ 2
  soft_nonneg n := sq_nonneg _
  soft_summable := D.soft_summable

theorem covariant_eq_mul (R : ℝ) (hR : 0 < R) (hU : SpatialScalarIntertwining D.U)
    (n : ℕ) (j : Fin N × Fin 3) :
    ((D.conditioned R hR).covariant n j : Q × Configuration N → K) =ᵐ[μ.prod volume]
      (fun qx => (latticeMultiplier R (Nat.unpair n).2 qx.2 : ℂ) •
          D.U (D.dψ (Nat.unpair n).1 j) qx -
        Complex.I • (fderiv ℝ (latticeMultiplier R (Nat.unpair n).2) qx.2
          (EuclideanSpace.single j 1) : ℂ) • D.U (D.ψ (Nat.unpair n).1) qx) := by
  apply SpatialScalarIntertwining.covariant_eq_mul hU (latticeMultiplier R)
    (latticeMultiplier_partition R) (latticeMultiplier_measurable R)
    (D.ψ (Nat.unpair n).1) (D.dψ (Nat.unpair n).1 j) (EuclideanSpace.single j 1) _
    (Nat.unpair n).2 (latticeMultiplier_derivative_measurable R _ j)
    (Real.sqrt (LatticePartition.metricConstant / R ^ 2))
    (latticeMultiplier_derivative_bound R hR _ j)

end LatticeSourceData
end Source
end GptLean.RemovalSource
