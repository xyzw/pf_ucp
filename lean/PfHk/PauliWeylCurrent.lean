import PfHk.PauliWeylEnergy
import PfHk.PauliDensityWeighted
import PfHk.GroundState

/-! The difference of the two physical Pauli Weyl derivatives is the
actual spin-summed density times the external vector difference. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliWeylEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalWeyl GptLean.PhysicalPolarization GptLean.PhysicalPairDuality
  GptLean.PhysicalPairSpace GptLean.SymmetricLift GptLean.PhysicalSourceCoordinates
  PfHk.PauliSpin PfHk.PauliGroundState PfHk.PauliCurrentAlgebra
  PfHk.PhysicalCommonFormDomain PfHk.CenteredPhysicalReference

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 90000

private theorem weighted_current_difference {j₁ j₂ j a₁ a₂ m ρ w : ℝ}
    (h₁ : j₁ = j + a₁ * m) (h₂ : j₂ = j + a₂ * m) (hm : ρ = m) :
    w * j₁ - w * j₂ = w * (a₁ - a₂) * ρ := by
  rw [h₁, h₂, hm]
  ring

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion PauliCurrent.wave
  PauliReference.wave PauliGroundState.data derivatives covariant
  PauliCurrentAlgebra.current

variable (F : Frame) (χ : ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (e : ℝ) (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

set_option hygiene false in
local notation "κ" => profile (N := N) F χ 0
set_option hygiene false in
local notation "hκ" => profile_measurable (N := N) F χ 0
set_option hygiene false in
local notation "M" => profileBound F χ
set_option hygiene false in
local notation "hb" => profile_bound (N := N) F χ 0

theorem current_derivatives_ae (u : PauliGroundState.Ref N) (n : Fin N) (a : Fin 3) :
    (fun X => current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
      (fun b s => derivatives F χ C e A v c hc u (n, b) s X) a) =ᵐ[volume]
      fun X => current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hb e (n, b) (u s) X) a +
        vector A (n, a) X * density (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) := by
  filter_upwards [ae_all_iff.mpr (fun b => ae_all_iff.mpr
    (derivatives_ae F χ C e A v c hc u (n, b)))] with X hx
  exact (congrArg (fun d => current n
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X) d a)
      (funext fun b => funext (hx b))).trans
    (current_shift n _ _ (fun b => vector A (n, b) X) a)

theorem currentShift_integrable (f : Lp ℂ 2 photonMeasure) (u : PauliGroundState.Ref N)
    (n : Fin N) (a : Fin 3) :
    Integrable (fun X => classicalField κ f (n, a) X *
      current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
        (fun b s => derivatives F χ C e A v c hc u (n, b) s X) a) volume :=
  PauliExternalEnergyLp.current_integrable n
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (fun b => derivatives F χ C e A v c hc u (n, b)) a (classicalField κ f (n, a))
    (fun s => PauliWeylEnergyLp.bounded_multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (classicalField κ f (n, a))
      (classicalField_aestronglyMeasurable κ hκ f (n, a))
      (classicalField_bound κ M hb f (n, a)))

omit C e A v c hc in
theorem classicalField_position (f : Lp ℂ 2 photonMeasure)
    (n : Fin N) (a : Fin 3) (X : PhysicalSourceCoordinates.Configuration N) :
    classicalField κ f (n, a) X = classicalVector F χ f a ((split n) X).1 := by
  simp only [classicalField, profile, zero_add, PhysicalSourcePair.split_fst_eq_particle,
    classicalVector, PhysicalNonattainmentFluxKernel.physicalKernel, fieldKernel]

omit A v in
theorem currentShift_difference (A₁ A₂ : VectorPotential) (v₁ v₂ : ScalarPotential)
    (f : Lp ℂ 2 photonMeasure) (u : PauliGroundState.Ref N) (hN : 0 < N) :
    currentShift F χ C e A₁ v₁ c hc f u - currentShift F χ C e A₂ v₂ c hc f u =
      ∑ a, ∫ x, classicalVector F χ f a x *
        PfHk.vectorDifference (v₁, A₁) (v₂, A₂) (data C e F χ u) x a := by
  let weight : Fin 3 → PhysicalSourceCoordinates.Position → ℝ := fun a x =>
    classicalVector F χ f a x * (A₁.val x a - A₂.val x a)
  have heq (n : Fin N) (a : Fin 3) :
      (fun X => classicalField κ f (n, a) X *
        current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => derivatives F χ C e A₁ v₁ c hc u (n, b) s X) a -
        classicalField κ f (n, a) X *
        current n (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X)
          (fun b s => derivatives F χ C e A₂ v₂ c hc u (n, b) s X) a) =ᵐ[volume]
        fun X => weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2 := by
    filter_upwards [current_derivatives_ae F χ C e A₁ v₁ c hc u n a,
      current_derivatives_ae F χ C e A₂ v₂ c hc u n a,
      PauliReference.wave_norm_sq_ae u] with X h₁ h₂ hm
    have hr := weighted_current_difference (w := classicalField κ f (n, a) X) h₁ h₂ hm
    simpa only [weight, vector, vectorCoefficient,
      FriedrichsDivergenceBackground.configurationVector,
      CoordinateSobolev.coordinateCoefficient, PhysicalSourcePair.split_fst_eq_particle,
      classicalField_position F χ f n a X, density] using hr
  have hi (n : Fin N) (a : Fin 3) : Integrable
      (fun X => weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2) volume :=
    ((currentShift_integrable F χ C e A₁ v₁ c hc f u n a).sub
      (currentShift_integrable F χ C e A₂ v₂ c hc f u n a)).congr (heq n a)
  have hrow (a : Fin 3) :
      (∫ x, weight a x * densityL1 (data C e F χ u) x) =
        ∑ n, ∫ X, weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2 := by
    have ht := congrArg (fun ρ : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) =>
      ∫ x, weight a x * ρ x) (data_density_eq C e F χ hN u)
    exact ht.trans (PauliDensityWeighted.density_integral
      (PauliReference.wave u) (weight a) (fun n => hi n a))
  calc
    _ = ∑ n, ∑ a, ∫ X, weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2 := by
      unfold currentShift
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← integral_sub (currentShift_integrable F χ C e A₁ v₁ c hc f u n a)
        (currentShift_integrable F χ C e A₂ v₂ c hc f u n a)]
      exact integral_congr_ae (heq n a)
    _ = ∑ a, ∫ x, weight a x * densityL1 (data C e F χ u) x := by
      have hs : (∑ n : Fin N, ∑ a : Fin 3,
          ∫ X, weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2) =
          ∑ a : Fin 3, ∑ n : Fin N,
            ∫ X, weight a ((split n) X).1 * ‖PauliReference.wave u X‖ ^ 2 :=
        Finset.sum_comm
      exact hs.trans (Finset.sum_congr rfl fun a _ => (hrow a).symm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [weight, PfHk.vectorDifference, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        ring

end PfHk.PauliWeylEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
