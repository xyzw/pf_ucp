import PfHk.PhysicalShiftedFormEnergyLp
import PfHk.PhysicalParticleFubini
import PfHk.PhysicalCommonFormDomain
import PfHk.PhysicalReferenceCoulombEquiv
import GptLean.TransformationsPotentials
import GptLean.AppendixAGaugeForm

/-! The literal external quadratic form and the paper's shifted pair energy.
All scalar and vector terms are evaluated through their actual L2
multipliers. The marginal formulas allow the full stated potential class.
-/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PhysicalShiftedFormEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.PhysicalPairSpace GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

local instance shiftedPhotonRealInner : InnerProductSpace ℝ PhotonFock :=
  PhysicalCommonFormDomain.commonPhotonRealInner

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  PhysicalPFReference.referenceSubspace PhysicalReferenceCoulombEquiv.equiv
  externalEnergy energy kineticEnergy externalCovariant

private theorem energy_accounting {J : Type*} [Fintype J]
    (x y yr m a : J → ℝ) (r rr v0 vc ci pp nn vs : ℝ)
    (hx : ∀ j, x j = y j + 2 * m j + a j) (hy : ∀ j, yr j = y j)
    (hr : rr = r) (hzero : v0 = 0) (hc : vc = ci) (hs : pp - nn = vs + ci) :
    (1 / 2 : ℝ) * (∑ j, x j) + r + v0 + pp - nn =
      ((1 / 2 : ℝ) * (∑ j, yr j) + rr + vc) + vs + (∑ j, m j) +
        (1 / 2 : ℝ) * (∑ j, a j) := by
  simp only [hx, hy, hr, hzero, hc, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith only [hs]

def scalarPairing (v : ScalarPotential) (P : PhysicalPairSpace.Pair) : ℝ :=
  pairing (α := PhysicalSourceCoordinates.Position) (E := ℝ) (μ := volume)
    (p := (3 : ℝ≥0∞)) (q := (3 / 2 : ℝ≥0∞)) v P.1

def vectorPairing (A : VectorPotential) (P : PhysicalPairSpace.Pair) : ℝ :=
  pairing (α := PhysicalSourceCoordinates.Position) (E := PhysicalPairSpace.Vector) (μ := volume)
    (p := (3 / 2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞)) A P.2

theorem pairPotential_eq_parts (v : ScalarPotential) (A : VectorPotential)
    (P : PhysicalPairSpace.Pair) :
    pairPotential (v, A) P = scalarPairing v P + vectorPairing A P := rfl

theorem scalarPairing_eq_integral (v : ScalarPotential) (P : PhysicalPairSpace.Pair) :
    scalarPairing v P = ∫ x, v.val x * densityL1 P x :=
  TransformationsPotentials.pairing_density v P

theorem vectorPairing_eq_integral (A : VectorPotential) (P : PhysicalPairSpace.Pair) :
    vectorPairing A P = ∫ x, inner ℝ (A.val x) (currentL1 P x) :=
  TransformationsPotentials.pairing_current A P

theorem vectorPairing_eq_sum_integrals (A : VectorPotential) (P : PhysicalPairSpace.Pair) :
    vectorPairing A P = ∑ b : Fin 3, ∫ x, A.val x b * currentL1 P x b := by
  have hA := TransformationsGauge.vectorPotential_component_in_sum A
  have hm (b : Fin 3) : Integrable (fun x => A.val x b * currentL1 P x b) volume :=
    memLp_one_iff_integrable.mp ((hA b).mul_memLp_one
      ((Lp.memLp (currentL1 P)).eval_piLp b)
      ((TransformationsGauge.SpatialGauge.current_memLp_three_halves P).eval_piLp b))
  have hinner (x : PhysicalSourceCoordinates.Position) :
      inner ℝ (A.val x) (currentL1 P x) = ∑ b : Fin 3, A.val x b * currentL1 P x b := by
    simp only [PiLp.inner_apply, Real.inner_apply]
  exact (vectorPairing_eq_integral A P).trans
    ((integral_congr_ae (Filter.Eventually.of_forall hinner)).trans
      (integral_finsetSum _ (fun b _ => hm b)))

private theorem sum_components {N : ℕ} (f : Fin N × Fin 3 → ℝ) :
    (∑ b : Fin 3, ∑ n : Fin N, f (n, b)) = ∑ q : Fin N × Fin 3, f q :=
  (Finset.sum_comm).trans (Fintype.sum_prod_type f).symm

attribute [local irreducible] scalarPairing vectorPairing

variable {N : ℕ}

private theorem potential_norm_sq_ae {I : Type} [Fintype I] [DecidableEq I]
    (V : PhysicalPFReference.Position I → ℝ) (hV : ∀ X, 0 ≤ V X)
    (u : Reference I V) :
    (fun X => ‖potential I V u X‖ ^ 2) =ᵐ[volume]
      fun X => V X * ‖inclusion I V u X‖ ^ 2 := by
  have hp : ∀ᵐ X ∂volume, potential I V u X = (Real.sqrt (V X) : ℂ) •
      PhysicalMultiplicationGraph.inclusion volume _ (potentialSource I V u) X := by
    unfold potential
    exact (potentialSource I V u).property
  have hv := potential_matches I V u
  filter_upwards [hp] with X hX
  have hval := congrArg (fun w : WaveSpace I => w X) hv
  have hpoint : potential I V u X = (Real.sqrt (V X) : ℂ) • inclusion I V u X :=
    hX.trans (congrArg (fun w : PhotonFock => (Real.sqrt (V X) : ℂ) • w) hval)
  exact (congrArg (fun w : PhotonFock => ‖w‖ ^ 2) hpoint).trans
    (PhysicalShiftedFormEnergyLp.sqrt_smul_norm_sq (V X) (hV X) (inclusion I V u X))

private theorem potential_integrable {I : Type} [Fintype I] [DecidableEq I]
    (V : PhysicalPFReference.Position I → ℝ) (hV : ∀ X, 0 ≤ V X)
    (u : Reference I V) :
    Integrable (fun X => V X * ‖inclusion I V u X‖ ^ 2) volume :=
  (Lp.memLp (potential I V u)).norm.integrable_sq.congr (potential_norm_sq_ae V hV u)

private theorem potential_norm_sq {I : Type} [Fintype I] [DecidableEq I]
    (V : PhysicalPFReference.Position I → ℝ) (hV : ∀ X, 0 ≤ V X)
    (u : Reference I V) :
    ‖potential I V u‖ ^ 2 = ∫ X, V X * ‖inclusion I V u X‖ ^ 2 := by
  have h := GptLean.Repair.toL2_norm_sq (Lp.memLp (potential I V u))
  simp only [Lp.toLp_coeFn] at h
  exact h.trans (integral_congr_ae (potential_norm_sq_ae V hV u))

def scalarSum (v : ScalarPotential) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : ℝ :=
  ∑ n : Fin N, ∫ X, CoordinateSobolev.coordinateCoefficient n
    (v.val : PhysicalSourceCoordinates.Position → ℝ) X *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2

def squareSum (A : VectorPotential) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : ℝ :=
  ∑ q : Fin N × Fin 3, ∫ X, vector A q X ^ 2 *
    ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2

theorem scalar_integrable (v : ScalarPotential) (n : Fin N)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (fun X => CoordinateSobolev.coordinateCoefficient n
      (v.val : PhysicalSourceCoordinates.Position → ℝ) X *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2) volume := by
  apply (scalar_coordinate_integrable v n u).mono'
    ((CoordinateSobolev.coordinateCoefficient_measurable n v.val.aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable (inclusion (Fin N × Fin 3) (fun _ => 0) u)).norm.pow 2))
  filter_upwards [] with X
  simp only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
  exact le_rfl

theorem square_integrable (A : VectorPotential) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (fun X => vector A q X ^ 2 *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2) volume :=
  PhysicalShiftedFormEnergyLp.multiplier_square_integrable _ _
    ((externalDomain A (0 : ScalarPotential) 0 le_rfl u).vector q)

variable (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

def magneticSum (A : VectorPotential) (u : Reference (Fin N × Fin 3) (fun _ => 0)) : ℝ :=
  ∑ q : Fin N × Fin 3, ∫ X, vector A q X *
    (⟪inclusion (Fin N × Fin 3) (fun _ => 0) u X,
      covariant (Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e q u X⟫_ℂ).re

theorem magnetic_integrable (A : VectorPotential) (q : Fin N × Fin 3)
    (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    Integrable (fun X => vector A q X *
      (⟪inclusion (Fin N × Fin 3) (fun _ => 0) u X,
        covariant (Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e q u X⟫_ℂ).re) volume :=
  PhysicalShiftedFormEnergyLp.multiplier_cross_integrable _ _ _
    ((externalDomain A (0 : ScalarPotential) 0 le_rfl u).vector q)

attribute [local irreducible] scalarSum squareSum magneticSum

theorem external_energy_expansion (A : VectorPotential) (v : ScalarPotential)
    (c : ℝ) (hc : 0 ≤ c) (u : Reference (Fin N × Fin 3) (fun _ => 0)) :
    externalEnergy (I := Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e
      (vector A) (positive v c) (negative v c) u (externalDomain A v c hc u) =
    energy (Fin N × Fin 3) (fun X => c * PhysicalCoulombH1.potential N X)
      C κP hκP M hbP e (PhysicalReferenceCoulombEquiv.equiv (N := N) c hc u) +
      scalarSum (N := N) v u + magneticSum (N := N) C K hK M hM e A u + (1 / 2 : ℝ) * squareSum (N := N) A u := by
  let D := externalDomain A v c hc u
  let ψ : WaveSpace (Fin N × Fin 3) := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let d : (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3) := fun q => covariant (Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e q u
  let Vc := fun X : Configuration N => c * PhysicalCoulombH1.potential N X
  let w := PhysicalReferenceCoulombEquiv.equiv (N := N) c hc u
  have hterm (q : Fin N × Fin 3) :
      ‖externalCovariant (I := Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e
        (vector A) (positive v c) (negative v c) u D q‖ ^ 2 =
      ‖d q‖ ^ 2 + 2 * (∫ X, vector A q X * (⟪ψ X, d q X⟫_ℂ).re) +
        ∫ X, vector A q X ^ 2 * ‖ψ X‖ ^ 2 := by
    unfold externalCovariant roughMultiply
    exact PhysicalShiftedFormEnergyLp.norm_add_multiplier_sq ψ (d q) (vector A q) (D.vector q)
  have hscalar : ‖roughMultiply (positive v c) ψ D.positive‖ ^ 2 -
      ‖roughMultiply (negative v c) ψ D.negative‖ ^ 2 =
      ∫ X, scalar v c X * ‖ψ X‖ ^ 2 := by
    unfold roughMultiply
    exact PhysicalShiftedFormEnergyLp.signed_multiplier_difference ψ (positive v c) (negative v c)
      (scalar v c) D.positive D.negative (Filter.Eventually.of_forall fun X =>
        SignedScalarMultiplier.amplitude_difference (scalar v c) X)
  have hpot0 : ‖potential (Fin N × Fin 3) (fun _ => 0) u‖ ^ 2 = 0 := by
    exact (potential_norm_sq (fun _ => 0) (fun _ => le_rfl) u).trans (by simp)
  have hrad : ‖radiation (Fin N × Fin 3) Vc w‖ ^ 2 =
      ‖radiation (Fin N × Fin 3) (fun _ => 0) u‖ ^ 2 :=
    congrArg (fun z : WaveSpace (Fin N × Fin 3) => ‖z‖ ^ 2)
      (PhysicalReferenceCoulombEquiv.radiation_equiv (N := N) c hc u)
  have hcov (q : Fin N × Fin 3) :
      ‖covariant (Fin N × Fin 3) Vc C κP hκP M hbP e q w‖ ^ 2 = ‖d q‖ ^ 2 :=
    congrArg (fun z : WaveSpace (Fin N × Fin 3) => ‖z‖ ^ 2)
      (PhysicalReferenceCoulombEquiv.covariant_equiv (N := N) C κP hκP M hbP c hc e u q)
  have hpot : ‖potential (Fin N × Fin 3) Vc w‖ ^ 2 = ∫ X, Vc X * ‖ψ X‖ ^ 2 :=
    (potential_norm_sq Vc (fun X => mul_nonneg hc (PhysicalCoulombH1.potential_nonneg N X)) w).trans
      (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ∫ X, Vc X * ‖z X‖ ^ 2)
        (PhysicalReferenceCoulombEquiv.inclusion_equiv (N := N) c hc u))
  have hpotint : Integrable (fun X => Vc X * ‖ψ X‖ ^ 2) volume :=
    (congrArg (fun z : WaveSpace (Fin N × Fin 3) =>
      Integrable (fun X => Vc X * ‖z X‖ ^ 2) volume)
      (PhysicalReferenceCoulombEquiv.inclusion_equiv (N := N) c hc u)).mp
        (potential_integrable Vc
          (fun X => mul_nonneg hc (PhysicalCoulombH1.potential_nonneg N X)) w)
  have hscalarint : (∫ X, scalar v c X * ‖ψ X‖ ^ 2) = scalarSum (N := N) v u +
      ∫ X, Vc X * ‖ψ X‖ ^ 2 := by
    unfold scalarSum
    change (∫ X, ((∑ n : Fin N, CoordinateSobolev.coordinateCoefficient n
      (v.val : PhysicalSourceCoordinates.Position → ℝ) X) + Vc X) * ‖ψ X‖ ^ 2) = _
    simp_rw [add_mul, Finset.sum_mul]
    exact (integral_add (integrable_finsetSum _ (fun n _ => scalar_integrable v n u)) hpotint).trans
      (congrArg (fun r : ℝ => r + ∫ X, Vc X * ‖ψ X‖ ^ 2)
        (integral_finsetSum _ (fun n _ => scalar_integrable v n u)))
  unfold externalEnergy energy kineticEnergy magneticSum squareSum
  exact energy_accounting
    (fun q : Fin N × Fin 3 => ‖externalCovariant (I := Fin N × Fin 3) (fun _ => 0)
      C κP hκP M hbP e (vector A) (positive v c) (negative v c) u D q‖ ^ 2)
    (fun q : Fin N × Fin 3 => ‖d q‖ ^ 2)
    (fun q : Fin N × Fin 3 => ‖covariant (Fin N × Fin 3) Vc C κP hκP M hbP e q w‖ ^ 2)
    (fun q : Fin N × Fin 3 => ∫ X, vector A q X * (⟪ψ X, d q X⟫_ℂ).re)
    (fun q : Fin N × Fin 3 => ∫ X, vector A q X ^ 2 * ‖ψ X‖ ^ 2)
    (‖radiation (Fin N × Fin 3) (fun _ => 0) u‖ ^ 2)
    (‖radiation (Fin N × Fin 3) Vc w‖ ^ 2)
    (‖potential (Fin N × Fin 3) (fun _ => 0) u‖ ^ 2)
    (‖potential (Fin N × Fin 3) Vc w‖ ^ 2) (∫ X, Vc X * ‖ψ X‖ ^ 2)
    (‖roughMultiply (positive v c) ψ D.positive‖ ^ 2)
    (‖roughMultiply (negative v c) ψ D.negative‖ ^ 2) (scalarSum (N := N) v u)
    hterm hcov hrad hpot0 hpot (hscalar.trans hscalarint)

attribute [local irreducible] PhysicalPFParticle.pair PhysicalPairDuality.pairing

set_option backward.isDefEq.respectTransparency.types false in
theorem pairing_scalar (i : Fin N) (v : ScalarPotential)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    scalarPairing v (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u) =
      scalarSum (N := N) v u := by
  have hp := PhysicalParticleFubini.density (N := N) C K hK M hM (fun _ => 0)
    i e u hu (v.val : PhysicalPairSpace.Position → ℝ) (fun n => scalar_integrable v n u)
  have hright : (∫ X, (∑ n, v.val (particle X n)) *
      ‖inclusion (Fin N × Fin 3) (fun _ => 0) u X‖ ^ 2) = scalarSum (N := N) v u := by
    unfold scalarSum
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum _ (fun n _ => scalar_integrable v n u)
  exact (scalarPairing_eq_integral v
    (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u)).trans (hp.trans hright)

set_option backward.isDefEq.respectTransparency.types false in
theorem pairing_vector (i : Fin N) (A : VectorPotential)
    (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hu : inclusion (Fin N × Fin 3) (fun _ => 0) u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    vectorPairing A (PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u) =
      magneticSum (N := N) C K hK M hM e A u := by
  let ψ : WaveSpace (Fin N × Fin 3) := inclusion (Fin N × Fin 3) (fun _ => 0) u
  let d : (Fin N × Fin 3) → WaveSpace (Fin N × Fin 3) := fun j =>
    covariant (Fin N × Fin 3) (fun _ => 0) C κP hκP M hbP e j u
  let P : PhysicalPairSpace.Pair := PhysicalPFParticle.pair (N := N) C K hK M hM (fun _ => 0) i e u
  have hrow (b : Fin 3) : (∫ x, A.val x b * currentL1 P x b) =
      ∑ n : Fin N, ∫ X, vector A (n, b) X * (⟪ψ X, d (n, b) X⟫_ℂ).re := by
    have hp := PhysicalParticleFubini.current (N := N) C K hK M hM (fun _ => 0)
      i e u hu b (fun x => A.val x b)
      (fun n => magnetic_integrable C K hK M hM e A (n, b) u)
    exact hp.trans (integral_finsetSum _
      (fun n _ => magnetic_integrable C K hK M hM e A (n, b) u))
  exact (vectorPairing_eq_sum_integrals A P).trans
    ((Finset.sum_congr rfl (fun b _ => hrow b)).trans (by
      unfold magneticSum
      exact sum_components (fun q : Fin N × Fin 3 =>
        ∫ X, vector A q X * (⟪ψ X, d q X⟫_ℂ).re)))


end PfHk.PhysicalShiftedFormEnergy

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
