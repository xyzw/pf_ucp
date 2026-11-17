import GptLean.PhysicalPFSource
import GptLean.PhysicalLpUpgrade
import GptLean.PhysicalPairBilinear
import GptLean.PhysicalEnsembleTests
import GptLean.PhysicalPairSpatialTests

/-!
The actual density-current pair series converges in the article's full
Banach space. The L6 source map is bounded by the closed-graph theorem,
and Holder makes the pair a bounded bilinear expression in the common
reference vector. The limit is identified using the proved source tests.
Consequently every potential in the actual sum-Lp dual has the correct
spectral series without a separate potential regularizer assumption.
-/

noncomputable section

namespace GptLean.PhysicalPFPairSeries

open MeasureTheory PhysicalFock PhysicalPFReference PhysicalNormalTrace PhysicalClosedForms
  PhysicalPFSource PhysicalSourceMarginal PhysicalSourceCoordinates PhysicalPairSpace
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 400000

private theorem generic_pair_diagonal {Q H : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [InnerProductSpace ℂ H]
    (N : ℕ) (L₂ : Q →L[ℝ] Lp H 2 (volume : Measure PhysicalPairSpace.Position))
    (L₆ : Q →L[ℝ] Lp H 6 (volume : Measure PhysicalPairSpace.Position))
    (hL : ∀ u, (L₂ u : PhysicalPairSpace.Position → H) =ᵐ[volume] L₆ u)
    (D : Fin 3 → Q →L[ℝ] Lp H 2 (volume : Measure PhysicalPairSpace.Position))
    (h₆ : ∀ u, MemLp (L₂ u) 6 volume)
    (hinner : ∀ v w : H, inner ℝ v w = (inner ℂ v w).re) (u : Q) :
    PhysicalPairBilinear.form N L₂ L₆ hL D u u =
      PhysicalPairRealization.ofSource N (L₂ u) (fun a => D a u)
        (Lp.memLp _) (h₆ u) (fun _ => Lp.memLp _) := by
  apply pair_ext_ae
  · filter_upwards [PhysicalPairBilinear.density_form_ae N L₂ L₆ hL D u u,
      PhysicalPairRealization.density_ofSource_ae N (L₂ u) (fun a => D a u)
        (Lp.memLp _) (h₆ u) (fun _ => Lp.memLp _)] with x h₁ h₂
    exact h₁.trans ((congrArg ((N : ℝ) * ·)
      (real_inner_self_eq_norm_sq (L₂ u x))).trans h₂.symm)
  · filter_upwards [PhysicalPairBilinear.current_form_ae N L₂ L₆ hL D u u,
      PhysicalPairRealization.current_ofSource_ae N (L₂ u) (fun a => D a u)
        (Lp.memLp _) (h₆ u) (fun _ => Lp.memLp _)] with x h₁ h₂
    apply h₁.trans
    apply Eq.trans _ h₂.symm
    ext a
    exact congrArg ((N : ℝ) * ·) (hinner (L₂ u x) (D a u x))

private theorem generic_summable_diagonal {Q Y : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : Q →L[ℝ] Q →L[ℝ] Y) (u : ℕ → Q)
    (hu : Summable (fun n => ‖u n‖ ^ 2)) : Summable (fun n => A (u n) (u n)) := by
  apply (hu.mul_left ‖A‖).of_norm_bounded
  intro n
  exact (A.le_opNorm₂ (u n) (u n)).trans_eq (by ring)

private def generic_upgrade {Q H : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (L : Q →L[ℝ] Lp H 2 (volume : Measure PhysicalPairSpace.Position))
    (hm : ∀ u, MemLp (L u) 6 volume) :
    {K : Q →L[ℝ] Lp H 6 (volume : Measure PhysicalPairSpace.Position) //
      ∀ u, (L u : PhysicalPairSpace.Position → H) =ᵐ[volume] K u} :=
  ⟨PhysicalLpUpgrade.map L hm,
    fun u => (PhysicalLpUpgrade.map_ae L hm u).symm⟩

abbrev Index (N : ℕ) := Fin N × Fin 3
abbrev Fiber {N : ℕ} (i : Fin N) := Lp PhotonFock 2 (volume : Measure (Spectator i))

local instance fiberRealInner {N : ℕ} (i : Fin N) : InnerProductSpace ℝ (Fiber i) :=
  InnerProductSpace.rclikeToReal ℂ (Fiber i)

local instance fiberRealSpace {N : ℕ} (i : Fin N) : NormedSpace ℝ (Fiber i) :=
  (fiberRealInner i).toNormedSpace

local instance fiberRealModule {N : ℕ} (i : Fin N) : Module ℝ (Fiber i) :=
  (fiberRealSpace i).toModule

local instance fiberRealSMul {N : ℕ} (i : Fin N) : SMul ℝ (Fiber i) :=
  (fiberRealModule i).toSMul

local instance fiberRealTower {N : ℕ} (i : Fin N) : IsScalarTower ℝ ℂ (Fiber i) :=
  IsScalarTower.restrictScalars ℝ ℂ (Fiber i)

local instance referenceComplexModule {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    Module ℂ (Reference (Index N) V) :=
  (referenceNormedSpace (Index N) V).toModule

local instance referenceComplexSMul {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    SMul ℂ (Reference (Index N) V) :=
  (referenceComplexModule V).toSMul

local instance referenceRealSpace {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    NormedSpace ℝ (Reference (Index N) V) :=
  NormedSpace.restrictScalars ℝ ℂ (Reference (Index N) V)

local instance referenceRealModule {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    Module ℝ (Reference (Index N) V) :=
  (referenceRealSpace V).toModule

local instance referenceRealSMul {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    SMul ℝ (Reference (Index N) V) :=
  (referenceRealModule V).toSMul

local instance referenceRealTower {N : ℕ}
    (V : PhysicalPFReference.Position (Index N) → ℝ) :
    IsScalarTower ℝ ℂ (Reference (Index N) V) :=
  IsScalarTower.restrictScalars ℝ ℂ (Reference (Index N) V)

variable {N : ℕ} (i : Fin N) (V : PhysicalPFReference.Position (Index N) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (κ : Index N → PhysicalPFReference.Position (Index N) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hbound : ∀ q, ∀ᵐ x ∂volume, ‖κ q x‖ ≤ M)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground) (e : ℝ)

def sourceTwo : Reference (Index N) V →L[ℝ]
    Lp (Fiber i) 2 (volume : Measure PhysicalPairSpace.Position) :=
  ((particleMap i).toContinuousLinearMap.comp (inclusion (Index N) V)).restrictScalars ℝ

theorem sourceTwo_six (u : Reference (Index N) V) :
    MemLp (sourceTwo i V u) 6 volume :=
  particleSource_memLp_six i (ElectronicH1Complex.realEquiv (electronic (Index N) V u))

attribute [local irreducible] sourceTwo

set_option backward.isDefEq.respectTransparency.types false in
private def sourceSixData :
    {K : Reference (Index N) V →L[ℝ]
      Lp (Fiber i) 6 (volume : Measure PhysicalPairSpace.Position) //
      ∀ u, (sourceTwo i V u : PhysicalPairSpace.Position → Fiber i) =ᵐ[volume] K u} :=
  generic_upgrade (Q := Reference (Index N) V) (H := Fiber i)
    (sourceTwo i V) (sourceTwo_six i V)

attribute [local irreducible] sourceSixData

def sourceSix : Reference (Index N) V →L[ℝ]
    Lp (Fiber i) 6 (volume : Measure PhysicalPairSpace.Position) :=
  (sourceSixData i V).val

theorem source_compatible (u : Reference (Index N) V) :
    (sourceTwo i V u : PhysicalPairSpace.Position → Fiber i) =ᵐ[volume] sourceSix i V u :=
  (sourceSixData i V).property u

def covariantSource (a : Fin 3) : Reference (Index N) V →L[ℝ]
    Lp (Fiber i) 2 (volume : Measure PhysicalPairSpace.Position) :=
  ((particleMap i).toContinuousLinearMap.comp
    (covariant (Index N) V C κ hκ M hbound e (i, a))).restrictScalars ℝ

attribute [local irreducible] covariantSource

def pairForm : Reference (Index N) V →L[ℝ] Reference (Index N) V →L[ℝ] Pair :=
  PhysicalPairBilinear.form (Q := Reference (Index N) V) (H := Fiber i)
    N (sourceTwo i V) (sourceSix i V) (source_compatible i V)
    (covariantSource i V C κ hκ M hbound e)

attribute [local irreducible] PhysicalPairBilinear.form

def vectorPair (u : Reference (Index N) V) : Pair :=
  PhysicalSourcePair.ofWaveFunction i
    (ElectronicH1Complex.realEquiv (electronic (Index N) V u))
    (fun a => covariant (Index N) V C κ hκ M hbound e (i, a) u)

theorem vectorPair_eq_source (u : Reference (Index N) V) :
    vectorPair i V C κ hκ M hbound e u =
      PhysicalPairRealization.ofSource N (sourceTwo i V u)
        (fun a => covariantSource i V C κ hκ M hbound e a u)
        (Lp.memLp _) (sourceTwo_six i V u) (fun _ => Lp.memLp _) := by
  simp only [vectorPair, PhysicalSourcePair.ofWaveFunction, sourceTwo,
    covariantSource, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    inclusion]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem pairForm_diagonal (u : Reference (Index N) V) :
    pairForm i V C κ hκ M hbound e u u = vectorPair i V C κ hκ M hbound e u := by
  have hdiag := @generic_pair_diagonal (Reference (Index N) V) (Fiber i)
    (inferInstance : NormedAddCommGroup (Reference (Index N) V))
    (referenceRealSpace V) (inferInstance : NormedAddCommGroup (Fiber i))
    (fiberRealInner i) (inferInstance : InnerProductSpace ℂ (Fiber i))
    N (sourceTwo i V) (sourceSix i V) (source_compatible i V)
    (covariantSource i V C κ hκ M hbound e) (sourceTwo_six i V)
    (fun _ _ => rfl) u
  exact hdiag.trans (vectorPair_eq_source i V C κ hκ M hbound e u).symm

variable {B}

theorem summable_vectorPair {x : B.Trace (WaveSpace (Index N))}
    (s : Source (Index N) V B x)
    (he : (normalEnergy (Index N) V C κ hκ M hbound B S e).expectation x < ⊤) :
    Summable (fun n => vectorPair i V C κ hκ M hbound e (s.vector n)) := by
  have h := generic_summable_diagonal (pairForm i V C κ hκ M hbound e) s.vector
    (s.reference_summable C κ hκ M hbound S e he)
  exact h.congr (fun n => pairForm_diagonal i V C κ hκ M hbound e (s.vector n))

theorem vectorPair_hasSum {x : B.Trace (WaveSpace (Index N))}
    (s : Source (Index N) V B x)
    (he : (normalEnergy (Index N) V C κ hκ M hbound B S e).expectation x < ⊤) :
    HasSum (fun n => vectorPair i V C κ hκ M hbound e (s.vector n))
      (s.pair C M S e i V κ hκ hbound he) := by
  have hs := summable_vectorPair i V C κ hκ M hbound S e s he
  suffices h : (∑' n, vectorPair i V C κ hκ M hbound e (s.vector n)) =
      s.pair C M S e i V κ hκ hbound he by
    exact h ▸ hs.hasSum
  apply pair_eq_of_spatial_test_maps
  · intro t
    have hterm (n : ℕ) : spatialDensityTest t
        (vectorPair i V C κ hκ M hbound e (s.vector n)) =
          (N : ℝ) * ∫ z, t.weight ((split i) z).1 *
            ‖inclusion (Index N) V (s.vector n) z‖ ^ 2 :=
      (spatialDensityTest_eq t _).trans
        (PhysicalSourcePair.tested_density_ofWaveFunction i
          (ElectronicH1Complex.realEquiv (electronic (Index N) V (s.vector n)))
          (fun a => covariant (Index N) V C κ hκ M hbound e (i, a) (s.vector n))
          t.weight t.measurable (ae_of_all _ t.bounded))
    have htotal := PhysicalSourcePair.tested_density_ofEnsemble i
      (fun n => ElectronicH1Complex.realEquiv (electronic (Index N) V (s.vector n)))
      s.mass_hasSum.summable
      (fun b => s.operator_summable C κ hκ M hbound S e he (ordinary (Index N) V b))
      (fun a n => covariant (Index N) V C κ hκ M hbound e (i, a) (s.vector n))
      (fun a => s.operator_summable C κ hκ M hbound S e he
        (covariant (Index N) V C κ hκ M hbound e (i, a)))
      t.weight t.measurable (ae_of_all _ t.bounded)
    calc
      _ = ∑' n, spatialDensityTest t
          (vectorPair i V C κ hκ M hbound e (s.vector n)) :=
        (spatialDensityTest t).map_tsum hs
      _ = (N : ℝ) * ∑' n, ∫ z, t.weight ((split i) z).1 *
          ‖inclusion (Index N) V (s.vector n) z‖ ^ 2 := by
        simp only [hterm, tsum_mul_left]
      _ = _ := htotal.symm.trans (spatialDensityTest_eq t _).symm
  · intro b t
    have hterm (n : ℕ) : spatialCurrentTest b t
        (vectorPair i V C κ hκ M hbound e (s.vector n)) =
          (N : ℝ) * ∫ z, t.weight ((split i) z).1 *
            (inner ℂ (inclusion (Index N) V (s.vector n) z)
              (covariant (Index N) V C κ hκ M hbound e (i, b) (s.vector n) z)).re :=
      (spatialCurrentTest_eq b t _).trans
        (PhysicalSourcePair.tested_current_ofWaveFunction i
          (ElectronicH1Complex.realEquiv (electronic (Index N) V (s.vector n)))
          (fun a => covariant (Index N) V C κ hκ M hbound e (i, a) (s.vector n)) b
          t.weight t.measurable (ae_of_all _ t.bounded))
    have htotal := PhysicalSourcePair.tested_current_ofEnsemble i
      (fun n => ElectronicH1Complex.realEquiv (electronic (Index N) V (s.vector n)))
      s.mass_hasSum.summable
      (fun a => s.operator_summable C κ hκ M hbound S e he (ordinary (Index N) V a))
      (fun a n => covariant (Index N) V C κ hκ M hbound e (i, a) (s.vector n))
      (fun a => s.operator_summable C κ hκ M hbound S e he
        (covariant (Index N) V C κ hκ M hbound e (i, a))) b
      t.weight t.measurable (ae_of_all _ t.bounded)
    calc
      _ = ∑' n, spatialCurrentTest b t
          (vectorPair i V C κ hκ M hbound e (s.vector n)) :=
        (spatialCurrentTest b t).map_tsum hs
      _ = (N : ℝ) * ∑' n, ∫ z, t.weight ((split i) z).1 *
          (inner ℂ (inclusion (Index N) V (s.vector n) z)
            (covariant (Index N) V C κ hκ M hbound e (i, b) (s.vector n) z)).re := by
        simp only [hterm, tsum_mul_left]
      _ = _ := htotal.symm.trans (spatialCurrentTest_eq b t _).symm

theorem potential_hasSum {x : B.Trace (WaveSpace (Index N))}
    (s : Source (Index N) V B x)
    (he : (normalEnergy (Index N) V C κ hκ M hbound B S e).expectation x < ⊤)
    (a : PhysicalPairDuality.Potential) :
    HasSum (fun n => PhysicalPairDuality.pairPotential a
      (vectorPair i V C κ hκ M hbound e (s.vector n)))
      (PhysicalPairDuality.pairPotential a (s.pair C M S e i V κ hκ hbound he)) :=
  (PhysicalPairDuality.pairPotential a).hasSum
    (vectorPair_hasSum i V C κ hκ M hbound S e s he)

end GptLean.PhysicalPFPairSeries
