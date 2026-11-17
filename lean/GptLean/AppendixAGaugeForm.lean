import GptLean.AppendixAGaugePotential
import GptLean.TransformationsClosedForm

/-! Gauge invariance of the external energy on the common form domain.
The vector potential is allowed to have L3 and Linfinity parts. -/

noncomputable section

namespace GptLean.TransformationsGauge

open MeasureTheory PhysicalPairSpace PhysicalPairDuality PhysicalFock PhysicalPFReference
  SymmetricLift
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 800000

/-- Every component of an article vector potential has the required sum regularity. -/
theorem vectorPotential_component_in_sum (A : VectorPotential) (a : Fin 3) :
    InLpThreeAddTop (fun x => A.val x a) := by
  refine ⟨fun x => (parts A).2 x a, fun x => (parts A).1 x a,
    (Lp.memLp (parts A).2).eval_piLp a, (Lp.memLp (parts A).1).eval_piLp a, ?_⟩
  filter_upwards [TransformationsPotentials.coeFn_parts A] with x hx
  rw [hx, PiLp.add_apply, add_comm]

/-- The ordinary external quadratic energy, including the diamagnetic term. -/
def externalEnergy (v : ScalarPotential) (A : Fin 3 → PhysicalPairSpace.Position → ℝ)
    (internal : ℝ) (p : Pair) : ℝ :=
  internal + pairing v p.1 + vectorEnergy A p

namespace WeakSpatialGauge

variable (g : WeakSpatialGauge)

theorem density_shiftPair (p : Pair) : (g.shiftPair p).1 = p.1 := by
  exact PhysicalPairSpace.fst_injective (g.densityL1_shiftPair p)

/-- The external energy is invariant under the simultaneous gauge transformation. -/
theorem externalEnergy_shift (v : ScalarPotential)
    (A : Fin 3 → PhysicalPairSpace.Position → ℝ)
    (hA : ∀ a, InLpThreeAddTop (A a)) (E : ℝ) (p : Pair) :
    externalEnergy v (fun a x => A a x - g.gradient a x)
      (E + g.energyShift p) (g.shiftPair p) = externalEnergy v A E p := by
  unfold externalEnergy
  rw [g.density_shiftPair]
  have h := g.vectorEnergy_gauge A hA p
  linarith

variable {N : ℕ} (V : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ)
  (C : CanonicalSectorCCR photonMeasure)
  (K : Fin 3 × Gaussian.FieldSpace → WeightedPhotonKernel) (hK : Continuous K)
  (M : ℝ) (hM : ∀ z, ‖K z‖ ≤ M) (e : ℝ) (i : Fin N)

set_option hygiene false in
local notation "κP" => PhysicalPFParticle.particleKernel (N := N) K
set_option hygiene false in
local notation "hκP" => PhysicalPFParticle.particleKernel_measurable (N := N) K hK
set_option hygiene false in
local notation "hbP" => PhysicalPFParticle.particleKernel_bound (N := N) K M hM

/-- The full weak gauge preserves the actual closed internal form domain in both directions. -/
theorem mem_domain_gauge (w : WaveSpace (Fin N × Fin 3)) :
    g.wavePhase w ∈ (energyOperator (Fin N × Fin 3) V C κP hκP M hbP e).domain ↔
      w ∈ (energyOperator (Fin N × Fin 3) V C κP hκP M hbP e).domain :=
  TransformationsClosedForm.mem_domain_transport V C κP hκP M hbP e κP hκP M hbP e
    g.wavePhase g.neg.wavePhase g.wavePhase_neg
    (fun u => ⟨g.gaugeReference V u, g.inclusion_gaugeReference V u⟩)
    (fun u => ⟨g.neg.gaugeReference V u, g.neg.inclusion_gaugeReference V u⟩) w

/-- `H-gauge` on quadratic energies for every article scalar and vector potential. -/
theorem externalEnergy_gauge (v : ScalarPotential) (A : VectorPotential)
    (u : Reference (Fin N × Fin 3) V)
    (hu : inclusion (Fin N × Fin 3) V u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock) :
    externalEnergy v (fun a x => A.val x a - g.gradient a x)
      (energy (Fin N × Fin 3) V C κP hκP M hbP e (g.gaugeReference V u))
      (PhysicalPFParticle.pair C K hK M hM V i e (g.gaugeReference V u)) =
    externalEnergy v (fun a x => A.val x a)
      (energy (Fin N × Fin 3) V C κP hκP M hbP e u)
      (PhysicalPFParticle.pair C K hK M hM V i e u) := by
  rw [g.pair_gauge V C K hK M hM e i u, g.energy_gauge V C K hK M hM e i u hu]
  exact g.externalEnergy_shift v (fun a x => A.val x a)
    (vectorPotential_component_in_sum A) _ _

end WeakSpatialGauge

end GptLean.TransformationsGauge
