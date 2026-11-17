import GptLean.PhysicalFockCreation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Concrete finite creation words in the symmetric L² Fock model.

The vacuum is the constant unit vector in the zero-photon product measure.
Each word uses the already constructed normalized symmetric insertion and
is placed in its actual number sector. These vectors specify the model
matching required of the universal Fock exponential law.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

instance zeroSectorProbability : IsProbabilityMeasure (SectorMeasure μ 0) :=
  ⟨Measure.pi_empty_univ _⟩

def vacuumWaveFunction : FullSector μ 0 := Lp.const 2 (SectorMeasure μ 0) (1 : ℂ)

omit [SigmaFinite μ] in
theorem vacuumWaveFunction_ae : vacuumWaveFunction μ =ᵐ[SectorMeasure μ 0] fun _ => (1 : ℂ) :=
  Lp.coeFn_const _ _ _

theorem vacuumWaveFunction_symmetric : vacuumWaveFunction μ ∈ symmetricSubspace μ 0 := by
  intro π
  apply Lp.ext
  have hp := measurePreserving_piCongrLeft (fun _ : Fin 0 => μ) π
  filter_upwards [permutation_ae μ 0 π (vacuumWaveFunction μ),
    hp.quasiMeasurePreserving.ae (vacuumWaveFunction_ae μ), vacuumWaveFunction_ae μ]
    with k hk hp hv
  exact hk.trans (hp.trans hv.symm)

def vacuumSector : Sector μ 0 := ⟨vacuumWaveFunction μ, vacuumWaveFunction_symmetric μ⟩

theorem vacuumSector_norm : ‖vacuumSector μ‖ = 1 := by
  change ‖Lp.const 2 (SectorMeasure μ 0) (1 : ℂ)‖ = 1
  rw [Lp.norm_const' _ _ _ (by norm_num) (by norm_num)]
  simp

/-- Ordered products of actual creation operators applied to the actual vacuum. -/
def creationWordSector : (w : List (Lp ℂ 2 μ)) → Sector μ w.length
  | [] => vacuumSector μ
  | f :: w => creationSector μ w.length f (creationWordSector w)

def creationWord (w : List (Lp ℂ 2 μ)) : Fock μ :=
  lp.single 2 w.length (creationWordSector μ w)

@[simp] theorem creationWord_nil : creationWord μ [] = lp.single 2 0 (vacuumSector μ) := rfl

theorem creationWord_norm (w : List (Lp ℂ 2 μ)) :
    ‖creationWord μ w‖ = ‖creationWordSector μ w‖ := lp.norm_single (by norm_num) _ _

theorem vacuum_norm : ‖creationWord μ []‖ = 1 := by rw [creationWord_norm, creationWordSector, vacuumSector_norm]

theorem creationWord_number (w : List (Lp ℂ 2 μ)) :
    photonNumberForm μ (creationWord μ w) =
      ENNReal.ofReal ((w.length : ℝ) * ‖creationWord μ w‖ ^ 2) := by
  have h := photonNumber_sector μ w.length (creationWord μ w)
  have he : photonSector μ w.length (creationWord μ w) = creationWord μ w := by
    change lp.single 2 w.length ((lp.single 2 w.length (creationWordSector μ w)) w.length) = _
    rw [lp.single_apply_self]
    rfl
  simpa only [he] using h

end GptLean.PhysicalFock
