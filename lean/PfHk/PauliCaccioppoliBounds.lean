import PfHk.PauliPhysicalFormBounds
import PfHk.PauliGroundState
import PfHk.PauliLocalEnergy
import PfHk.PhysicalLocalEnergyCutoff

/-! Physical spin sums and recovery of the full external covariant energy
from the ordinary and radiation form energies. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCaccioppoli

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant externalCovariant roughMultiply

def massOn (s : Set (Configuration N)) (u : Ref N) : ℝ :=
  ∫ X in s, ‖PauliReference.wave u X‖ ^ 2

theorem massOn_nonneg (s : Set (Configuration N)) (u : Ref N) : 0 ≤ massOn s u :=
  integral_nonneg fun _ => sq_nonneg _

theorem massOn_eq_sum (s : Set (Configuration N)) (u : Ref N) :
    massOn s u = ∑ t, PhysicalLocalEnergy.massOn s
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)) := by
  unfold massOn PhysicalLocalEnergy.massOn
  calc
    _ = ∫ X in s, ∑ t, ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u t) X‖ ^ 2 :=
      integral_congr_ae (ae_restrict_of_ae (PauliReference.wave_norm_sq_ae u))
    _ = _ := integral_finsetSum _ (fun t _ =>
      (Lp.memLp (inclusion (Fin N × Fin 3) (fun _ => 0) (u t))).norm.integrable_sq.integrableOn)

theorem component_mass_le (s : Set (Configuration N)) (u : Ref N) (t : SpinIndex N) :
    PhysicalLocalEnergy.massOn s (inclusion (Fin N × Fin 3) (fun _ => 0) (u t)) ≤
      massOn s u := by
  exact (Finset.single_le_sum
    (f := fun j : SpinIndex N => PhysicalLocalEnergy.massOn s
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u j)))
    (fun j _ => PhysicalLocalEnergy.massOn_nonneg s _) (Finset.mem_univ t)).trans_eq
      (massOn_eq_sum s u).symm

private theorem norm_three_covariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p f av : H) (e : ℝ) :
    ‖(-Complex.I) • p + -((e : ℂ) • f) + av‖ ^ 2 ≤
      3 * ‖p‖ ^ 2 + 3 * e ^ 2 * ‖f‖ ^ 2 + 3 * ‖av‖ ^ 2 := by
  have h := PauliContractionBounds.three_square_bound ((-Complex.I) • p) (-((e : ℂ) • f)) av
  simp only [norm_neg, norm_smul, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, mul_pow, sq_abs, one_mul] at h
  nlinarith only [h]

private theorem sub_add_eq {H : Type*} [AddCommGroup H] (a b c : H) :
    a - b + c = a + -b + c := by simp only [sub_eq_add_neg]

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

def covariantEnergy (u : Ref N) : ℝ :=
  ∑ q : Fin N × Fin 3, ∑ s, ‖rawCovariant C κ hκ M hκbound e
    (vector A) (positive v c) (negative v c) u (physicalDomain A v c hc u) q s‖ ^ 2

theorem covariantEnergy_nonneg (u : Ref N) :
    0 ≤ covariantEnergy C κ hκ M hκbound e A v c hc u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem covariant_three (u : Ref N) (q : Fin N × Fin 3) (s : SpinIndex N) :
    ‖rawCovariant C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      u (physicalDomain A v c hc u) q s‖ ^ 2 ≤
      3 * ‖ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)‖ ^ 2 +
      3 * e ^ 2 * ‖field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound q (u s)‖ ^ 2 +
      3 * ‖roughMultiply (vector A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
        ((physicalDomain A v c hc u s).vector q)‖ ^ 2 := by
  let p := ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)
  let f := field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound q (u s)
  let av := roughMultiply (vector A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    ((physicalDomain A v c hc u s).vector q)
  have he : rawCovariant C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      u (physicalDomain A v c hc u) q s = (-Complex.I) • p + -((e : ℂ) • f) + av := by
    unfold rawCovariant externalCovariant
    exact (congrArg (fun z : WaveSpace (Fin N × Fin 3) => z + av)
      (covariant_apply (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound e q (u s))).trans
      (sub_add_eq _ _ _)
  exact (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ‖z‖ ^ 2) he).le.trans
    (norm_three_covariant p f av e)

theorem covariant_bound_raw (u : Ref N) :
    covariantEnergy C κ hκ M hκbound e A v c hc u ≤
      3 * ordinaryEnergy u + 3 * e ^ 2 * fieldEnergy C κ hκ M hκbound u +
      3 * vectorEnergy (vector A) (positive v c) (negative v c) u
        (physicalDomain A v c hc u) := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun q _ =>
    Finset.sum_le_sum (s := Finset.univ) fun s _ => covariant_three C κ hκ M hκbound e A v c hc u q s
  simpa only [covariantEnergy, ordinaryEnergy, fieldEnergy, vectorEnergy,
    Finset.sum_add_distrib, ← Finset.mul_sum] using h

def covariantRecovery : ℝ :=
  let k := PauliPhysicalFormBounds.constants (N := N) A v c hc e M
  3 + 3 * (Fintype.card (Fin N × Fin 3) : ℝ) * k.vectorRate +
    24 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2

def covariantMass : ℝ :=
  let k := PauliPhysicalFormBounds.constants (N := N) A v c hc e M
  6 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 +
    3 * (Fintype.card (Fin N × Fin 3) : ℝ) * k.vectorMass

theorem covariantRecovery_nonneg : 0 ≤ covariantRecovery (N := N) M e A v c hc := by
  have h := (PauliPhysicalFormBounds.constants (N := N) A v c hc e M).vectorRate_pos.le
  unfold covariantRecovery
  positivity

theorem covariantMass_nonneg : 0 ≤ covariantMass (N := N) M e A v c hc := by
  have h := (PauliPhysicalFormBounds.constants (N := N) A v c hc e M).vectorMass_nonneg
  unfold covariantMass
  positivity

private theorem combine_covariant {Q O R m F V a d ε C₀ e : ℝ}
    (hO : 0 ≤ O) (hR : 0 ≤ R) (ha : 0 ≤ a) (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hQ : Q ≤ 3 * O + 3 * e ^ 2 * F + 3 * V)
    (hF : F ≤ 8 * d * a * R + 2 * d * a * m)
    (hV : V ≤ d * ε * O + d * C₀ * m) :
    Q ≤ (3 + 3 * d * ε + 24 * e ^ 2 * d * a) * (O + R) +
      (6 * e ^ 2 * d * a + 3 * d * C₀) * m := by
  have hm := mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ 3 * e ^ 2)
  have hvo := mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 3)
  have h₁ : 0 ≤ (3 + 3 * d * ε) * R := mul_nonneg (by positivity) hR
  have h₂ : 0 ≤ (24 * e ^ 2 * d * a) * O := mul_nonneg (by positivity) hO
  nlinarith only [hQ, hm, hvo, h₁, h₂]

theorem covariant_bound (u : Ref N) :
    covariantEnergy C κ hκ M hκbound e A v c hc u ≤
      covariantRecovery (N := N) M e A v c hc * (ordinaryEnergy u + radiationEnergy u) +
      covariantMass (N := N) M e A v c hc * normSquared u := by
  let k := PauliPhysicalFormBounds.constants (N := N) A v c hc e M
  exact combine_covariant (ordinaryEnergy_nonneg u) (radiationEnergy_nonneg u)
    (sq_nonneg (max M 0)) k.vectorRate_pos.le (Nat.cast_nonneg _)
    (covariant_bound_raw C κ hκ M hκbound e A v c hc u)
    (field_bound C κ hκ M hκbound u)
    (vector_bound (vector A) (positive v c) (negative v c) k.vectorRate k.vectorMass
      k.vectorRate_pos.le k.vector_bound u (physicalDomain A v c hc u))

end PfHk.PauliCaccioppoli

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
