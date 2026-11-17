import PfHk.PauliCaccioppoliBounds
import PfHk.PhysicalLocalEnergyBumps

/-! Caccioppoli estimates for the actual coupled Pauli weak equation.
Coercivity and the scalar cutoff error are applied before any continuation
argument. Every constant is derived from the physical coefficient classes. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliCaccioppoli

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.PhysicalPairDuality GptLean.SymmetricLift GptLean.ElectronicH1Multiplier
  PfHk.PhysicalLocalEnergy PfHk.PhysicalCommonFormDomain
  PfHk.PauliGroundState PfHk.PauliFormBounds PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

variable {N : ℕ}
attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant externalCovariant roughMultiply rawEnergy
  PhysicalPFScalarMultiplier.multiply

theorem cutoff_mass_bound {O : Configuration N} {r L : ℝ}
    (a : BallCutoff O r L) (u : Ref N) :
    normSquared (PauliLocalEnergy.localize a.multiplier u) ≤ massOn (Metric.ball O (2*r)) u := by
  unfold normSquared
  have h := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    (congrArg (fun z : WaveSpace (Fin N × Fin 3) => ‖z‖ ^ 2)
      (PhysicalPFScalarMultiplier.value_multiply (fun _ => 0) a.multiplier (u s))).le.trans
        (a.mass_bound _)
  exact h.trans_eq (massOn_eq_sum (Metric.ball O (2*r)) u).symm

private theorem sum_coordinate_bounds {S Q : Type*} [Fintype S] [Fintype Q]
    (f : Q → S → ℝ) (m : S → ℝ) (d L r : ℝ)
    (h : ∀ s, (∑ q, f q s) ≤ d * (L/r)^2 * m s) :
    (∑ q, ∑ s, f q s) ≤ d * (L/r)^2 * ∑ s, m s := by
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => h s

private theorem times_three (a b c : ℝ) : 3 * (a * b * c) = 3 * a * b * c := by ring

theorem cutoff_error_bound {O : Configuration N} {r L : ℝ}
    (a : BallCutoff O r L) (u : Ref N) :
    (∑ n, ∑ s, ‖PauliLocalEnergy.error a.multiplier u n s‖ ^ 2) ≤
      3 * (Fintype.card (Fin N × Fin 3) : ℝ) * (L / r) ^ 2 * massOn (Metric.ball O (2*r)) u := by
  have h₀ : (∑ n, ∑ s, ‖PauliLocalEnergy.error a.multiplier u n s‖ ^ 2) ≤
      3 * ∑ q : Fin N × Fin 3, ∑ s,
        ‖a.multiplier.derivativeMultiplier q (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))‖ ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) fun n _ =>
      PauliLocalEnergy.error_norm_sq_le a.multiplier u n
    simpa only [← Finset.mul_sum, Fintype.sum_prod_type] using hh
  have h₁ : (∑ q : Fin N × Fin 3, ∑ s,
      ‖a.multiplier.derivativeMultiplier q (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))‖ ^ 2) ≤
      (Fintype.card (Fin N × Fin 3) : ℝ) * (L / r) ^ 2 * massOn (Metric.ball O (2*r)) u := by
    have hh := sum_coordinate_bounds
      (fun q s => ‖a.multiplier.derivativeMultiplier q
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))‖ ^ 2)
      (fun s => PhysicalLocalEnergy.massOn (Metric.ball O (2*r))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)))
      (Fintype.card (Fin N × Fin 3)) L r (fun s => a.error_bound _)
    exact hh.trans_eq (congrArg
      (fun z : ℝ => (Fintype.card (Fin N × Fin 3) : ℝ) * (L/r)^2 * z)
      (massOn_eq_sum (Metric.ball O (2*r)) u).symm)
  exact h₀.trans ((mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
    (times_three _ _ _))

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Configuration N → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : VectorPotential) (v : ScalarPotential) (c : ℝ) (hc : 0 ≤ c)

def coercivityFactor : ℝ := 4 * (recoveryFactor N e M + 1)

theorem coercivityFactor_nonneg : 0 ≤ coercivityFactor (N := N) M e := by
  unfold coercivityFactor recoveryFactor
  positivity

def ordinaryConstant (E L : ℝ) : ℝ :=
  coercivityFactor (N := N) M e *
    (|E| + (3 / 2 : ℝ) * (Fintype.card (Fin N × Fin 3) : ℝ) * L ^ 2) +
      PauliPhysicalFormBounds.fullMass (N := N) A v c hc e M

theorem ordinaryConstant_nonneg (E L : ℝ) :
    0 ≤ ordinaryConstant (N := N) M e A v c hc E L :=
  add_nonneg (mul_nonneg (coercivityFactor_nonneg M e) (by positivity))
    (PauliPhysicalFormBounds.fullMass_nonneg M e A v c hc)

private theorem localized_scalar {O P R q m m₀ err F B E d L r : ℝ}
    (hP : 0 ≤ P) (hm : 0 ≤ m) (hm₀ : 0 ≤ m₀) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : O + P + R ≤ F * q + B * m)
    (hims : q = E * m + (1 / 2 : ℝ) * err)
    (hmass : m ≤ m₀) (herr : err ≤ 3 * d * (L / r) ^ 2 * m₀) :
    O + R ≤ (F * (|E| + (3 / 2 : ℝ) * d * L ^ 2) + B) / r ^ 2 * m₀ := by
  have hE := mul_le_mul_of_nonneg_right (le_abs_self E) hm
  have hc : 0 ≤ F * |E| + B := by positivity
  have hm' := mul_le_mul_of_nonneg_left hmass hc
  have he' := mul_le_mul_of_nonneg_left herr (show 0 ≤ F / 2 by positivity)
  have hscaled : (F * |E| + B) * m₀ ≤ (F * |E| + B) / r ^ 2 * m₀ := by
    apply mul_le_mul_of_nonneg_right _ hm₀
    exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      (mul_le_of_le_one_right hc (by nlinarith only [hr, hr1]))
  have hfe := mul_le_mul_of_nonneg_left hE hF
  have halg : (F * (|E| + (3 / 2 : ℝ) * d * L ^ 2) + B) / r ^ 2 * m₀ =
      (F * |E| + B) / r ^ 2 * m₀ + (F / 2) * (3 * d * (L / r) ^ 2 * m₀) := by
    field_simp
    ring
  rw [halg]
  rw [hims] at hbound
  nlinarith only [hP, hbound, hm', he', hscaled, hfe]

theorem localized_ordinary_radiation {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff O r L) :
    ordinaryEnergy (PauliLocalEnergy.localize a.multiplier u) +
      radiationEnergy (PauliLocalEnergy.localize a.multiplier u) ≤
      ordinaryConstant (N := N) M e A v c hc E L / r ^ 2 * massOn (Metric.ball O (2*r)) u := by
  let w := PauliLocalEnergy.localize a.multiplier u
  have hf := PauliPhysicalFormBounds.full_energy_bound C κ hκ M hκbound e A v c hc w
  have hi := PauliLocalEnergy.eigenstate_ims C κ hκ M hκbound e
    (vector A) (positive v c) (negative v c) a.multiplier u (physicalDomain A v c hc u) heigen
  exact localized_scalar
    (pauliEnergy_nonneg C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      w (physicalDomain A v c hc w))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (massOn_nonneg _ u)
    (coercivityFactor_nonneg M e) (PauliPhysicalFormBounds.fullMass_nonneg M e A v c hc)
    hr hr1 hf hi (cutoff_mass_bound a u) (cutoff_error_bound a u)

def caccioppoliConstant (E L : ℝ) : ℝ :=
  (covariantRecovery (N := N) M e A v c hc + 1) *
    ordinaryConstant (N := N) M e A v c hc E L + covariantMass (N := N) M e A v c hc

theorem caccioppoliConstant_nonneg (E L : ℝ) :
    0 ≤ caccioppoliConstant (N := N) M e A v c hc E L :=
  add_nonneg (mul_nonneg (add_nonneg (covariantRecovery_nonneg M e A v c hc) zero_le_one)
    (ordinaryConstant_nonneg M e A v c hc E L)) (covariantMass_nonneg M e A v c hc)

private theorem combined_scalar {O R Q K m m₀ a b r : ℝ}
    (hm₀ : 0 ≤ m₀) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) (hr1 : r ≤ 1)
    (hOR : O + R ≤ K / r ^ 2 * m₀) (hQ : Q ≤ a * (O + R) + b * m)
    (hm : m ≤ m₀) : O + Q + R ≤ ((a + 1) * K + b) / r ^ 2 * m₀ := by
  have h₁ := mul_le_mul_of_nonneg_left hOR ha
  have h₂ := mul_le_mul_of_nonneg_left hm hb
  have h₃ : b * m₀ ≤ b / r ^ 2 * m₀ := by
    apply mul_le_mul_of_nonneg_right _ hm₀
    exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      (mul_le_of_le_one_right hb (by nlinarith only [hr, hr1]))
  have he : ((a + 1) * K + b) / r ^ 2 * m₀ =
      (a + 1) * (K / r ^ 2 * m₀) + b / r ^ 2 * m₀ := by ring
  rw [he]
  linarith only [hOR, hQ, h₁, h₂, h₃]

theorem localized_full {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff O r L) :
    ordinaryEnergy (PauliLocalEnergy.localize a.multiplier u) +
      covariantEnergy C κ hκ M hκbound e A v c hc (PauliLocalEnergy.localize a.multiplier u) +
      radiationEnergy (PauliLocalEnergy.localize a.multiplier u) ≤
      caccioppoliConstant (N := N) M e A v c hc E L / r ^ 2 * massOn (Metric.ball O (2*r)) u :=
  combined_scalar (massOn_nonneg _ u) (covariantRecovery_nonneg M e A v c hc)
    (covariantMass_nonneg M e A v c hc) hr hr1
    (localized_ordinary_radiation C κ hκ M hκbound e A v c hc heigen hr hr1 a)
    (covariant_bound C κ hκ M hκbound e A v c hc (PauliLocalEnergy.localize a.multiplier u))
    (cutoff_mass_bound a u)

def ordinaryEnergyOn (s : Set (Configuration N)) (u : Ref N) : ℝ :=
  ∑ t, ∑ q, PhysicalLocalEnergy.massOn s (ordinary (Fin N × Fin 3) (fun _ => 0) q (u t))

def covariantEnergyOn (s : Set (Configuration N)) (u : Ref N) : ℝ :=
  ∑ t, ∑ q, PhysicalLocalEnergy.massOn s
    (rawCovariant C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      u (physicalDomain A v c hc u) q t)

def radiationEnergyOn (s : Set (Configuration N)) (u : Ref N) : ℝ :=
  ∑ t, PhysicalLocalEnergy.massOn s (radiation (Fin N × Fin 3) (fun _ => 0) (u t))

private theorem sum_energy_bound {S Q : Type*} [Fintype S] [Fintype Q]
    (o q O Q' : S → Q → ℝ) (r R : S → ℝ)
    (h : ∀ s, (∑ j, o s j) + (∑ j, q s j) + r s ≤
      (∑ j, O s j) + (∑ j, Q' s j) + R s) :
    (∑ s, ∑ j, o s j) + (∑ s, ∑ j, q s j) + (∑ s, r s) ≤
      (∑ j, ∑ s, O s j) + (∑ j, ∑ s, Q' s j) + (∑ s, R s) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ => h s
  have hs' : (∑ s, ∑ j, o s j) + (∑ s, ∑ j, q s j) + (∑ s, r s) ≤
      (∑ s, ∑ j, O s j) + (∑ s, ∑ j, Q' s j) + (∑ s, R s) := by
    simpa only [Finset.sum_add_distrib] using hs
  exact hs'.trans_eq (congrArg₂ (fun a b : ℝ => a + b + ∑ s, R s)
    Finset.sum_comm Finset.sum_comm)

theorem energy_on_ball_le_localized (u : Ref N) {O : Configuration N} {r L : ℝ}
    (a : BallCutoff O r L) :
    ordinaryEnergyOn (Metric.ball O r) u + covariantEnergyOn C κ hκ M hκbound e A v c hc
      (Metric.ball O r) u + radiationEnergyOn (Metric.ball O r) u ≤
    ordinaryEnergy (PauliLocalEnergy.localize a.multiplier u) +
      covariantEnergy C κ hκ M hκbound e A v c hc (PauliLocalEnergy.localize a.multiplier u) +
      radiationEnergy (PauliLocalEnergy.localize a.multiplier u) := by
  unfold ordinaryEnergyOn covariantEnergyOn radiationEnergyOn ordinaryEnergy
    covariantEnergy radiationEnergy rawCovariant PauliLocalEnergy.localize
  exact sum_energy_bound
    (fun t q => PhysicalLocalEnergy.massOn (Metric.ball O r)
      (ordinary (Fin N × Fin 3) (fun _ => 0) q (u t)))
    (fun t q => PhysicalLocalEnergy.massOn (Metric.ball O r)
      (externalCovariant (fun _ => 0) C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
        (u t) (physicalDomain A v c hc u t) q))
    (fun t q => ‖ordinary (Fin N × Fin 3) (fun _ => 0) q
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.multiplier (u t))‖ ^ 2)
    (fun t q => ‖externalCovariant (fun _ => 0) C κ hκ M hκbound e
      (vector A) (positive v c) (negative v c)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.multiplier (u t))
      ((physicalDomain A v c hc u t).localize (fun _ => 0) a.multiplier) q‖ ^ 2)
    (fun t => PhysicalLocalEnergy.massOn (Metric.ball O r)
      (radiation (Fin N × Fin 3) (fun _ => 0) (u t)))
    (fun t => ‖radiation (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.multiplier (u t))‖ ^ 2)
    (fun t => PhysicalLocalEnergy.energy_on_ball_le_localized (fun _ => 0) C κ hκ M hκbound e
      (vector A) (positive v c) (negative v c) (u t) (physicalDomain A v c hc u t) a)

theorem caccioppoli {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u))
    {O : Configuration N} {r L : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : BallCutoff O r L) :
    ordinaryEnergyOn (Metric.ball O r) u + covariantEnergyOn C κ hκ M hκbound e A v c hc
      (Metric.ball O r) u + radiationEnergyOn (Metric.ball O r) u ≤
      caccioppoliConstant (N := N) M e A v c hc E L / r ^ 2 * massOn (Metric.ball O (2*r)) u :=
  (energy_on_ball_le_localized C κ hκ M hκbound e A v c hc u a).trans
    (localized_full C κ hκ M hκbound e A v c hc heigen hr hr1 a)

theorem exists_caccioppoli_constant {E : ℝ} {u : Ref N}
    (heigen : IsWeakEigenstate C κ hκ M hκbound e (vector A) (positive v c) (negative v c)
      E u (physicalDomain A v c hc u)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (O : Configuration N) (r : ℝ), 0 < r → r ≤ 1 →
      ordinaryEnergyOn (Metric.ball O r) u + covariantEnergyOn C κ hκ M hκbound e A v c hc
        (Metric.ball O r) u + radiationEnergyOn (Metric.ball O r) u ≤
      K / r ^ 2 * massOn (Metric.ball O (2*r)) u :=
  ⟨caccioppoliConstant (N := N) M e A v c hc E (ballCutoffConstant (I := Fin N × Fin 3)),
    caccioppoliConstant_nonneg M e A v c hc E _,
    fun O r hr hr1 => caccioppoli C κ hκ M hκbound e A v c hc heigen hr hr1 (ballCutoff O r hr)⟩

end PfHk.PauliCaccioppoli

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
