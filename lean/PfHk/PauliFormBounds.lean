import PfHk.PauliFreeGradient
import PfHk.PauliRawForm
import PfHk.PauliContractionRecovery
import PfHk.PauliCoercivityAlgebra
import PfHk.PhysicalOrdinaryMultiplierBound

/-! Recovery of ordinary electronic derivatives from the physical Pauli
form. The external vector multiplier is absorbed using an ordinary scalar
Sobolev bound. The quantum term uses the actual radiation graph estimate. -/

set_option Elab.async false
noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliFormBounds

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PauliSpin PauliCurrentAlgebra PauliGroundState PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  PhysicalPFReference.field rawCovariant rawContraction externalCovariant roughMultiply rawForm rawEnergy

def ordinaryEnergy (u : Ref N) : ℝ :=
  ∑ q : Fin N × Fin 3, ∑ s, ‖ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)‖ ^ 2

def radiationEnergy (u : Ref N) : ℝ :=
  ∑ s, ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2

theorem ordinaryEnergy_nonneg (u : Ref N) : 0 ≤ ordinaryEnergy (N := N) u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem radiationEnergy_nonneg (u : Ref N) : 0 ≤ radiationEnergy (N := N) u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem scalar_bound (w : Position (Fin N × Fin 3) → ℝ) (ε C₀ : ℝ) (hε : 0 ≤ ε)
    (hSob : ScalarMultiplierBound w ε C₀) (u : Ref N)
    (hu : ∀ s, HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))) :
    (∑ s, ‖roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s)‖ ^ 2) ≤
      ε * ordinaryEnergy (N := N) u + C₀ * normSquared (N := N) u := by
  exact PauliCoercivityAlgebra.sum_scalar_bounds
    (S := SpinIndex N) (Q := Fin N × Fin 3)
    (fun s => ‖roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s)‖ ^ 2)
    (fun s q => ‖ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)‖ ^ 2)
    (fun s => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2) ε C₀
    (fun s => PhysicalOrdinaryMultiplierBound.scalar_bound (I := Fin N × Fin 3)
      (fun _ => 0) w ε C₀ hε hSob (u s) (hu s))

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Position (Fin N × Fin 3) → ℝ)
  (positive negative : Position (Fin N × Fin 3) → ℝ)

def pauliEnergy (u : Ref N) (hu : Domain A positive negative u) : ℝ :=
  ∑ n, ∑ s, ‖rawContraction C κ hκ M hκbound e A positive negative u hu n s‖ ^ 2

def fieldEnergy (u : Ref N) : ℝ :=
  ∑ q : Fin N × Fin 3, ∑ s, ‖field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound q (u s)‖ ^ 2

def vectorEnergy (u : Ref N) (hu : Domain A positive negative u) : ℝ :=
  ∑ q : Fin N × Fin 3, ∑ s,
    ‖roughMultiply (A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).vector q)‖ ^ 2

theorem pauliEnergy_nonneg (u : Ref N) (hu : Domain A positive negative u) :
    0 ≤ pauliEnergy C κ hκ M hκbound e A positive negative u hu :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem derivative_recovery (u : Ref N) (hu : Domain A positive negative u) :
    ordinaryEnergy (N := N) u ≤
      3 * pauliEnergy C κ hκ M hκbound e A positive negative u hu +
      9 * e ^ 2 * fieldEnergy C κ hκ M hκbound u +
      9 * vectorEnergy A positive negative u hu := by
  have h (n : Fin N) :
      (∑ a : Fin 3, ∑ s, ‖ordinary (Fin N × Fin 3) (fun _ => 0) (n, a) (u s)‖ ^ 2) ≤
      3 * (∑ s, ‖rawContraction C κ hκ M hκbound e A positive negative u hu n s‖ ^ 2) +
      9 * e ^ 2 * (∑ a : Fin 3, ∑ s,
        ‖field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound (n, a) (u s)‖ ^ 2) +
      9 * (∑ a : Fin 3, ∑ s, ‖roughMultiply (A (n, a))
        (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).vector (n, a))‖ ^ 2) := by
    have hf := PauliFreeGradient.reference_norm_sq (N := N) u n
    apply hf.symm.le.trans
    unfold rawContraction
    apply PauliContractionRecovery.contraction_recovery (H := WaveSpace (Fin N × Fin 3)) n
    funext a s
    have hc := covariant_apply (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound e (n, a) (u s)
    change (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) (n, a) (u s) =
      rawCovariant C κ hκ M hκbound e A positive negative u hu (n, a) s +
      (e : ℂ) • field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound (n, a) (u s) -
      roughMultiply (A (n, a)) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).vector (n, a))
    let p : WaveSpace (Fin N × Fin 3) :=
      (-Complex.I) • ordinary (Fin N × Fin 3) (fun _ => 0) (n, a) (u s)
    let f : WaveSpace (Fin N × Fin 3) :=
      (e : ℂ) • field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound (n, a) (u s)
    let av : WaveSpace (Fin N × Fin 3) :=
      roughMultiply (A (n, a)) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).vector (n, a))
    have hd : rawCovariant C κ hκ M hκbound e A positive negative u hu (n, a) s = p - f + av := by
      unfold rawCovariant externalCovariant
      exact congrArg (fun z : WaveSpace (Fin N × Fin 3) => z + av) hc
    have ha : p = (p - f + av) + f - av := by abel
    exact ha.trans (congrArg (fun z : WaveSpace (Fin N × Fin 3) => z + f - av) hd.symm)

  have hs := Finset.sum_le_sum (s := Finset.univ) (fun n _ => h n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simpa only [ordinaryEnergy, pauliEnergy, fieldEnergy, vectorEnergy,
    Fintype.sum_prod_type] using hs

theorem field_bound (u : Ref N) :
    fieldEnergy C κ hκ M hκbound u ≤
      8 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 * radiationEnergy (N := N) u +
      2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 * normSquared (N := N) u := by
  have h := PauliCoercivityAlgebra.sum_uniform_bounds
    (S := SpinIndex N) (Q := Fin N × Fin 3)
    (fun q s => ‖field (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound q (u s)‖ ^ 2)
    (fun s => ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2)
    (fun s => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖ ^ 2)
    (8 * (max M 0) ^ 2) (2 * (max M 0) ^ 2)
    (fun q s => uniform_field_bound (I := Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound (u s) q)
  unfold fieldEnergy radiationEnergy normSquared
  convert h using 1
  ring

theorem vector_bound (ε C_A : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ q, ScalarMultiplierBound (A q) ε C_A)
    (u : Ref N) (hu : Domain A positive negative u) :
    vectorEnergy A positive negative u hu ≤
      (Fintype.card (Fin N × Fin 3) : ℝ) * ε * ordinaryEnergy (N := N) u +
      (Fintype.card (Fin N × Fin 3) : ℝ) * C_A * normSquared (N := N) u := by
  exact PauliCoercivityAlgebra.sum_repeated_bound (Q := Fin N × Fin 3)
    (fun q => ∑ s, ‖roughMultiply (A q) (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
      ((hu s).vector q)‖ ^ 2) ε (ordinaryEnergy (N := N) u) C_A (normSquared (N := N) u)
    (fun q => scalar_bound (A q) ε C_A hε (hA q) u (fun s => (hu s).vector q))

/-- Absorption gives the ordinary H1 estimate with explicit constants. -/

theorem ordinary_bound (ε C_A : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ q, ScalarMultiplierBound (A q) ε C_A)
    (hsmall : 9 * (Fintype.card (Fin N × Fin 3) : ℝ) * ε ≤ 1 / 2)
    (u : Ref N) (hu : Domain A positive negative u) :
    ordinaryEnergy (N := N) u ≤
      6 * pauliEnergy C κ hκ M hκbound e A positive negative u hu +
      144 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 * radiationEnergy (N := N) u +
      (36 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 +
        18 * (Fintype.card (Fin N × Fin 3) : ℝ) * C_A) * normSquared (N := N) u :=
  PauliCoercivityAlgebra.recover_ordinary (ordinaryEnergy_nonneg (N := N) u)
    (derivative_recovery C κ hκ M hκbound e A positive negative u hu)
    (field_bound C κ hκ M hκbound u)
    (vector_bound A positive negative ε C_A hε hA u hu) hsmall

def recoveryFactor (N : ℕ) (e M : ℝ) : ℝ :=
  6 + 144 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2

def massFactor (N : ℕ) (e M C_A : ℝ) : ℝ :=
  36 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2 +
    18 * (Fintype.card (Fin N × Fin 3) : ℝ) * C_A

theorem ordinary_sum_bound (ε C_A : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ q, ScalarMultiplierBound (A q) ε C_A)
    (hsmall : 9 * (Fintype.card (Fin N × Fin 3) : ℝ) * ε ≤ 1 / 2)
    (u : Ref N) (hu : Domain A positive negative u) :
    ordinaryEnergy (N := N) u ≤ recoveryFactor N e M *
      (pauliEnergy C κ hκ M hκbound e A positive negative u hu + radiationEnergy (N := N) u) +
      massFactor N e M C_A * normSquared (N := N) u := by
  have ho := ordinary_bound C κ hκ M hκbound e A positive negative ε C_A hε hA hsmall u hu
  have hp := mul_nonneg
    (by positivity : 0 ≤ 144 * e ^ 2 * (Fintype.card (Fin N × Fin 3) : ℝ) * (max M 0) ^ 2)
    (pauliEnergy_nonneg C κ hκ M hκbound e A positive negative u hu)
  have hr := radiationEnergy_nonneg (N := N) u
  unfold recoveryFactor massFactor
  nlinarith only [ho, hp, hr]

/-- The negative scalar part is absorbed into the actual Pauli form. -/

theorem form_lower_bound (ε C_A : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ q, ScalarMultiplierBound (A q) ε C_A)
    (hsmall : 9 * (Fintype.card (Fin N × Fin 3) : ℝ) * ε ≤ 1 / 2)
    (δ C₀ : ℝ) (hδ : 0 ≤ δ) (hv : ScalarMultiplierBound negative δ C₀)
    (hvsmall : δ * recoveryFactor N e M ≤ 1 / 4)
    (u : Ref N) (hu : Domain A positive negative u) :
    (pauliEnergy C κ hκ M hκbound e A positive negative u hu + radiationEnergy (N := N) u) / 4 -
      (C₀ + δ * massFactor N e M C_A) * normSquared (N := N) u ≤
      rawEnergy C κ hκ M hκbound e A positive negative u hu := by
  have ho := ordinary_sum_bound C κ hκ M hκbound e A positive negative ε C_A hε hA hsmall u hu
  have hn := scalar_bound negative δ C₀ hδ hv u (fun s => (hu s).negative)
  have he := rawEnergy_eq C κ hκ M hκbound e A positive negative u hu
  have hp := pauliEnergy_nonneg C κ hκ M hκbound e A positive negative u hu
  have hr := radiationEnergy_nonneg (N := N) u
  have hw : 0 ≤ ∑ s, ‖roughMultiply positive
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).positive)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply PauliCoercivityAlgebra.form_lower_bound hp hr
    hw hδ ho hn _ hvsmall
  convert he using 1
  unfold pauliEnergy radiationEnergy
  ring

/-- Control of the full ordinary, Pauli and radiation energies. -/

theorem full_energy_bound (ε C_A : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ q, ScalarMultiplierBound (A q) ε C_A)
    (hsmall : 9 * (Fintype.card (Fin N × Fin 3) : ℝ) * ε ≤ 1 / 2)
    (δ C₀ : ℝ) (hδ : 0 ≤ δ) (hv : ScalarMultiplierBound negative δ C₀)
    (hvsmall : δ * recoveryFactor N e M ≤ 1 / 4)
    (u : Ref N) (hu : Domain A positive negative u) :
    ordinaryEnergy (N := N) u + pauliEnergy C κ hκ M hκbound e A positive negative u hu + radiationEnergy (N := N) u ≤
      4 * (recoveryFactor N e M + 1) * rawEnergy C κ hκ M hκbound e A positive negative u hu +
      (4 * (recoveryFactor N e M + 1) * (C₀ + δ * massFactor N e M C_A) +
        massFactor N e M C_A) * normSquared (N := N) u := by
  have ho := ordinary_sum_bound C κ hκ M hκbound e A positive negative ε C_A hε hA hsmall u hu
  have hn := scalar_bound negative δ C₀ hδ hv u (fun s => (hu s).negative)
  have he := rawEnergy_eq C κ hκ M hκbound e A positive negative u hu
  have hp := pauliEnergy_nonneg C κ hκ M hκbound e A positive negative u hu
  have hr := radiationEnergy_nonneg (N := N) u
  have hw : 0 ≤ ∑ s, ‖roughMultiply positive
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) ((hu s).positive)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply PauliCoercivityAlgebra.full_energy_bound hp hr
    hw hδ
    (by unfold recoveryFactor; positivity) ho hn _ hvsmall
  convert he using 1
  unfold pauliEnergy radiationEnergy
  ring

end PfHk.PauliFormBounds
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
