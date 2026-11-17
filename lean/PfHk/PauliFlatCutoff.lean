import PfHk.PauliFlatCutoffAlgebra
import PfHk.PauliBufferedCutoffLocality

/-! A cutoff that is flat on a physical wave can be removed from the
test argument of the full Pauli form. Mixed second derivatives account
for all Pauli cross terms. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
namespace PfHk.PauliFlatCutoff

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  GptLean.ElectronicH1Multiplier PfHk.PhysicalLocalEnergy
  PfHk.PhysicalCutoffCommutator PfHk.PhysicalCutoffLocality
  PfHk.PauliSpin PfHk.PauliCurrentAlgebra PfHk.PauliGroundState PfHk.PauliLocalEnergy
open scoped InnerProductSpace

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 40000

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion radiation roughMultiply
  externalCovariant PhysicalPFScalarMultiplier.multiply rawCovariant rawContraction
  DifferentiableMultiplier.multiplier DifferentiableMultiplier.derivativeMultiplier
  rawForm PauliLocalEnergy.error PauliLocalEnergy.localize

private theorem contraction_of_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (n : Fin N) (d : Fin 3 → SpinIndex N → H)
    (hd : ∀ i s, d i s = 0) (s : SpinIndex N) : contraction n d s = 0 := by
  have he : d = 0 := funext fun i => funext (hd i)
  rw [he]
  simp only [contraction, sigmaFamily, Pi.zero_apply, smul_zero, ite_self,
    Finset.sum_apply, Finset.sum_const_zero]

theorem reference_fixed (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (s : SpinIndex N) :
    PhysicalPFScalarMultiplier.multiply (fun _ => 0) a.scalar (u s) = u s :=
  reference_multiply_eq_of_value (fun _ => 0) a.scalar (u s) (u s) (hfix s)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Position (Fin N × Fin 3) → ℝ)
  (positive negative : Position (Fin N × Fin 3) → ℝ)

theorem derivative_covariant_zero (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u)
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i j s, (a.derivative i).derivativeMultiplier j
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (i j : Fin N × Fin 3) (s : SpinIndex N) :
    (a.derivative i).multiplier
      (rawCovariant C κ hκ M hκbound e A positive negative u hu j s) = 0 := by
  have hzero : PhysicalPFScalarMultiplier.multiply (fun _ => 0) (a.derivative i) (u s) = 0 :=
    reference_multiply_eq_of_value (fun _ => 0) (a.derivative i) (u s) 0
      ((hfirst i s).trans (map_zero (inclusion (Fin N × Fin 3) (fun _ => 0))).symm)
  have hzeroD := externalCovariant_zero (fun _ => 0) C κ hκ M hκbound e A positive negative
    _ ((hu s).localize (fun _ => 0) (a.derivative i)) hzero j
  have hproduct := externalCovariant_localize (fun _ => 0) C κ hκ M hκbound e A positive negative
    (u s) (hu s) (a.derivative i) j
  have h := hzeroD.symm.trans hproduct
  unfold rawCovariant
  change (a.derivative i).multiplier
    (externalCovariant (fun _ => 0) C κ hκ M hκbound e A positive negative (u s) (hu s) j) = 0
  simpa only [hsecond i j s, smul_zero, add_zero] using h.symm

theorem derivative_contraction_zero (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u)
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i j s, (a.derivative i).derivativeMultiplier j
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (i : Fin N × Fin 3) (n : Fin N) (s : SpinIndex N) :
    (a.derivative i).multiplier
      (rawContraction C κ hκ M hκbound e A positive negative u hu n s) = 0 := by
  unfold rawContraction
  exact (congrFun (contraction_map n ((a.derivative i).multiplier (H := PhotonFock))
    (fun j => rawCovariant C κ hκ M hκbound e A positive negative u hu (n, j))) s).symm.trans
    (contraction_of_zero n _
      (fun j t => derivative_covariant_zero C κ hκ M hκbound e A positive negative
        a u hu hfirst hsecond i (n, j) t) s)

theorem covariant_fixed (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (i : Fin N × Fin 3) (s : SpinIndex N) :
    a.scalar.multiplier (rawCovariant C κ hκ M hκbound e A positive negative u hu i s) =
      rawCovariant C κ hκ M hκbound e A positive negative u hu i s := by
  have hgrad := (derivative_multiplier a i
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s))).symm.trans (hfirst i s)
  have h := externalCovariant_localize (fun _ => 0) C κ hκ M hκbound e A positive negative
    (u s) (hu s) a.scalar i
  have href := reference_fixed a u hfix s
  unfold rawCovariant
  change a.scalar.multiplier
    (externalCovariant (fun _ => 0) C κ hκ M hκbound e A positive negative (u s) (hu s) i) =
    externalCovariant (fun _ => 0) C κ hκ M hκbound e A positive negative (u s) (hu s) i
  simpa only [href, hgrad, smul_zero, add_zero] using h.symm

theorem contraction_fixed (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (u : Ref N) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (n : Fin N) (s : SpinIndex N) :
    a.scalar.multiplier (rawContraction C κ hκ M hκbound e A positive negative u hu n s) =
      rawContraction C κ hκ M hκbound e A positive negative u hu n s := by
  have hf : (fun j t => a.scalar.multiplier
      (rawCovariant C κ hκ M hκbound e A positive negative u hu (n, j) t)) =
      (fun j => rawCovariant C κ hκ M hκbound e A positive negative u hu (n, j)) :=
    funext fun j => funext fun t =>
      covariant_fixed C κ hκ M hκbound e A positive negative a u hu hfix hfirst (n, j) t
  unfold rawContraction
  exact (congrFun (contraction_map n (a.scalar.multiplier (H := PhotonFock))
    (fun j => rawCovariant C κ hκ M hκbound e A positive negative u hu (n, j))) s).symm.trans
    (congrArg (fun d => contraction n d s) hf)

theorem kinetic_localize_left (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (v u : Ref N) (hv : Domain A positive negative v) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i j s, (a.derivative i).derivativeMultiplier j
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0) (n : Fin N) :
  (∑ s, inner ℂ
    (rawContraction C κ hκ M hκbound e A positive negative (localize a.scalar v)
      (domain_localize hv a.scalar) n s)
    (rawContraction C κ hκ M hκbound e A positive negative u hu n s)) =
  ∑ s, inner ℂ (rawContraction C κ hκ M hκbound e A positive negative v hv n s)
    (rawContraction C κ hκ M hκbound e A positive negative u hu n s) := by
  have herr := PauliFlatCutoffAlgebra.error_pair_zero n
    (fun k => (a.derivative (n, k)).multiplier (H := PhotonFock))
    (fun k => (a.derivative (n, k)).multiplier_symmetric (H := PhotonFock))
    (fun s => inclusion (Fin N × Fin 3) (fun _ => 0) (v s))
    (rawContraction C κ hκ M hκbound e A positive negative u hu n)
    (fun k s => derivative_contraction_zero C κ hκ M hκbound e A positive negative
      a u hu hfirst hsecond (n, k) n s)
  have herr' : (∑ s, inner ℂ (PauliLocalEnergy.error a.scalar v n s)
      (rawContraction C κ hκ M hκbound e A positive negative u hu n s)) = 0 := by
    simpa only [PauliLocalEnergy.error, derivative_multiplier] using herr
  rw [contraction_localize C κ hκ M hκbound e A positive negative a.scalar v hv n]
  exact PauliFlatCutoffAlgebra.kinetic_fixed (a.scalar.multiplier (H := PhotonFock))
    (a.scalar.multiplier_symmetric (H := PhotonFock))
    (rawContraction C κ hκ M hκbound e A positive negative u hu n)
    (rawContraction C κ hκ M hκbound e A positive negative v hv n)
    (PauliLocalEnergy.error a.scalar v n)
    (contraction_fixed C κ hκ M hκbound e A positive negative a u hu hfix hfirst n) herr'

private theorem radiation_pair_fixed (a : DifferentiableMultiplier (Fin N × Fin 3))
    (v u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hfix : PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u = u) :
    inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a v))
      (radiation (Fin N × Fin 3) (fun _ => 0) u) =
    inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) v)
      (radiation (Fin N × Fin 3) (fun _ => 0) u) := by
  have h := scalar_multiplier_pair (H := PhotonFock) a _ _ _ _
    (PhysicalPFScalarMultiplier.radiation_multiply (fun _ => 0) a v)
    (PhysicalPFScalarMultiplier.radiation_multiply (fun _ => 0) a u)
  exact h.symm.trans (congrArg
    (fun z : Reference (Fin N × Fin 3) (fun _ => 0) =>
      inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) v)
        (radiation (Fin N × Fin 3) (fun _ => 0) z)) hfix)

private theorem rough_pair_fixed (a : DifferentiableMultiplier (Fin N × Fin 3))
    (w : Position (Fin N × Fin 3) → ℝ)
    (v u : Reference (Fin N × Fin 3) (fun _ => 0))
    (hv : HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0) v))
    (hu : HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0) u))
    (hav : HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a v)))
    (hau : HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u)))
    (hfix : PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u = u) :
    inner ℂ (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0)
      (PhysicalPFScalarMultiplier.multiply (fun _ => 0) a v)) hav)
      (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu) =
    inner ℂ (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) v) hv)
      (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) u) hu) := by
  have h := scalar_multiplier_pair (H := PhotonFock) a _ _ _ _
    (roughMultiply_reference_localize (fun _ => 0) a w v hv hav)
    (roughMultiply_reference_localize (fun _ => 0) a w u hu hau)
  have hfixed : (⟨PhysicalPFScalarMultiplier.multiply (fun _ => 0) a u, hau⟩ :
      {z : Reference (Fin N × Fin 3) (fun _ => 0) //
        HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0) z)}) = ⟨u, hu⟩ :=
    Subtype.ext hfix
  have hpair := congrArg
    (fun z : {z : Reference (Fin N × Fin 3) (fun _ => 0) //
        HasMultiplier w (inclusion (Fin N × Fin 3) (fun _ => 0) z)} =>
      inner ℂ (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) v) hv)
        (roughMultiply w (inclusion (Fin N × Fin 3) (fun _ => 0) z.val) z.property)) hfixed
  exact h.symm.trans hpair

theorem rawForm_localize_left (a : TwiceDifferentiableMultiplier (Fin N × Fin 3))
    (v u : Ref N) (hv : Domain A positive negative v) (hu : Domain A positive negative u)
    (hfix : ∀ s, a.scalar.multiplier (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s))
    (hfirst : ∀ i s, (a.derivative i).multiplier
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0)
    (hsecond : ∀ i j s, (a.derivative i).derivativeMultiplier j
      (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) = 0) :
    rawForm C κ hκ M hκbound e A positive negative (localize a.scalar v) u
      (domain_localize hv a.scalar) hu =
      rawForm C κ hκ M hκbound e A positive negative v u hv hu := by
  have hk := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun n _ => kinetic_localize_left C κ hκ M hκbound e A positive negative
      a v u hv hu hfix hfirst hsecond n)
  have href := reference_fixed a u hfix
  have hr (s : SpinIndex N) :
      inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (localize a.scalar v s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) =
      inner ℂ (radiation (Fin N × Fin 3) (fun _ => 0) (v s))
        (radiation (Fin N × Fin 3) (fun _ => 0) (u s)) := by
    unfold localize
    exact radiation_pair_fixed a.scalar (v s) (u s) (href s)
  have hp (s : SpinIndex N) :
      inner ℂ (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0)
        (localize a.scalar v s)) ((domain_localize hv a.scalar) s).positive)
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive) =
      inner ℂ (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (v s)) (hv s).positive)
        (roughMultiply positive (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).positive) := by
    unfold localize
    exact rough_pair_fixed a.scalar positive (v s) (u s) (hv s).positive (hu s).positive
      ((hv s).localize (fun _ => 0) a.scalar).positive
      ((hu s).localize (fun _ => 0) a.scalar).positive (href s)
  have hn (s : SpinIndex N) :
      inner ℂ (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0)
        (localize a.scalar v s)) ((domain_localize hv a.scalar) s).negative)
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative) =
      inner ℂ (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (v s)) (hv s).negative)
        (roughMultiply negative (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hu s).negative) := by
    unfold localize
    exact rough_pair_fixed a.scalar negative (v s) (u s) (hv s).negative (hu s).negative
      ((hv s).localize (fun _ => 0) a.scalar).negative
      ((hu s).localize (fun _ => 0) a.scalar).negative (href s)
  unfold rawForm
  exact PauliFlatCutoffAlgebra.form_fixed hk
    (Finset.sum_congr rfl (fun s _ => hr s))
    (Finset.sum_congr rfl (fun s _ => hp s))
    (Finset.sum_congr rfl (fun s _ => hn s))

theorem rawForm_buffered_left {O : Position (Fin N × Fin 3)}
    (family : SmoothCutoffBounds.BufferedFamily O) {r : ℝ} (hr : 0 < r)
    (v u : Ref N) (hv : Domain A positive negative v) (hu : Domain A positive negative u)
    (hs : ∀ s, ∀ᵐ X ∂volume, X ∉ Metric.ball O r →
      inclusion (Fin N × Fin 3) (fun _ => 0) (u s) X = 0) :
    rawForm C κ hκ M hκbound e A positive negative (localize (family.cutoff r).scalar v) u
      (domain_localize hv (family.cutoff r).scalar) hu =
      rawForm C κ hκ M hκbound e A positive negative v u hv hu := by
  have h (s : SpinIndex N) := PauliBufferedCutoffLocality.cutoff_action_mixed family hr
    (inclusion (Fin N × Fin 3) (fun _ => 0) (u s)) (hs s)
  exact rawForm_localize_left C κ hκ M hκbound e A positive negative (family.cutoff r)
    v u hv hu (fun s => (h s).1) (fun i s => (h s).2.1 i) (fun i j s => (h s).2.2 i j)

end PfHk.PauliFlatCutoff
attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed GptLean.SymmetricLift.TensorHilbert.inner
