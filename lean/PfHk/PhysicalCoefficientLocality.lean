import PfHk.PhysicalLocalEnergyRough

/-! External multiplication and the actual weak form depend only on
coefficients on the supports of their arguments. -/

noncomputable section
namespace PfHk.PhysicalCoefficientLocality

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
  PfHk.PhysicalLocalEnergy
open scoped InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

attribute [local irreducible] inclusion covariant radiation potential roughMultiply
  externalCovariant externalForm PhysicalPFReference.referenceSubspace

private theorem smul_eq_on_support {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure X}
    (u : X → H) (a b : X → ℝ) (h : ∀ᵐ x ∂μ, u x ≠ 0 → a x = b x) :
    (fun x => a x • u x) =ᵐ[μ] fun x => b x • u x := by
  filter_upwards [h] with x hx
  by_cases hu : u x = 0
  · simp only [hu, smul_zero]
  · exact congrArg (fun z : ℝ => z • u x) (hx hu)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem hasMultiplier_congr (u : WaveSpace I) (a b : Position I → ℝ)
    (ha : HasMultiplier a u) (h : ∀ᵐ x ∂volume, u x ≠ 0 → a x = b x) :
    HasMultiplier b u := ha.ae_eq (smul_eq_on_support u a b h)

theorem roughMultiply_congr (u : WaveSpace I) (a b : Position I → ℝ)
    (ha : HasMultiplier a u) (hb : HasMultiplier b u)
    (h : ∀ᵐ x ∂volume, u x ≠ 0 → a x = b x) :
    roughMultiply a u ha = roughMultiply b u hb := by
  unfold roughMultiply
  exact MemLp.toLp_congr ha hb (smul_eq_on_support u a b h)

variable (V : Position I → ℝ)
  (A A' : I → Position I → ℝ) (positive negative positive' negative' : Position I → ℝ)

structure Agreement (ψ : WaveSpace I) : Prop where
  vector : ∀ i, ∀ᵐ x ∂volume, ψ x ≠ 0 → A i x = A' i x
  positive : ∀ᵐ x ∂volume, ψ x ≠ 0 → positive x = positive' x
  negative : ∀ᵐ x ∂volume, ψ x ≠ 0 → negative x = negative' x

theorem Agreement.symm {ψ : WaveSpace I}
    (h : Agreement A A' positive negative positive' negative' ψ) :
    Agreement A' A positive' negative' positive negative ψ :=
  ⟨fun i => (h.vector i).mono fun _ hx hn => (hx hn).symm,
    h.positive.mono fun _ hx hn => (hx hn).symm,
    h.negative.mono fun _ hx hn => (hx hn).symm⟩

theorem domain_congr (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (h : Agreement A A' positive negative positive' negative' (inclusion I V u)) :
    ExternalDomain V A' positive' negative' u :=
  ⟨fun i => hasMultiplier_congr _ _ _ (hu.vector i) (h.vector i),
    hasMultiplier_congr _ _ _ hu.positive h.positive,
    hasMultiplier_congr _ _ _ hu.negative h.negative⟩

theorem agreement_localize
    (a : ElectronicH1Multiplier.DifferentiableMultiplier I) (u : Reference I V)
    (hA : ∀ i x, a.weight x ≠ 0 → A i x = A' i x)
    (hp : ∀ x, a.weight x ≠ 0 → positive x = positive' x)
    (hn : ∀ x, a.weight x ≠ 0 → negative x = negative' x) :
    Agreement A A' positive negative positive' negative'
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u)) := by
  have hscalar : (a.multiplier (H := PhotonFock) (inclusion I V u) : Position I → PhotonFock) =ᵐ[volume]
      fun x => a.weight x • inclusion I V u x :=
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound (ae_of_all _ a.bounded) _
  have heq := (Filter.EventuallyEq.of_eq (congrArg (fun z : WaveSpace I => ⇑z)
    (PhysicalPFScalarMultiplier.value_multiply V a u))).trans hscalar
  have hweight : ∀ᵐ x ∂volume,
      inclusion I V (PhysicalPFScalarMultiplier.multiply V a u) x ≠ 0 → a.weight x ≠ 0 := by
    filter_upwards [heq] with x hx hne hz
    exact hne (hx.trans ((congrArg (fun z : ℝ => z • inclusion I V u x) hz).trans (zero_smul _ _)))
  exact ⟨fun i => hweight.mono fun x hx hu => hA i x (hx hu),
    hweight.mono fun x hx hu => hp x (hx hu), hweight.mono fun x hx hu => hn x (hx hu)⟩

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i : I, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i : I, ∀ᵐ x : Position I ∂volume, ‖(κ i x).val‖ ≤ M) (e : ℝ)

theorem covariant_congr (u : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hu' : ExternalDomain V A' positive' negative' u)
    (h : Agreement A A' positive negative positive' negative' (inclusion I V u)) (i : I) :
    externalCovariant V C κ hκ M hbound e A positive negative u hu i =
      externalCovariant V C κ hκ M hbound e A' positive' negative' u hu' i := by
  unfold externalCovariant
  exact congrArg (fun z : WaveSpace I => covariant I V C κ hκ M hbound e i u + z)
    (roughMultiply_congr _ _ _ (hu.vector i) (hu'.vector i) (h.vector i))

theorem form_congr (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v)
    (hu' : ExternalDomain V A' positive' negative' u)
    (hv' : ExternalDomain V A' positive' negative' v)
    (hU : Agreement A A' positive negative positive' negative' (inclusion I V u))
    (hV : Agreement A A' positive negative positive' negative' (inclusion I V v)) :
    externalForm V C κ hκ M hbound e A positive negative u v hu hv =
      externalForm V C κ hκ M hbound e A' positive' negative' u v hu' hv' := by
  have hkin : (∑ i, ⟪externalCovariant V C κ hκ M hbound e A positive negative u hu i,
      externalCovariant V C κ hκ M hbound e A positive negative v hv i⟫_ℂ) =
      ∑ i, ⟪externalCovariant V C κ hκ M hbound e A' positive' negative' u hu' i,
        externalCovariant V C κ hκ M hbound e A' positive' negative' v hv' i⟫_ℂ :=
    Finset.sum_congr rfl fun i _ => congrArg₂ (fun x y : WaveSpace I => ⟪x, y⟫_ℂ)
      (covariant_congr V A A' positive negative positive' negative' C κ hκ M hbound e u hu hu' hU i)
      (covariant_congr V A A' positive negative positive' negative' C κ hκ M hbound e v hv hv' hV i)
  have hpos := congrArg₂ (fun x y : WaveSpace I => ⟪x, y⟫_ℂ)
    (roughMultiply_congr _ _ _ hu.positive hu'.positive hU.positive)
    (roughMultiply_congr _ _ _ hv.positive hv'.positive hV.positive)
  have hneg := congrArg₂ (fun x y : WaveSpace I => ⟪x, y⟫_ℂ)
    (roughMultiply_congr _ _ _ hu.negative hu'.negative hU.negative)
    (roughMultiply_congr _ _ _ hv.negative hv'.negative hV.negative)
  unfold externalForm
  exact congrArg₂ (fun x y : ℂ => x - y)
    (congrArg₂ (fun x y : ℂ => x + y)
      (congrArg (fun z : ℂ => (1 / 2 : ℂ) * z +
        ⟪radiation I V u, radiation I V v⟫_ℂ + ⟪potential I V u, potential I V v⟫_ℂ) hkin)
      hpos) hneg

end PfHk.PhysicalCoefficientLocality
