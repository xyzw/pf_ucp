import PfHk.PhysicalLocalEnergyIMS

/-! The single-cutoff identity with rough external magnetic and signed
electric potentials. Domain witnesses state only that the corresponding
pointwise multiplication belongs to L2. Localization of this domain and
the IMS formula are proved below. -/

noncomputable section

namespace PfHk.PhysicalLocalEnergy

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPFReference
open GptLean.ElectronicH1Multiplier
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false

attribute [local irreducible] PhysicalPFReference.covariant PhysicalPFReference.field
  PhysicalPFReference.ordinary PhysicalPFReference.inclusion PhysicalPFReference.radiation
  PhysicalPFReference.potential PhysicalPFScalarMultiplier.multiply

variable {I : Type} [Fintype I] [DecidableEq I]

def HasMultiplier (f : Position I → ℝ) (u : WaveSpace I) : Prop :=
  MemLp (fun x => f x • u x) 2 volume

def roughMultiply (f : Position I → ℝ) (u : WaveSpace I)
    (h : HasMultiplier f u) : WaveSpace I := h.toLp _

theorem roughMultiply_ae (f : Position I → ℝ) (u : WaveSpace I)
    (h : HasMultiplier f u) :
    roughMultiply f u h =ᵐ[volume] fun x => f x • u x := h.coeFn_toLp

theorem hasMultiplier_localize (a : DifferentiableMultiplier I)
    (f : Position I → ℝ) (u : WaveSpace I) (h : HasMultiplier f u) :
    HasMultiplier f (a.multiplier u) := by
  refine (memLp_congr_ae ?_).mp (a.weighted_memLp (roughMultiply f u h))
  filter_upwards [roughMultiply_ae f u h,
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) u] with x hx hy
  calc
    _ = a.weight x • (f x • u x) := congrArg (fun z : PhotonFock => a.weight x • z) hx
    _ = f x • (a.weight x • u x) := smul_comm _ _ _
    _ = _ := congrArg (fun z : PhotonFock => f x • z) hy.symm

theorem roughMultiply_localize (a : DifferentiableMultiplier I)
    (f : Position I → ℝ) (u : WaveSpace I) (h : HasMultiplier f u)
    (h' : HasMultiplier f (a.multiplier u)) :
    roughMultiply f (a.multiplier u) h' = a.multiplier (roughMultiply f u h) := by
  apply Lp.ext
  filter_upwards [roughMultiply_ae f (a.multiplier u) h', roughMultiply_ae f u h,
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) u,
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (roughMultiply f u h)] with x h₁ h₂ h₃ h₄
  calc
    _ = f x • a.multiplier u x := h₁
    _ = f x • (a.weight x • u x) := congrArg (fun z : PhotonFock => f x • z) h₃
    _ = a.weight x • (f x • u x) := smul_comm _ _ _
    _ = a.weight x • roughMultiply f u h x := congrArg (fun z : PhotonFock => a.weight x • z) h₂.symm
    _ = _ := h₄.symm

variable (V : Position I → ℝ)

theorem roughMultiply_reference_localize (a : DifferentiableMultiplier I)
    (f : Position I → ℝ) (u : Reference I V)
    (h : HasMultiplier f (inclusion I V u))
    (h' : HasMultiplier f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u))) :
    roughMultiply f (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u)) h' =
      a.multiplier (roughMultiply f (inclusion I V u) h) := by
  have heq := PhysicalPFScalarMultiplier.value_multiply V a u
  apply Lp.ext
  filter_upwards [roughMultiply_ae f _ h', roughMultiply_ae f _ h,
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (inclusion I V u),
    PhotonLocalization.realL2Multiplier_apply a.weight
      a.differentiable.continuous.aestronglyMeasurable a.bound
      (ae_of_all _ a.bounded) (roughMultiply f (inclusion I V u) h)] with x h₁ h₂ h₃ h₄
  have hvalue : inclusion I V (PhysicalPFScalarMultiplier.multiply V a u) x =
      a.multiplier (inclusion I V u) x := congrArg (fun z : WaveSpace I => z x) heq
  calc
    _ = f x • inclusion I V (PhysicalPFScalarMultiplier.multiply V a u) x := h₁
    _ = f x • a.multiplier (inclusion I V u) x := congrArg (fun z : PhotonFock => f x • z) hvalue
    _ = f x • (a.weight x • inclusion I V u x) := congrArg (fun z : PhotonFock => f x • z) h₃
    _ = a.weight x • (f x • inclusion I V u x) := smul_comm _ _ _
    _ = a.weight x • roughMultiply f (inclusion I V u) h x :=
      congrArg (fun z : PhotonFock => a.weight x • z) h₂.symm
    _ = _ := h₄.symm

/-- The three extra multiplication-domain conditions for rough external
fields. For an electric potential v, take the amplitudes sqrt(v₊) and
sqrt(v₋). These are membership conditions, not energy estimates. -/
structure ExternalDomain (A : I → Position I → ℝ)
    (positive negative : Position I → ℝ) (u : Reference I V) : Prop where
  vector : ∀ i, HasMultiplier (A i) (inclusion I V u)
  positive : HasMultiplier positive (inclusion I V u)
  negative : HasMultiplier negative (inclusion I V u)

attribute [local irreducible] roughMultiply DifferentiableMultiplier.multiplier
  DifferentiableMultiplier.derivativeMultiplier

theorem ExternalDomain.localize {A : I → Position I → ℝ}
    {positive negative : Position I → ℝ} {u : Reference I V}
    (hu : ExternalDomain V A positive negative u) (a : DifferentiableMultiplier I) :
    ExternalDomain V A positive negative (PhysicalPFScalarMultiplier.multiply V a u) := by
  constructor
  · intro i
    exact (congrArg (HasMultiplier (A i)) (PhysicalPFScalarMultiplier.value_multiply V a u)).mpr
      (hasMultiplier_localize a (A i) (inclusion I V u) (hu.vector i))
  · exact (congrArg (HasMultiplier positive) (PhysicalPFScalarMultiplier.value_multiply V a u)).mpr
      (hasMultiplier_localize a positive (inclusion I V u) hu.positive)
  · exact (congrArg (HasMultiplier negative) (PhysicalPFScalarMultiplier.value_multiply V a u)).mpr
      (hasMultiplier_localize a negative (inclusion I V u) hu.negative)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)
  (A : I → Position I → ℝ) (positive negative : Position I → ℝ)

def externalCovariant (u : Reference I V) (hu : ExternalDomain V A positive negative u)
    (i : I) : WaveSpace I :=
  covariant I V C κ hκ M hbound e i u +
    roughMultiply (A i) (inclusion I V u) (hu.vector i)

theorem externalCovariant_localize (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) (a : DifferentiableMultiplier I) (i : I) :
    externalCovariant V C κ hκ M hbound e A positive negative
      (PhysicalPFScalarMultiplier.multiply V a u) (hu.localize V a) i =
    a.multiplier (externalCovariant V C κ hκ M hbound e A positive negative u hu i) +
      (-Complex.I) • a.derivativeMultiplier i (inclusion I V u) := by
  have hD := PhysicalPFScalarMultiplier.covariant_multiply V a C κ hκ M hbound e u i
  have hx : roughMultiply (A i)
      (inclusion I V (PhysicalPFScalarMultiplier.multiply V a u))
      ((hu.localize V a).vector i) =
      a.multiplier (roughMultiply (A i) (inclusion I V u) (hu.vector i)) := by
    exact roughMultiply_reference_localize V a (A i) u _ _
  let L : WaveSpace I →L[ℂ] WaveSpace I := a.multiplier
  let b := (-Complex.I) • a.derivativeMultiplier i (inclusion I V u)
  let d := covariant I V C κ hκ M hbound e i u
  let q := roughMultiply (A i) (inclusion I V u) (hu.vector i)
  exact (congrArg₂ (· + ·) hD hx).trans
    ((add_right_comm (L d) b (L q)).trans
      (congrArg (fun z : WaveSpace I => z + b) (L.map_add d q).symm))

attribute [local irreducible] externalCovariant

def externalForm (u v : Reference I V)
    (hu : ExternalDomain V A positive negative u)
    (hv : ExternalDomain V A positive negative v) : ℂ :=
  (1 / 2 : ℂ) * ∑ i,
    ⟪externalCovariant V C κ hκ M hbound e A positive negative u hu i,
      externalCovariant V C κ hκ M hbound e A positive negative v hv i⟫_ℂ +
  ⟪radiation I V u, radiation I V v⟫_ℂ +
  ⟪potential I V u, potential I V v⟫_ℂ +
  ⟪roughMultiply positive (inclusion I V u) hu.positive,
    roughMultiply positive (inclusion I V v) hv.positive⟫_ℂ -
  ⟪roughMultiply negative (inclusion I V u) hu.negative,
    roughMultiply negative (inclusion I V v) hv.negative⟫_ℂ

def externalEnergy (u : Reference I V) (hu : ExternalDomain V A positive negative u) : ℝ :=
  (1 / 2 : ℝ) * ∑ i,
    ‖externalCovariant V C κ hκ M hbound e A positive negative u hu i‖ ^ 2 +
  ‖radiation I V u‖ ^ 2 + ‖potential I V u‖ ^ 2 +
  ‖roughMultiply positive (inclusion I V u) hu.positive‖ ^ 2 -
  ‖roughMultiply negative (inclusion I V u) hu.negative‖ ^ 2

attribute [local irreducible] externalForm externalEnergy

theorem externalForm_diagonal (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) :
    (externalForm V C κ hκ M hbound e A positive negative u u hu hu).re =
      externalEnergy V C κ hκ M hbound e A positive negative u hu := by
  simp only [externalForm, externalEnergy, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im,
     Complex.re_sum, Complex.im_sum,
    re_inner_self (H := WaveSpace I), zero_div, zero_mul, sub_zero]


def IsExternalWeakEigenstate (E : ℝ) (u : Reference I V)
    (hu : ExternalDomain V A positive negative u) : Prop :=
  ∀ v : Reference I V, ∀ hv : ExternalDomain V A positive negative v,
    externalForm V C κ hκ M hbound e A positive negative v u hv hu =
      (E : ℂ) * ⟪inclusion I V v, inclusion I V u⟫_ℂ

end PfHk.PhysicalLocalEnergy
