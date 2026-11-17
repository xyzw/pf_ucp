import GptLean.PhysicalPFDomain
import GptLean.PhotonLocalizationLocalFormsOperators

/-!
Closed forms of the Pauli--Fierz Hamiltonians, for the operator identities of
`app-transformation-properties`.

The internal Hamiltonian `H^{0,0}` is the self-adjoint operator of the closed
form `q(v, w) = ⟪D v, D w⟫`, where `D = energyOperator` is the closed graph
operator. Its components are `2^{-1/2}` times the covariant derivatives, the
radiation root and the Coulomb root. Its domain is the reference domain
`𝒬_PF`, the image of `Reference`, which depends neither on the coupling nor on
the field kernels.

For bounded real external potentials, given by a vector potential with one
component `a i` for each configuration coordinate and a scalar potential `w`,
the form of `H^{w,a}` in `qvA-def` is

`q^{w,a}(v, v') = ⟪D v + B_a v, D v' + B_a v'⟫ + ⟪v, w v'⟫`,

where `B_a` multiplies the covariant coordinates by `2^{-1/2} a i` and
vanishes on the radiation and Coulomb coordinates. Its covariant coordinates
are therefore `2^{-1/2} (Dᵢ + aᵢ)`. For `I = Fin N × Fin 3`, the spatial
potentials `A` and `v` give `a (n, μ) X = A_μ(xₙ)` and `w X = ∑ₙ v(xₙ)`.

By the uniqueness part of the representation theorem for closed forms, an
identity of closed forms together with the matching form domains is an
identity of the self-adjoint operators. The representation theorem itself is
not formalized. This file contains the facts used to pass from identities on
the reference domain to identities of closed forms: transport of the form
domain, the inner product of form coordinates, and polarization.
-/

noncomputable section

namespace GptLean.TransformationsClosedForm

open MeasureTheory PhysicalFock PhysicalPFReference
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

section Algebra

/-- Polarization: linear maps with equal norms have equal inner products. -/
theorem inner_eq_of_norm_eq {Q E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f g : Q →ₗ[ℂ] E)
    (h : ∀ x, ‖f x‖ = ‖g x‖) (x y : Q) : ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ := by
  have h1 : f x + f y = f (x + y) := (map_add f x y).symm
  have h2 : f x - f y = f (x - y) := (map_sub f x y).symm
  have h3 : f x - (RCLike.I : ℂ) • f y = f (x - (RCLike.I : ℂ) • y) := by
    rw [map_sub, map_smul]
  have h4 : f x + (RCLike.I : ℂ) • f y = f (x + (RCLike.I : ℂ) • y) := by
    rw [map_add, map_smul]
  have g1 : g x + g y = g (x + y) := (map_add g x y).symm
  have g2 : g x - g y = g (x - y) := (map_sub g x y).symm
  have g3 : g x - (RCLike.I : ℂ) • g y = g (x - (RCLike.I : ℂ) • y) := by
    rw [map_sub, map_smul]
  have g4 : g x + (RCLike.I : ℂ) • g y = g (x + (RCLike.I : ℂ) • y) := by
    rw [map_add, map_smul]
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (f x) (f y),
    inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (g x) (g y), h1, h2, h3, h4, g1, g2, g3, g4,
    h, h, h, h]

end Algebra

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The inner product of form coordinates is the sum over the covariant,
radiation and Coulomb coordinates. -/
theorem inner_output (x y : EnergyOutput I) :
    ⟪x, y⟫_ℂ = (∑ i, ⟪x (Sum.inl i), y (Sum.inl i)⟫_ℂ) +
      ⟪x (Sum.inr 0), y (Sum.inr 0)⟫_ℂ + ⟪x (Sum.inr 1), y (Sum.inr 1)⟫_ℂ :=
  (PiLp.inner_apply x y).trans ((Fintype.sum_sum_type _).trans
    ((congrArg (fun t : ℂ => (∑ i, ⟪x (Sum.inl i), y (Sum.inl i)⟫_ℂ) + t)
      (Fin.sum_univ_two fun n => ⟪x (Sum.inr n), y (Sum.inr n)⟫_ℂ)).trans (add_assoc _ _ _).symm))

section Domain

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

set_option hygiene false in
local notation "D" => energyOperator I V C κ hκ M hbound e

/-- Every vector of the form domain comes from the reference domain. -/
theorem exists_reference (v : (D).domain) : ∃ u : Reference I V, inclusion I V u = v :=
  (PhysicalPFRadiation.normalEnergy_operator_domain I V C κ hκ M hbound e v).mp v.2

/-- The form coordinates of a reference vector are its value under `D`. -/
theorem energyOperator_reference (u : Reference I V) (v : (D).domain)
    (hv : inclusion I V u = v) :
    D v = energyOutput I V C κ hκ M hbound e u :=
  (D).mem_graph_snd_inj ((D).mem_graph v)
    (reference_mem_energyOperator I V C κ hκ M hbound e u) hv.symm

/-- The closed form on the diagonal is the Pauli--Fierz energy. -/
theorem norm_energyOperator_sq (u : Reference I V) (v : (D).domain)
    (hv : inclusion I V u = v) :
    ‖D v‖ ^ 2 = energy I V C κ hκ M hbound e u :=
  (congrArg (fun x : EnergyOutput I => ‖x‖ ^ 2)
    (energyOperator_reference V C κ hκ M hbound e u v hv)).trans
    (energyOutput_norm_sq I V C κ hκ M hbound e u)

variable (κ' : I → Position I → WeightedPhotonKernel)
  (hκ' : ∀ i, AEStronglyMeasurable (κ' i) volume)
  (M' : ℝ) (hbound' : ∀ i, ∀ᵐ x ∂volume, ‖κ' i x‖ ≤ M') (e' : ℝ)

/-- **Transport of the form domain.** A map of the wave space with a left
inverse, both of which map the reference domain into itself, maps the form
domain onto the form domain. The two closed operators may have different
kernels and couplings, since the form domain depends on neither. -/
theorem mem_domain_transport (T T' : WaveSpace I → WaveSpace I)
    (hinv : ∀ v, T' (T v) = v)
    (hT : ∀ u : Reference I V, ∃ u' : Reference I V, inclusion I V u' = T (inclusion I V u))
    (hT' : ∀ u : Reference I V, ∃ u' : Reference I V, inclusion I V u' = T' (inclusion I V u))
    (v : WaveSpace I) :
    T v ∈ (energyOperator I V C κ' hκ' M' hbound' e').domain ↔ v ∈ (D).domain :=
  (PhysicalPFRadiation.normalEnergy_operator_domain I V C κ' hκ' M' hbound' e' (T v)).trans
    (Iff.trans
      (Iff.intro
        (fun h : ∃ u : Reference I V, inclusion I V u = T v =>
          Exists.elim h fun u hu =>
            Exists.imp (fun u' (hu' : inclusion I V u' = T' (inclusion I V u)) =>
              hu'.trans ((congrArg T' hu).trans (hinv v))) (hT' u))
        (fun h : ∃ u : Reference I V, inclusion I V u = v =>
          Exists.elim h fun u hu =>
            Exists.imp (fun u' (hu' : inclusion I V u' = T (inclusion I V u)) =>
              hu'.trans (congrArg T hu)) (hT u)))
      (PhysicalPFRadiation.normalEnergy_operator_domain I V C κ hκ M hbound e v).symm)

/-- `v ↦ D' (T v)` as a linear map on the form domain of `D`. -/
def transport (T : WaveSpace I →ₗ[ℂ] WaveSpace I)
    (hT : ∀ v : (D).domain, T v ∈ (energyOperator I V C κ' hκ' M' hbound' e').domain) :
    (D).domain →ₗ[ℂ] EnergyOutput I :=
  (energyOperator I V C κ' hκ' M' hbound' e').toFun.comp
    (LinearMap.codRestrict (energyOperator I V C κ' hκ' M' hbound' e').domain
      (T.comp (D).domain.subtype) hT)

theorem transport_apply (T : WaveSpace I →ₗ[ℂ] WaveSpace I)
    (hT : ∀ v : (D).domain, T v ∈ (energyOperator I V C κ' hκ' M' hbound' e').domain)
    (v : (D).domain) :
    transport V C κ hκ M hbound e κ' hκ' M' hbound' e' T hT v =
      energyOperator I V C κ' hκ' M' hbound' e' ⟨T v, hT v⟩ := rfl

/-- The kinetic part `½ ∑ᵢ ⟪Dᵢ v, Dᵢ w⟫` of the closed form. -/
def kineticForm (v w : (D).domain) : ℂ := ∑ i, ⟪D v (Sum.inl i), D w (Sum.inl i)⟫_ℂ

/-- The radiation part `⟪√H_rad v, √H_rad w⟫` of the closed form. -/
def radiationForm (v w : (D).domain) : ℂ := ⟪D v (Sum.inr 0), D w (Sum.inr 0)⟫_ℂ

/-- The Coulomb part of the closed form. -/
def coulombForm (v w : (D).domain) : ℂ := ⟪D v (Sum.inr 1), D w (Sum.inr 1)⟫_ℂ

/-- The closed form is the sum of its kinetic, radiation and Coulomb parts. -/
theorem form_eq_parts (v w : (D).domain) :
    ⟪D v, D w⟫_ℂ = kineticForm V C κ hκ M hbound e v w + radiationForm V C κ hκ M hbound e v w +
      coulombForm V C κ hκ M hbound e v w :=
  inner_output _ _

end Domain

/-- Bounded real external potentials on configuration space: a vector
potential with one component for each configuration coordinate and a scalar
potential. -/
structure BoundedPotential (I : Type) [Fintype I] [DecidableEq I] where
  vector : I → Position I → ℝ
  scalar : Position I → ℝ
  vector_measurable : ∀ i, Measurable (vector i)
  scalar_measurable : Measurable scalar
  vectorBound : ℝ
  scalarBound : ℝ
  vector_bounded : ∀ i x, |vector i x| ≤ vectorBound
  scalar_bounded : ∀ x, |scalar x| ≤ scalarBound

namespace BoundedPotential

variable (P : BoundedPotential I)

/-- Multiplication by the vector-potential component `a i`. -/
def vectorMultiplier (i : I) : WaveSpace I →L[ℂ] WaveSpace I :=
  PhotonLocalization.realL2Multiplier (P.vector i) (P.vector_measurable i).aestronglyMeasurable
    P.vectorBound (ae_of_all _ (P.vector_bounded i))

/-- Multiplication by the scalar potential. -/
def scalarMultiplier : WaveSpace I →L[ℂ] WaveSpace I :=
  PhotonLocalization.realL2Multiplier P.scalar P.scalar_measurable.aestronglyMeasurable
    P.scalarBound (ae_of_all _ P.scalar_bounded)

theorem vectorMultiplier_ae (i : I) (v : WaveSpace I) :
    P.vectorMultiplier i v =ᵐ[volume] fun x => P.vector i x • v x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ v

theorem scalarMultiplier_ae (v : WaveSpace I) :
    P.scalarMultiplier v =ᵐ[volume] fun x => P.scalar x • v x :=
  PhotonLocalization.realL2Multiplier_apply _ _ _ _ v

/-- The external part `B_a` of the form coordinates. -/
def output : WaveSpace I →L[ℂ] EnergyOutput I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I ⊕ Fin 2 => WaveSpace I)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim
      (fun i => (Real.sqrt (1 / 2 : ℝ) : ℂ) • P.vectorMultiplier i)
      (fun _ : Fin 2 => 0)))

theorem output_inl (v : WaveSpace I) (i : I) :
    P.output v (Sum.inl i) = (Real.sqrt (1 / 2 : ℝ) : ℂ) • P.vectorMultiplier i v := rfl

theorem output_inr (v : WaveSpace I) (n : Fin 2) : P.output v (Sum.inr n) = 0 := rfl

/-- The opposite vector potential with the same scalar potential, for `H^{v,-A}`. -/
def negVector : BoundedPotential I where
  vector i x := -P.vector i x
  scalar := P.scalar
  vector_measurable i := (P.vector_measurable i).neg
  scalar_measurable := P.scalar_measurable
  vectorBound := P.vectorBound
  scalarBound := P.scalarBound
  vector_bounded i x := (abs_neg (P.vector i x)).trans_le (P.vector_bounded i x)
  scalar_bounded := P.scalar_bounded

/-- The zero potential. -/
def zero : BoundedPotential I where
  vector _ _ := 0
  scalar _ := 0
  vector_measurable _ := measurable_const
  scalar_measurable := measurable_const
  vectorBound := 0
  scalarBound := 0
  vector_bounded _ _ := by simp
  scalar_bounded _ := by simp

end BoundedPotential

section External

variable (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M) (e : ℝ)

set_option hygiene false in
local notation "D" => energyOperator I V C κ hκ M hbound e

/-- The closed form of `H^{w,a}` for bounded external potentials, on the form
domain `𝒬_PF`. -/
def externalForm (P : BoundedPotential I) (v w : (D).domain) : ℂ :=
  ⟪D v + P.output v, D w + P.output w⟫_ℂ + ⟪(v : WaveSpace I), P.scalarMultiplier w⟫_ℂ

/-- With zero external potentials the closed form is the internal form `⟪D v, D w⟫`. -/
theorem externalForm_zero (v w : (D).domain) :
    externalForm V C κ hκ M hbound e BoundedPotential.zero v w = ⟪D v, D w⟫_ℂ := by
  have ho (x : WaveSpace I) : (BoundedPotential.zero : BoundedPotential I).output x = 0 := by
    apply PiLp.ext
    intro z
    rcases z with i | n
    · refine ((BoundedPotential.zero : BoundedPotential I).output_inl x i).trans ?_
      refine (congrArg (fun y => (Real.sqrt (1 / 2 : ℝ) : ℂ) • y) ?_).trans (smul_zero _)
      apply Lp.ext
      filter_upwards [(BoundedPotential.zero : BoundedPotential I).vectorMultiplier_ae i x,
        Lp.coeFn_zero (E := PhotonFock) (p := 2) (μ := volume)] with y h₁ h₂
      exact h₁.trans ((zero_smul ℝ (x y)).trans h₂.symm)
    · exact (BoundedPotential.zero : BoundedPotential I).output_inr x n
  have hs (x : WaveSpace I) : (BoundedPotential.zero : BoundedPotential I).scalarMultiplier x = 0 := by
    apply Lp.ext
    filter_upwards [(BoundedPotential.zero : BoundedPotential I).scalarMultiplier_ae x,
      Lp.coeFn_zero (E := PhotonFock) (p := 2) (μ := volume)] with y h₁ h₂
    exact h₁.trans ((zero_smul ℝ (x y)).trans h₂.symm)
  calc externalForm V C κ hκ M hbound e BoundedPotential.zero v w
      = ⟪D v + 0, D w + 0⟫_ℂ + ⟪(v : WaveSpace I), (0 : WaveSpace I)⟫_ℂ :=
        congrArg₂ (· + ·) (congrArg₂ (fun a b : EnergyOutput I => ⟪D v + a, D w + b⟫_ℂ)
          (ho v) (ho w)) (congrArg (fun c : WaveSpace I => ⟪(v : WaveSpace I), c⟫_ℂ) (hs w))
    _ = ⟪D v, D w⟫_ℂ :=
        (congrArg₂ (· + ·) (congrArg₂ (fun a b : EnergyOutput I => ⟪a, b⟫_ℂ) (add_zero _)
          (add_zero _)) (inner_zero_right _)).trans (add_zero _)

end External

end GptLean.TransformationsClosedForm
