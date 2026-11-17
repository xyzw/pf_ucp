import GptLean.TransformationsFockPointwise
import GptLean.ElectronicH1Map
import GptLean.PhysicalPFReference

/-!
Antiunitary fibre maps on the actual common Pauli--Fierz reference domain.

Let `W` be an antiunitary map of the photon Fock space with a compatible
antiunitary map `Wr` of the radiation graph. Applied pointwise in the
electronic configuration, `(Θ Ψ)(x) = W (Ψ(x))` is a real-linear,
conjugate-linear isometry of electronic L². It commutes with all weak
electronic derivatives, so it preserves the electronic H1 graph, and it
preserves the radiation and Coulomb graphs, hence the reference domain.
Because `Θ` is antilinear, `Θ (-i ∂) = i ∂ Θ`. If the field kernels are odd,
`W A(x) = - A(x) W`, then the covariant derivatives are odd,
`D (Θ u) = - Θ (D u)`, and the Pauli--Fierz energy is invariant. With
`W = Γ(-J)` this is the time reversal of `prop-time-reversal`.
-/

noncomputable section

namespace GptLean.TransformationsTimeReversal

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsFock
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

section Real

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- A conjugate-linear isometry is real linear. -/
def realCLM (W : F ≃ₗᵢ⋆[ℂ] F') : F →L[ℝ] F' where
  toFun := W
  map_add' := map_add W
  map_smul' r x := by
    change W (r • x) = r • W x
    rw [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
  cont := W.continuous

@[simp] theorem realCLM_apply (W : F ≃ₗᵢ⋆[ℂ] F') (x : F) : realCLM W x = W x := rfl

end Real

variable {I : Type} [Fintype I] [DecidableEq I]

section Wave

variable (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)

/-- Pointwise application of the antiunitary `W` to a wave function. -/
def antiWave (v : WaveSpace I) : WaveSpace I := (realCLM W).compLpL 2 volume v

theorem antiWave_ae (v : WaveSpace I) : antiWave W v =ᵐ[volume] fun x => W (v x) :=
  (realCLM W).coeFn_compLpL v

theorem antiWave_add (v w : WaveSpace I) : antiWave W (v + w) = antiWave W v + antiWave W w :=
  map_add ((realCLM W).compLpL 2 volume) v w

theorem antiWave_sub (v w : WaveSpace I) : antiWave W (v - w) = antiWave W v - antiWave W w :=
  map_sub ((realCLM W).compLpL 2 volume) v w

theorem antiWave_neg (v : WaveSpace I) : antiWave W (-v) = -antiWave W v :=
  map_neg ((realCLM W).compLpL 2 volume) v

theorem antiWave_smul (a : ℂ) (v : WaveSpace I) :
    antiWave W (a • v) = (starRingEnd ℂ a) • antiWave W v := by
  apply Lp.ext
  filter_upwards [antiWave_ae W (a • v), Lp.coeFn_smul a v,
    Lp.coeFn_smul (starRingEnd ℂ a) (antiWave W v), antiWave_ae W v] with x h₁ h₂ h₃ h₄
  refine h₁.trans ((congrArg W h₂).trans ((map_smulₛₗ W a (v x)).trans ?_))
  exact (congrArg (fun z => (starRingEnd ℂ a) • z) h₄.symm).trans h₃.symm

theorem norm_antiWave (v : WaveSpace I) : ‖antiWave W v‖ = ‖v‖ := by
  have h : eLpNorm (antiWave W v) 2 volume = eLpNorm v 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [antiWave_ae W v] with x hx
    exact (congrArg norm hx).trans (W.norm_map (v x))
  exact congrArg ENNReal.toReal h

theorem antiWave_symm (v : WaveSpace I) : antiWave W.symm (antiWave W v) = v := by
  apply Lp.ext
  filter_upwards [antiWave_ae W.symm (antiWave W v), antiWave_ae W v] with x h₁ h₂
  exact h₁.trans ((congrArg W.symm h₂).trans (W.symm_apply_apply (v x)))

theorem antiWave_symm_left (v : WaveSpace I) : antiWave W (antiWave W.symm v) = v := by
  apply Lp.ext
  filter_upwards [antiWave_ae W (antiWave W.symm v), antiWave_ae W.symm v] with x h₁ h₂
  exact h₁.trans ((congrArg W h₂).trans (W.apply_symm_apply (v x)))

/-- The electronic H1 graph map. -/
def antiH1 (w : ElectronicGraph I) : ElectronicGraph I :=
  ⟨(antiWave W (ElectronicH1Complex.value w),
      fun i => antiWave W (ElectronicH1Complex.derivative i w)),
    (Repair.weakH1Local_map (realCLM W) (ElectronicH1Complex.weak w)).congr
      ((realCLM W).coeFn_compLpL (ElectronicH1Complex.value w)).symm
      (fun i => ((realCLM W).coeFn_compLpL (ElectronicH1Complex.derivative i w)).symm)⟩

theorem value_antiH1 (w : ElectronicGraph I) :
    ElectronicH1Complex.value (antiH1 W w) = antiWave W (ElectronicH1Complex.value w) := rfl

theorem derivative_antiH1 (i : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative i (antiH1 W w) =
      antiWave W (ElectronicH1Complex.derivative i w) := rfl

end Wave

section Reference

variable (W : PhotonFock ≃ₗᵢ⋆[ℂ] PhotonFock)
  (Wr : RadiationGraphSpace ≃ₗᵢ⋆[ℂ] RadiationGraphSpace)
  (hincl : ∀ q, radiationGraphInclusion (Wr q) = W (radiationGraphInclusion q))
  (hderiv : ∀ q, radiationGraphDerivative (Wr q) = W (radiationGraphDerivative q))

/-- Pointwise application of `Wr` to a spatial radiation-graph vector. -/
def antiRadiation (r : RadiationGraph I) : RadiationGraph I :=
  (realCLM Wr).compLpL 2 volume r

include hincl in
theorem inclusion_antiRadiation (r : RadiationGraph I) :
    spatialRadiationInclusion volume (antiRadiation Wr r) =
      antiWave W (spatialRadiationInclusion volume r) := by
  apply Lp.ext
  filter_upwards [radiationGraphInclusion.coeFn_compLpL (antiRadiation Wr r),
    (realCLM Wr).coeFn_compLpL r, antiWave_ae W (spatialRadiationInclusion volume r),
    radiationGraphInclusion.coeFn_compLpL r] with x h₁ h₂ h₃ h₄
  refine h₁.trans ((congrArg radiationGraphInclusion h₂).trans ((hincl (r x)).trans ?_))
  exact (congrArg W h₄.symm).trans h₃.symm

include hderiv in
theorem derivative_antiRadiation (r : RadiationGraph I) :
    spatialRadiationDerivative volume (antiRadiation Wr r) =
      antiWave W (spatialRadiationDerivative volume r) := by
  apply Lp.ext
  filter_upwards [radiationGraphDerivative.coeFn_compLpL (antiRadiation Wr r),
    (realCLM Wr).coeFn_compLpL r, antiWave_ae W (spatialRadiationDerivative volume r),
    radiationGraphDerivative.coeFn_compLpL r] with x h₁ h₂ h₃ h₄
  refine h₁.trans ((congrArg radiationGraphDerivative h₂).trans ((hderiv (r x)).trans ?_))
  exact (congrArg W h₄.symm).trans h₃.symm

variable (V : Position I → ℝ)

theorem antiPotential_mem (p : PotentialGraph I V) :
    ((antiWave W p.val.1, antiWave W p.val.2) : WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun x => (Real.sqrt (V x) : ℂ)) := by
  have hp : ∀ᵐ x ∂volume, p.val.2 x = (Real.sqrt (V x) : ℂ) • p.val.1 x := p.property
  change ∀ᵐ x ∂volume, antiWave W p.val.2 x = (Real.sqrt (V x) : ℂ) • antiWave W p.val.1 x
  filter_upwards [hp, antiWave_ae W p.val.1, antiWave_ae W p.val.2] with x hx h₁ h₂
  refine h₂.trans ((congrArg W hx).trans ((map_smulₛₗ W _ _).trans ?_))
  refine (congrArg (fun a : ℂ => a • W (p.val.1 x)) (Complex.conj_ofReal _)).trans ?_
  exact congrArg (fun z : PhotonFock => (Real.sqrt (V x) : ℂ) • z) h₁.symm

/-- The Coulomb-graph map. -/
def antiPotential (p : PotentialGraph I V) : PotentialGraph I V :=
  ⟨(antiWave W p.val.1, antiWave W p.val.2), antiPotential_mem W V p⟩

/-- The pointwise antiunitary on the common reference domain. -/
def reverse (u : Reference I V) : Reference I V :=
  ⟨(antiH1 W (electronic I V u), antiRadiation Wr (radiationSource I V u),
      antiPotential W V (potentialSource I V u)), by
    change (ElectronicH1Complex.value (antiH1 W (electronic I V u)) -
        spatialRadiationInclusion volume (antiRadiation Wr (radiationSource I V u)),
      ElectronicH1Complex.value (antiH1 W (electronic I V u)) -
        antiWave W (potentialSource I V u).val.1) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((congrArg (antiWave W) (radiation_matches I V u).symm).trans
        (inclusion_antiRadiation W Wr hincl (radiationSource I V u)).symm)
    · exact sub_eq_zero.mpr (congrArg (antiWave W) (potential_matches I V u).symm)⟩

theorem inclusion_reverse (u : Reference I V) :
    inclusion I V (reverse W Wr hincl V u) = antiWave W (inclusion I V u) := rfl

theorem ordinary_reverse (i : I) (u : Reference I V) :
    ordinary I V i (reverse W Wr hincl V u) = antiWave W (ordinary I V i u) := rfl

include hderiv in
theorem radiation_reverse (u : Reference I V) :
    radiation I V (reverse W Wr hincl V u) = antiWave W (radiation I V u) :=
  derivative_antiRadiation W Wr hderiv (radiationSource I V u)

theorem potential_reverse (u : Reference I V) :
    potential I V (reverse W Wr hincl V u) = antiWave W (potential I V u) := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hodd : ∀ i x q, kernelField C (κ i x) (Wr q) = -W (kernelField C (κ i x) q))

include hodd in
/-- Odd field kernels make the field odd under the antiunitary. -/
theorem field_reverse (i : I) (u : Reference I V) :
    field I V C κ hκ M hbound i (reverse W Wr hincl V u) =
      -antiWave W (field I V C κ hκ M hbound i u) := by
  apply Lp.ext
  filter_upwards [spatialField_ae volume C (κ i) (hκ i) M (hbound i)
      (antiRadiation Wr (radiationSource I V u)),
    (realCLM Wr).coeFn_compLpL (radiationSource I V u),
    Lp.coeFn_neg (antiWave W (field I V C κ hκ M hbound i u)),
    antiWave_ae W (field I V C κ hκ M hbound i u),
    spatialField_ae volume C (κ i) (hκ i) M (hbound i) (radiationSource I V u)]
    with x h₁ h₂ h₃ h₄ h₅
  change spatialField volume C (κ i) (hκ i) M (hbound i)
      (antiRadiation Wr (radiationSource I V u)) x = _
  refine h₁.trans ((congrArg (kernelField C (κ i x)) h₂).trans ((hodd i x _).trans ?_))
  refine Eq.trans ?_ h₃.symm
  exact congrArg Neg.neg ((congrArg W h₅.symm).trans h₄.symm)

private theorem covariant_algebra {E : Type*} [AddCommGroup E] [Module ℂ E] (L : E → E)
    (hsub : ∀ a b, L (a - b) = L a - L b) (hsmul : ∀ (c : ℂ) a, L (c • a) = starRingEnd ℂ c • L a)
    (d f : E) (e : ℝ) :
    (-Complex.I) • L d - (e : ℂ) • -L f = -L ((-Complex.I) • d - (e : ℂ) • f) := by
  rw [hsub, hsmul, hsmul, map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal]
  simp only [smul_neg, neg_smul, sub_neg_eq_add, neg_sub]
  abel

include hodd in
/-- The covariant derivatives are odd, `D (Θ u) = - Θ (D u)`. -/
theorem covariant_reverse (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i (reverse W Wr hincl V u) =
      -antiWave W (covariant I V C κ hκ M hbound e i u) :=
  (covariant_apply I V C κ hκ M hbound e i (reverse W Wr hincl V u)).trans
    ((congrArg₂ (fun a b : WaveSpace I => (-Complex.I) • a - (e : ℂ) • b)
      (ordinary_reverse W Wr hincl V i u)
      (field_reverse W Wr hincl V C κ hκ M hbound hodd i u)).trans
      ((covariant_algebra (antiWave W) (antiWave_sub W) (antiWave_smul W)
        (ordinary I V i u) (field I V C κ hκ M hbound i u) e).trans
        (congrArg (fun z => -antiWave W z) (covariant_apply I V C κ hκ M hbound e i u).symm)))

include hodd hderiv in
/-- The antiunitary preserves the Pauli--Fierz energy. -/
theorem energy_reverse (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (reverse W Wr hincl V u) =
      energy I V C κ hκ M hbound e u := by
  have hk (i : I) : ‖covariant I V C κ hκ M hbound e i (reverse W Wr hincl V u)‖ =
      ‖covariant I V C κ hκ M hbound e i u‖ :=
    (congrArg norm (covariant_reverse W Wr hincl V C κ hκ M hbound hodd e i u)).trans
      ((norm_neg _).trans (norm_antiWave W _))
  have hr : ‖radiation I V (reverse W Wr hincl V u)‖ = ‖radiation I V u‖ :=
    (congrArg norm (radiation_reverse W Wr hincl hderiv V u)).trans (norm_antiWave W _)
  have hp : ‖potential I V (reverse W Wr hincl V u)‖ = ‖potential I V u‖ :=
    norm_antiWave W _
  unfold energy kineticEnergy
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun i _ =>
      congrArg (· ^ 2) (hk i))) (congrArg (· ^ 2) hr)) (congrArg (· ^ 2) hp)

end Reference

end GptLean.TransformationsTimeReversal
