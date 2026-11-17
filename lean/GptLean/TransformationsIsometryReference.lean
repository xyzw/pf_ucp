import GptLean.TransformationsFockFamily
import GptLean.TransformationsTranslationReference

/-!
Affine isometries on the actual common Pauli--Fierz reference domain.

Let `A x = L x + c` be an affine isometry of configuration space and `Γ` the
second quantization of a dispersive sector family (`TransformationsFockFamily`).
If the potential is invariant, `V ∘ A = V`, the map

`(T Ψ)(x) = Γ Ψ(A x)`

acts on the three graph coordinates of the reference domain. By the chain rule
the ordinary derivatives mix with the coefficient matrix `cᵢⱼ = (L eᵢ)ⱼ`:

`∂ᵢ (T Ψ) = ∑ⱼ cᵢⱼ T (∂ⱼ Ψ)`.

If the field kernels satisfy `κᵢ(x) = ∑ⱼ cᵢⱼ Γ κⱼ(A x)`, the fields and the
covariant derivatives mix in the same way. The coefficient matrix is
orthogonal, so `T` preserves the kinetic, radiation and Coulomb energies.
With `A` a simultaneous rotation of all electrons and `Γ` the photon rotation
this gives `prop-orthogonal-covariance`.
-/

noncomputable section

namespace GptLean.TransformationsIsometry

open MeasureTheory PhysicalFock PhysicalPFReference TransformationsAffine TransformationsFock
open scoped ENNReal InnerProductSpace

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

local instance radiationNormedSpace : NormedSpace ℂ RadiationGraphSpace :=
  radiationRoot.graph.normedSpace

section Algebra

/-- Real orthogonal mixing preserves the sum of squared norms. -/
theorem sum_norm_sq_mix {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (c : ι → ι → ℝ)
    (hc : ∀ j k, ∑ i, c i j * c i k = if j = k then 1 else 0) (w : ι → E) :
    ∑ i, ‖∑ j, ((c i j : ℝ) : ℂ) • w j‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
  have hn (x : E) : ‖x‖ ^ 2 = RCLike.re (⟪x, x⟫_ℂ) := (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have hinner (i : ι) : ⟪∑ j, ((c i j : ℝ) : ℂ) • w j, ∑ k, ((c i k : ℝ) : ℂ) • w k⟫_ℂ =
      ∑ j, ∑ k, ((c i j * c i k : ℝ) : ℂ) * ⟪w j, w k⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  have hsum : ∑ i, ∑ j, ∑ k, ((c i j * c i k : ℝ) : ℂ) * ⟪w j, w k⟫_ℂ = ∑ j, ⟪w j, w j⟫_ℂ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, hc, apply_ite (fun t : ℝ => (t : ℂ)),
      Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  simp only [hn, hinner]
  calc ∑ i, RCLike.re (∑ j, ∑ k, ((c i j * c i k : ℝ) : ℂ) * ⟪w j, w k⟫_ℂ)
      = RCLike.re (∑ i, ∑ j, ∑ k, ((c i j * c i k : ℝ) : ℂ) * ⟪w j, w k⟫_ℂ) :=
        (map_sum RCLike.re _ _).symm
    _ = RCLike.re (∑ j, ⟪w j, w j⟫_ℂ) := congrArg RCLike.re hsum
    _ = ∑ j, RCLike.re (⟪w j, w j⟫_ℂ) := map_sum RCLike.re _ _

/-- Mixing commutes with the affine combination defining a covariant derivative. -/
theorem mix_affine {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℂ E] (W : E →ₗ[ℂ] E)
    (c : ι → ℂ) (o f : ι → E) (e : ℂ) :
    (-Complex.I) • (∑ j, c j • W (o j)) - e • (∑ j, c j • W (f j)) =
      ∑ j, c j • W ((-Complex.I) • o j - e • f j) := by
  simp only [map_sub, map_smul, Finset.smul_sum, smul_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm (-Complex.I) (c j), smul_comm e (c j)]

theorem coeFn_finset_sum {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] {p : ℝ≥0∞} {ι : Type*} (s : Finset ι) (f : ι → Lp F p μ) :
    ⇑(∑ j ∈ s, f j) =ᵐ[μ] fun x => ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero F p μ] with x hx
    rw [Finset.sum_empty, hx, Finset.sum_empty]
    rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ j ∈ s, f j), ih] with x h₁ h₂
    rw [h₁, Pi.add_apply, h₂, Finset.sum_insert hj]

end Algebra

variable {I : Type} [Fintype I] [DecidableEq I] (A : AffineIsometry I)

/-- The chain-rule coefficients of an affine isometry form an orthogonal matrix. -/
theorem coefficient_orthogonal (j k : I) :
    ∑ i, A.coefficient i j * A.coefficient i k = if j = k then 1 else 0 := by
  have h (i m : I) : A.coefficient i m = A.linear.symm (EuclideanSpace.single m 1) i := by
    have h1 := A.linear.inner_map_eq_flip (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single m 1)
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
      one_mul, star_trivial, conj_trivial] at h1
    exact h1
  have h2 := A.linear.symm.inner_map_map (EuclideanSpace.single j (1 : ℝ))
    (EuclideanSpace.single k 1)
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, map_one, one_mul,
    PiLp.inner_apply] at h2
  simp only [h]
  refine Eq.trans ?_ h2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

section Lp

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- Pullback by the affine isometry on vector-valued L². -/
def pullL2 : Lp F 2 (volume : Measure (EuclideanSpace ℝ I)) →ₗᵢ[ℂ]
    Lp F 2 (volume : Measure (EuclideanSpace ℝ I)) :=
  Lp.compMeasurePreservingₗᵢ ℂ A.apply A.measurePreserving

theorem pullL2_ae (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    pullL2 A v =ᵐ[volume] fun x => v (A.apply x) :=
  Lp.coeFn_compMeasurePreserving v A.measurePreserving

theorem ae_pull {P : EuclideanSpace ℝ I → Prop} (h : ∀ᵐ x ∂volume, P x) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ I)), P (A.apply x) :=
  A.measurePreserving.quasiMeasurePreserving.ae h

theorem pullL2_compLpL (L : F →L[ℂ] F') (v : Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    pullL2 A (L.compLpL 2 volume v) = L.compLpL 2 volume (pullL2 A v) := by
  apply Lp.ext
  filter_upwards [pullL2_ae A (L.compLpL 2 volume v), ae_pull A (L.coeFn_compLpL v),
    L.coeFn_compLpL (pullL2 A v), pullL2_ae A v] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

end Lp

theorem pull_eq_pullL2 (v : WaveSpace I) : A.pull ℂ v = pullL2 A v := by
  apply Lp.ext
  filter_upwards [A.pull_ae ℂ v, pullL2_ae A v] with x h₁ h₂
  rw [h₁, h₂]

/-- The pullback of a real combination, pointwise. -/
theorem pull_real_sum_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [CompleteSpace F] (c : I → ℝ) (v : I → Lp F 2 (volume : Measure (EuclideanSpace ℝ I))) :
    A.pull ℂ (∑ j, c j • v j) =ᵐ[volume] fun x => ∑ j, c j • v j (A.apply x) := by
  filter_upwards [A.pull_ae ℂ (∑ j, c j • v j),
    ae_pull A (coeFn_finset_sum Finset.univ fun j => c j • v j),
    ae_pull A (ae_all_iff.mpr fun j => Lp.coeFn_smul (c j) (v j))] with x h₁ h₂ h₃
  rw [h₁, h₂]
  exact Finset.sum_congr rfl fun j _ => h₃ j

variable (G : SectorFamily photonMeasure) (hG : G.Dispersive)

/-- The Fock unitary `Γ`. -/
def fockCLM : PhotonFock →L[ℂ] PhotonFock := G.fock.toLinearIsometry.toContinuousLinearMap

/-- The induced map of the radiation graph. -/
def radiationCLM : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  (G.radiationGraph hG).toLinearIsometry.toContinuousLinearMap

theorem radiationGraphInclusion_comp :
    radiationGraphInclusion.comp (radiationCLM G hG) = (fockCLM G).comp radiationGraphInclusion :=
  ContinuousLinearMap.ext fun q => G.radiationGraphInclusion_radiationGraph hG q

theorem radiationGraphDerivative_comp :
    radiationGraphDerivative.comp (radiationCLM G hG) =
      (fockCLM G).comp radiationGraphDerivative :=
  ContinuousLinearMap.ext fun q => G.radiationGraphDerivative_radiationGraph hG q

/-- `(T v)(x) = Γ v(A x)` on the physical wave space. -/
def waveMap : WaveSpace I →L[ℂ] WaveSpace I :=
  (pullL2 A).toContinuousLinearMap.comp ((fockCLM G).compLpL 2 volume)

theorem waveMap_apply (v : WaveSpace I) :
    waveMap A G v = pullL2 A ((fockCLM G).compLpL 2 volume v) := rfl

theorem waveMap_ae (v : WaveSpace I) :
    waveMap A G v =ᵐ[volume] fun x => G.fock (v (A.apply x)) := by
  filter_upwards [pullL2_ae A ((fockCLM G).compLpL 2 volume v),
    ae_pull A ((fockCLM G).coeFn_compLpL v)] with x h₁ h₂
  exact h₁.trans h₂

theorem norm_fockCompLpL (v : WaveSpace I) : ‖(fockCLM G).compLpL 2 volume v‖ = ‖v‖ := by
  have h : eLpNorm ((fockCLM G).compLpL 2 volume v) 2 volume = eLpNorm v 2 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [(fockCLM G).coeFn_compLpL v] with x hx
    exact (congrArg norm hx).trans (G.fock.norm_map (v x))
  exact congrArg ENNReal.toReal h

theorem norm_waveMap (v : WaveSpace I) : ‖waveMap A G v‖ = ‖v‖ :=
  ((pullL2 A).norm_map _).trans (norm_fockCompLpL G v)

/-- The inverse isometry with the inverse family inverts `waveMap`. -/
theorem waveMap_inv (v : WaveSpace I) : waveMap A.inv G.symm (waveMap A G v) = v := by
  apply Lp.ext
  filter_upwards [waveMap_ae A.inv G.symm (waveMap A G v), ae_pull A.inv (waveMap_ae A G v)]
    with x h₁ h₂
  refine h₁.trans ((congrArg G.symm.fock h₂).trans ?_)
  refine (G.symm_fock _).trans ?_
  refine (congrArg (fun y => G.fock.symm (G.fock (v y))) (A.apply_inv_apply x)).trans ?_
  exact G.fock.symm_apply_apply (v x)

theorem waveMap_inv_left (v : WaveSpace I) : waveMap A G (waveMap A.inv G.symm v) = v := by
  apply Lp.ext
  filter_upwards [waveMap_ae A G (waveMap A.inv G.symm v), ae_pull A (waveMap_ae A.inv G.symm v)]
    with x h₁ h₂
  refine h₁.trans ((congrArg G.fock h₂).trans ?_)
  refine (congrArg G.fock (G.symm_fock _)).trans ?_
  refine (congrArg (fun y => G.fock (G.fock.symm (v y))) (A.inv_apply_apply x)).trans ?_
  exact G.fock.apply_symm_apply (v x)

/-! ### The three graph coordinates -/

/-- The electronic graph map `w ↦ (Γ w)(A ·)`. -/
def electronicMap (w : ElectronicGraph I) : ElectronicGraph I :=
  A.pullH1 (ElectronicH1Map.map (fockCLM G) w)

theorem value_electronicMap (w : ElectronicGraph I) :
    ElectronicH1Complex.value (electronicMap A G w) =
      waveMap A G (ElectronicH1Complex.value w) := rfl

theorem derivative_map_ae (j : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative j (ElectronicH1Map.map (fockCLM G) w) =ᵐ[volume]
      fun x => G.fock (ElectronicH1Complex.derivative j w x) :=
  (fockCLM G).coeFn_compLpL (ElectronicH1Complex.derivative j w)

theorem derivative_electronicMap_pull (i : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative i (electronicMap A G w) =
      A.pull ℂ (∑ j, A.coefficient i j •
        ElectronicH1Complex.derivative j (ElectronicH1Map.map (fockCLM G) w)) :=
  AffineIsometry.derivative_pullH1 A i (ElectronicH1Map.map (fockCLM G) w)

/-- The chain rule with mixing coefficients. -/
theorem derivative_electronicMap (i : I) (w : ElectronicGraph I) :
    ElectronicH1Complex.derivative i (electronicMap A G w) =
      ∑ j, ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (ElectronicH1Complex.derivative j w) := by
  refine (derivative_electronicMap_pull A G i w).trans ?_
  apply Lp.ext
  have hc : ∀ᵐ x ∂volume, ∀ j, (((A.coefficient i j : ℝ) : ℂ) •
      waveMap A G (ElectronicH1Complex.derivative j w)) x =
        ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (ElectronicH1Complex.derivative j w) x :=
    ae_all_iff.mpr fun j => Lp.coeFn_smul _ _
  have hd : ∀ᵐ x ∂volume, ∀ j,
      ElectronicH1Complex.derivative j (ElectronicH1Map.map (fockCLM G) w) x =
        G.fock (ElectronicH1Complex.derivative j w x) :=
    ae_all_iff.mpr fun j => derivative_map_ae G j w
  have hw : ∀ᵐ x ∂volume, ∀ j, waveMap A G (ElectronicH1Complex.derivative j w) x =
      G.fock (ElectronicH1Complex.derivative j w (A.apply x)) :=
    ae_all_iff.mpr fun j => waveMap_ae A G _
  have hp := pull_real_sum_ae A (fun j => A.coefficient i j)
    (fun j => ElectronicH1Complex.derivative j (ElectronicH1Map.map (fockCLM G) w))
  filter_upwards [hp, ae_pull A hd, coeFn_finset_sum Finset.univ fun j =>
      ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (ElectronicH1Complex.derivative j w), hc, hw]
    with x h₁ h₂ h₃ h₄ h₅
  refine h₁.trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h₃.symm)
  refine (congrArg (fun y => A.coefficient i j • y) (h₂ j)).trans ?_
  refine Eq.trans ?_ (h₄ j).symm
  refine Eq.trans ?_ (congrArg (fun y => ((A.coefficient i j : ℝ) : ℂ) • y) (h₅ j).symm)
  exact (Complex.coe_smul _ _).symm

/-- The radiation-graph map `r ↦ (Γ r)(A ·)`. -/
def radiationMap (r : RadiationGraph I) : RadiationGraph I :=
  pullL2 A ((radiationCLM G hG).compLpL 2 volume r)

theorem inclusion_radiationMap (r : RadiationGraph I) :
    spatialRadiationInclusion volume (radiationMap A G hG r) =
      waveMap A G (spatialRadiationInclusion volume r) :=
  ((pullL2_compLpL A radiationGraphInclusion ((radiationCLM G hG).compLpL 2 volume r)).symm.trans
    (congrArg (pullL2 A) ((ElectronicH1Map.compLpL_comp radiationGraphInclusion
      (radiationCLM G hG) r).trans ((congrArg (fun L => L.compLpL 2 volume r)
        (radiationGraphInclusion_comp G hG)).trans
          (ElectronicH1Map.compLpL_comp (fockCLM G) radiationGraphInclusion r).symm))))

theorem derivative_radiationMap (r : RadiationGraph I) :
    spatialRadiationDerivative volume (radiationMap A G hG r) =
      waveMap A G (spatialRadiationDerivative volume r) :=
  ((pullL2_compLpL A radiationGraphDerivative ((radiationCLM G hG).compLpL 2 volume r)).symm.trans
    (congrArg (pullL2 A) ((ElectronicH1Map.compLpL_comp radiationGraphDerivative
      (radiationCLM G hG) r).trans ((congrArg (fun L => L.compLpL 2 volume r)
        (radiationGraphDerivative_comp G hG)).trans
          (ElectronicH1Map.compLpL_comp (fockCLM G) radiationGraphDerivative r).symm))))

theorem radiationMap_ae (r : RadiationGraph I) :
    radiationMap A G hG r =ᵐ[volume] fun x => G.radiationGraph hG (r (A.apply x)) := by
  unfold radiationMap
  filter_upwards [pullL2_ae A ((radiationCLM G hG).compLpL 2 volume r),
    ae_pull A ((radiationCLM G hG).coeFn_compLpL r)] with x h₁ h₂
  exact h₁.trans h₂

variable (V : Position I → ℝ) (hV : ∀ x, V (A.apply x) = V x)

include hV in
theorem potentialMap_mem (p : PotentialGraph I V) :
    ((waveMap A G p.val.1, waveMap A G p.val.2) : WaveSpace I × WaveSpace I) ∈
      PhysicalMultiplicationGraph.graph volume (H := PhotonFock)
        (fun x => (Real.sqrt (V x) : ℂ)) := by
  have hp : ∀ᵐ x ∂volume, p.val.2 x = (Real.sqrt (V x) : ℂ) • p.val.1 x := p.property
  change ∀ᵐ x ∂volume, waveMap A G p.val.2 x = (Real.sqrt (V x) : ℂ) • waveMap A G p.val.1 x
  filter_upwards [ae_pull A hp, waveMap_ae A G p.val.1, waveMap_ae A G p.val.2]
    with x hx h₁ h₂
  refine h₂.trans ((congrArg G.fock hx).trans ((map_smul G.fock _ _).trans ?_))
  refine (congrArg (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) • G.fock (p.val.1 (A.apply x)))
    (hV x)).trans ?_
  exact congrArg (fun z : PhotonFock => (Real.sqrt (V x) : ℂ) • z) h₁.symm

/-- The Coulomb-graph map. -/
def potentialMap (p : PotentialGraph I V) : PotentialGraph I V :=
  ⟨(waveMap A G p.val.1, waveMap A G p.val.2), potentialMap_mem A G V hV p⟩

/-- The isometric change of variables on the common reference domain. -/
def isoMap (u : Reference I V) : Reference I V :=
  ⟨(electronicMap A G (electronic I V u), radiationMap A G hG (radiationSource I V u),
      potentialMap A G V hV (potentialSource I V u)), by
    change (ElectronicH1Complex.value (electronicMap A G (electronic I V u)) -
        spatialRadiationInclusion volume (radiationMap A G hG (radiationSource I V u)),
      ElectronicH1Complex.value (electronicMap A G (electronic I V u)) -
        waveMap A G (potentialSource I V u).val.1) = (0, 0)
    apply Prod.ext
    · exact sub_eq_zero.mpr ((value_electronicMap A G (electronic I V u)).trans
        ((congrArg (waveMap A G) (radiation_matches I V u).symm).trans
          (inclusion_radiationMap A G hG (radiationSource I V u)).symm))
    · exact sub_eq_zero.mpr ((value_electronicMap A G (electronic I V u)).trans
        (congrArg (waveMap A G) (potential_matches I V u).symm))⟩

theorem inclusion_isoMap (u : Reference I V) :
    inclusion I V (isoMap A G hG V hV u) = waveMap A G (inclusion I V u) :=
  value_electronicMap A G (electronic I V u)

theorem ordinary_isoMap (i : I) (u : Reference I V) :
    ordinary I V i (isoMap A G hG V hV u) =
      ∑ j, ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (ordinary I V j u) :=
  derivative_electronicMap A G i (electronic I V u)

theorem radiation_isoMap (u : Reference I V) :
    radiation I V (isoMap A G hG V hV u) = waveMap A G (radiation I V u) :=
  derivative_radiationMap A G hG (radiationSource I V u)

theorem potential_isoMap (u : Reference I V) :
    potential I V (isoMap A G hG V hV u) = waveMap A G (potential I V u) := rfl

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : I → Position I → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume)
  (M : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hcov : ∀ i, ∀ᵐ x ∂volume,
    κ i x = ∑ j, A.coefficient i j • G.kernel hG (κ j (A.apply x)))

/-- The field is real linear in the kernel. -/
theorem kernelField_mix (c : I → ℝ) (k : I → WeightedPhotonKernel) (q : RadiationGraphSpace) :
    kernelField C (∑ j, c j • k j) q = ∑ j, ((c j : ℝ) : ℂ) • kernelField C (k j) q := by
  have h : kernelField C (∑ j, c j • k j) = ∑ j, c j • kernelField C (k j) :=
    (map_sum (kernelFieldMap C) (fun j => c j • k j) Finset.univ).trans
      (Finset.sum_congr rfl fun j _ => (kernelFieldMap C).map_smul (c j) (k j))
  refine (congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock => L q) h).trans ?_
  refine (ContinuousLinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact (ContinuousLinearMap.smul_apply _ _ _).trans (Complex.coe_smul _ _).symm

include hcov in
/-- Covariant field kernels make the fields mix like the derivatives. -/
theorem field_isoMap (i : I) (u : Reference I V) :
    field I V C κ hκ M hbound i (isoMap A G hG V hV u) =
      ∑ j, ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (field I V C κ hκ M hbound j u) := by
  apply Lp.ext
  have hf : ∀ᵐ x ∂volume, ∀ j, field I V C κ hκ M hbound j u (A.apply x) =
      kernelField C (κ j (A.apply x)) (radiationSource I V u (A.apply x)) :=
    ae_pull A (ae_all_iff.mpr fun j =>
      spatialField_ae volume C (κ j) (hκ j) M (hbound j) (radiationSource I V u))
  have hs : ∀ᵐ x ∂volume, ∀ j, (((A.coefficient i j : ℝ) : ℂ) •
      waveMap A G (field I V C κ hκ M hbound j u)) x =
        ((A.coefficient i j : ℝ) : ℂ) • waveMap A G (field I V C κ hκ M hbound j u) x :=
    ae_all_iff.mpr fun j => Lp.coeFn_smul _ _
  have hw : ∀ᵐ x ∂volume, ∀ j, waveMap A G (field I V C κ hκ M hbound j u) x =
      G.fock (field I V C κ hκ M hbound j u (A.apply x)) :=
    ae_all_iff.mpr fun j => waveMap_ae A G _
  filter_upwards [spatialField_ae volume C (κ i) (hκ i) M (hbound i)
      (radiationMap A G hG (radiationSource I V u)),
    radiationMap_ae A G hG (radiationSource I V u), hcov i,
    coeFn_finset_sum Finset.univ fun j => ((A.coefficient i j : ℝ) : ℂ) •
      waveMap A G (field I V C κ hκ M hbound j u), hs, hw, hf] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  change spatialField volume C (κ i) (hκ i) M (hbound i)
      (radiationMap A G hG (radiationSource I V u)) x = _
  refine h₁.trans ((congrArg₂ (fun k q => kernelField C k q) h₃ h₂).trans
    ((kernelField_mix C _ _ _).trans (Eq.trans ?_ h₄.symm)))
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Eq.trans ?_ (h₅ j).symm
  refine congrArg (fun z => ((A.coefficient i j : ℝ) : ℂ) • z) ?_
  exact (G.kernelField_kernel hG C _ _).trans ((congrArg G.fock (h₇ j).symm).trans (h₆ j).symm)

include hcov in
theorem covariant_isoMap (e : ℝ) (i : I) (u : Reference I V) :
    covariant I V C κ hκ M hbound e i (isoMap A G hG V hV u) =
      ∑ j, ((A.coefficient i j : ℝ) : ℂ) •
        waveMap A G (covariant I V C κ hκ M hbound e j u) :=
  (covariant_apply I V C κ hκ M hbound e i (isoMap A G hG V hV u)).trans
    ((congrArg₂ (fun a b : WaveSpace I => (-Complex.I) • a - (e : ℂ) • b)
      (ordinary_isoMap A G hG V hV i u)
      (field_isoMap A G hG V hV C κ hκ M hbound hcov i u)).trans
      ((mix_affine (waveMap A G).toLinearMap (fun j => ((A.coefficient i j : ℝ) : ℂ))
        (fun j => ordinary I V j u) (fun j => field I V C κ hκ M hbound j u) (e : ℂ)).trans
        (Finset.sum_congr rfl fun j _ =>
          congrArg (fun w => ((A.coefficient i j : ℝ) : ℂ) • waveMap A G w)
            (covariant_apply I V C κ hκ M hbound e j u).symm)))

include hcov in
/-- The isometric change of variables preserves the kinetic energy. -/
theorem kineticEnergy_isoMap (e : ℝ) (u : Reference I V) :
    kineticEnergy I V C κ hκ M hbound e (isoMap A G hG V hV u) =
      kineticEnergy I V C κ hκ M hbound e u := by
  unfold kineticEnergy
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
  refine (Finset.sum_congr rfl fun i _ =>
    congrArg (· ^ 2) (congrArg norm (covariant_isoMap A G hG V hV C κ hκ M hbound hcov e i u))).trans
    ((sum_norm_sq_mix A.coefficient (coefficient_orthogonal A) _).trans ?_)
  exact Finset.sum_congr rfl fun j _ => congrArg (· ^ 2) (norm_waveMap A G _)

include hcov in
/-- The isometric change of variables preserves the Pauli--Fierz energy. -/
theorem energy_isoMap (e : ℝ) (u : Reference I V) :
    energy I V C κ hκ M hbound e (isoMap A G hG V hV u) = energy I V C κ hκ M hbound e u := by
  have hr : ‖radiation I V (isoMap A G hG V hV u)‖ = ‖radiation I V u‖ :=
    (congrArg norm (radiation_isoMap A G hG V hV u)).trans (norm_waveMap A G _)
  have hp : ‖potential I V (isoMap A G hG V hV u)‖ = ‖potential I V u‖ :=
    norm_waveMap A G _
  unfold energy
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (kineticEnergy_isoMap A G hG V hV C κ hκ M hbound hcov e u) (congrArg (· ^ 2) hr))
    (congrArg (· ^ 2) hp)

include hV in
/-- The potential is invariant under the inverse isometry as well. -/
theorem potential_inv : ∀ x, V (A.inv.apply x) = V x := fun x =>
  (hV (A.inv.apply x)).symm.trans (congrArg V (A.apply_inv_apply x))

end GptLean.TransformationsIsometry
