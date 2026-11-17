import GptLean.PhysicalPFVacuumEnergy
import GptLean.RemovalVacuumForm

/-!
The actual PF forms satisfy the spatial vacuum form interface. The hard
covariant derivative is recovered from the same ambient reference vector
used by the normal energy. The full tensor norm identity is proved from
the orthogonal hard and soft kernel split.
-/

noncomputable section

namespace GptLean.PhysicalPFVacuumForm

open MeasureTheory Filter Topology PhysicalFock PhysicalPFReference
  PhysicalNormalTrace PhysicalPFVacuumInsertion PhysicalPFVacuumEnergy
  RemovalState RemovalVacuum
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false

section Generic

variable {X H J : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
private theorem kinetic_integrable (d : J → Lp H 2 μ) :
    Integrable (fun x => (1 / 2 : ℝ) * ∑ j, ‖d j x‖ ^ 2) μ :=
  (integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (d j))).mp
      (Lp.memLp (d j)))).const_mul _

private theorem kinetic_integral (d : J → Lp H 2 μ) :
    (∫ x, (1 / 2 : ℝ) * ∑ j, ‖d j x‖ ^ 2 ∂μ) =
      (1 / 2 : ℝ) * ∑ j, ‖d j‖ ^ 2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (d j))).mp
      (Lp.memLp (d j)))]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (PhotonKernelLocalization.l2_norm_sq_eq_integral (d j)).symm

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
private theorem kinetic_integral_congr (f g : J → X → ℝ)
    (h : ∀ j, f j =ᵐ[μ] g j) :
    (∫ x, (1 / 2 : ℝ) * ∑ j, f j x ∂μ) =
      ∫ x, (1 / 2 : ℝ) * ∑ j, g j x ∂μ := by
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (Finset.sum_congr rfl (fun j _ => hx j))

private theorem orthogonal_sub_norm_sq (u v : H) (h : ⟪u, v⟫_ℂ = 0) (e : ℝ) :
    ‖u - (e : ℂ) • v‖ ^ 2 = ‖u‖ ^ 2 + e ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, h, mul_zero, map_zero,
    mul_zero, sub_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private theorem vacuum_norm_match {K V : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ω χ : V) (hΩ : ‖Ω‖ = 1) (hχ : inner ℂ Ω χ = 0)
    (e : ℝ) (d ψ : K) (a b f : H)
    (hd : ‖d‖ = ‖a‖) (ho : inner ℂ a b = 0)
    (hb : ‖b‖ ^ 2 = ‖χ‖ ^ 2 * ‖ψ‖ ^ 2)
    (hf : f = a - (e : ℂ) • b) :
    ‖vacuumDerivative Ω χ e d ψ‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [vacuumDerivative_norm_sq Ω χ hΩ hχ e, hf,
    orthogonal_sub_norm_sq a b ho e, hd, hb]
  ring

end Generic

section Reference

variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (BF : StandardSymmetricFockExponential) (κ : ℝ)

/-- The reference preimage is used only when the inserted vector belongs to its range. -/
def reference (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position I))) : Reference I V := by
  classical
  exact if hv : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v then
    hv.choose else 0

theorem reference_value (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position I)))
    (hv : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v) :
    inclusion I V (reference I V BF κ v) = insertion volume BF κ v := by
  simp only [reference, dite_eq_left hv]
  exact hv.choose_spec

variable (C : CanonicalSectorCCR photonMeasure)
  (h : I → Position I → WeightedPhotonKernel)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (Mh : ℝ) (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh) (e : ℝ)

/-- The hard covariant derivative takes values in the actual generated hard fiber. -/
def derivative (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position I))) (i : I) :
    Position I → generatedFockSubspace (hardOnePhoton κ) :=
  fun x => (generatedFockSubspace (hardOnePhoton κ)).orthogonalProjectionOnto
    (covariant I V C h hh Mh hMh e i (reference I V BF κ v) x)

def rest (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position I))) : ℝ :=
  ‖radiation I V (reference I V BF κ v)‖ ^ 2 +
    ‖potential I V (reference I V BF κ v)‖ ^ 2

omit C h hh Mh hMh e in
theorem reference_supported (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
    (volume : Measure (Position I)))
    (hv : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v) :
    ∀ᵐ x ∂volume, inclusion I V (reference I V BF κ v) x ∈
      generatedFockSubspace (hardOnePhoton κ) :=
  reference_mem_of_insertion I V BF κ v _ (reference_value I V BF κ v hv)

theorem derivative_coe
    (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ hardOnePhoton κ)
    (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position I)))
    (hv : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v) (i : I) :
    ∀ᵐ x ∂volume,
      (derivative I V BF κ C h hh Mh hMh e v i x : PhotonFock) =
        covariant I V C h hh Mh hMh e i (reference I V BF κ v) x := by
  filter_upwards [reference_covariant_mem I V C (hardOnePhoton κ) h hh Mh hMh hhard
    (reference I V BF κ v) (reference_supported I V BF κ v hv) e i] with x hx
  exact ((generatedFockSubspace (hardOnePhoton κ)).coe_orthogonalProjectionOnto_apply _).trans
    ((generatedFockSubspace (hardOnePhoton κ)).starProjection_eq_self_iff.mpr hx)

end Reference

attribute [local irreducible] PhysicalPFReference.normalEnergy PhysicalPFVacuumEnergy.hardEnergy
  PhysicalPFVacuumInsertion.insertion reference derivative rest

section Physical

local instance vacuumFormPhotonDirectInner : InnerProductSpace ℂ PhotonFock :=
  { (inferInstance : InnerProductSpace ℂ PhotonFock) with
    toNormedSpace := (inferInstance : NormedSpace ℂ PhotonFock) }

local instance vacuumFormHardDirectInner (κ : ℝ) :
    InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ)) :=
  { (inferInstance : InnerProductSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) with
    toNormedSpace := (inferInstance : NormedSpace ℂ (generatedFockSubspace (hardOnePhoton κ))) }


variable (I : Type) [Fintype I] [DecidableEq I]
  (V : Position I → ℝ) (C : CanonicalSectorCCR photonMeasure)
  (k h s : I → Position I → WeightedPhotonKernel)
  (hk : ∀ i, AEStronglyMeasurable (k i) volume)
  (hh : ∀ i, AEStronglyMeasurable (h i) volume)
  (hs : ∀ i, AEStronglyMeasurable (s i) volume)
  (Mk Mh Ms : ℝ)
  (hMk : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ Mk)
  (hMh : ∀ i, ∀ᵐ x ∂volume, ‖h i x‖ ≤ Mh)
  (hMs : ∀ i, ∀ᵐ x ∂volume, ‖s i x‖ ≤ Ms)
  (hsplit : ∀ i, ∀ᵐ x ∂volume, k i x = h i x + s i x)
  (B : StandardNormalTraceBackground) (S : PhysicalClosedForms.StandardClosedFormBackground)
  (BF : StandardSymmetricFockExponential) (κ e : ℝ)
  (hhard : ∀ i, ∀ᵐ x ∂volume, (h i x).val.1 ∈ hardOnePhoton κ)
  (hsoft : ∀ i, ∀ᵐ x ∂volume, (s i x).val.1 ∈ (hardOnePhoton κ)ᗮ)
  {Hv : Type*} [NormedAddCommGroup Hv] [InnerProductSpace ℂ Hv]
  (Ω : Hv) (χ : I → Position I → Hv) (hΩ : ‖Ω‖ = 1)
  (hχ : ∀ i, ∀ᵐ x ∂volume, inner ℂ Ω (χ i x) = 0)
  (hχnorm : ∀ i, ∀ᵐ x ∂volume, ‖χ i x‖ ^ 2 = ‖(s i x).val.1‖ ^ 2)

include hsplit hhard hsoft hΩ hχ hχnorm

set_option backward.isDefEq.respectTransparency.types true in
include hs Ms hMs in
private theorem full_kinetic_ae
    (v : Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position I)))
    (hv : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v) (i : I) :
    ∀ᵐ x ∂volume,
      ‖vacuumDerivative Ω (χ i x) e (derivative I V BF κ C h hh Mh hMh e v i x) (v x)‖ ^ 2 =
        ‖covariant I V C k hk Mk hMk e i (reference I V BF κ v) x‖ ^ 2 := by
  let u := reference I V BF κ v
  have hu := reference_supported I V BF κ v hv
  have hi := reference_value I V BF κ v hv
  have hrad := reference_radiation_ae I V u
  have hsp := reference_covariant_split I V C k h s hk hh hs Mk Mh Ms
    hMk hMh hMs hsplit u e i
  filter_upwards [derivative_coe I V BF κ C h hh Mh hMh e hhard v hv i,
    reference_soft_inner I V C (hardOnePhoton κ) s hs Ms hMs hsoft u hu
      (covariant I V C h hh Mh hMh e i u)
      (reference_covariant_mem I V C (hardOnePhoton κ) h hh Mh hMh hhard u hu e i) i,
    spatialField_ae volume C (s i) (hs i) Ms (hMs i) (radiationSource I V u),
    reference_radiation_mem I V (hardOnePhoton κ) u hu, hsoft i, hχ i, hχnorm i,
    hrad, insertion_ae volume BF κ v,
    Lp.coeFn_smul (e : ℂ) (field I V C s hs Ms hMs i u),
    Lp.coeFn_sub (covariant I V C h hh Mh hMh e i u)
      ((e : ℂ) • field I V C s hs Ms hMs i u)]
      with x hd ho hf hq hsoftx hχx hχnx hr hv he hsub
  have hvalue : inclusion I V u x = (v x : PhotonFock) :=
    (congrArg (fun w : WaveSpace I => w x) hi).trans hv
  have hfull : covariant I V C k hk Mk hMk e i u x =
      covariant I V C h hh Mh hMh e i u x - (e : ℂ) • field I V C s hs Ms hMs i u x :=
    (congrArg (fun w : WaveSpace I => w x) hsp).trans
      (hsub.trans (congrArg (fun z : PhotonFock =>
        covariant I V C h hh Mh hMh e i u x - z) he))
  have hdNorm : ‖derivative I V BF κ C h hh Mh hMh e v i x‖ =
      ‖covariant I V C h hh Mh hMh e i u x‖ :=
    congrArg (fun w : PhotonFock => ‖w‖) hd
  have hfieldNorm : ‖field I V C s hs Ms hMs i u x‖ ^ 2 =
      ‖kernelField C (s i x) (radiationSource I V u x)‖ ^ 2 :=
    congrArg (fun w : PhotonFock => ‖w‖ ^ 2) hf
  have hvalueNorm : ‖radiationGraphInclusion (radiationSource I V u x)‖ ^ 2 =
      ‖v x‖ ^ 2 :=
    congrArg (fun w : PhotonFock => ‖w‖ ^ 2) (hr.symm.trans hvalue)
  have hb : ‖field I V C s hs Ms hMs i u x‖ ^ 2 = ‖χ i x‖ ^ 2 * ‖v x‖ ^ 2 :=
    hfieldNorm.trans ((kernelField_norm_sq_of_orthogonal C (hardOnePhoton κ) (s i x) hsoftx
      (radiationSource I V u x) hq).trans (congrArg₂ (fun a b : ℝ => a * b)
        hχnx.symm hvalueNorm))
  exact vacuum_norm_match (H := PhotonFock)
    (K := generatedFockSubspace (hardOnePhoton κ))
    Ω (χ i x) hΩ hχx e (derivative I V BF κ C h hh Mh hMh e v i x) (v x)
    (covariant I V C h hh Mh hMh e i u x) (field I V C s hs Ms hMs i u x)
    (covariant I V C k hk Mk hMk e i u x) hdNorm ho hb hfull

set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
/-- Physical hard and full forms share the tensor vacuum kinetic formula. -/
def vacuumFormData : VacuumFormData
    (X := Position I) (I := I) (K := generatedFockSubspace (hardOnePhoton κ))
    (V := Hv) (Hfull := WaveSpace I) (ν := volume)
    (B.realization (Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position I)))).rank
    (B.traceData (H := Lp (generatedFockSubspace (hardOnePhoton κ)) 2
      (volume : Measure (Position I))))
    (hardEnergy I V C h hh Mh hMh B S BF κ e)
    (B.realization (WaveSpace I)).rank (B.traceData (H := WaveSpace I))
    (normalEnergy I V C k hk Mk hMk B S e) (insertion volume BF κ) Ω χ e where
  derivative := derivative I V BF κ C h hh Mh hMh e
  rest := rest I V BF κ
  kinetic_integrable v hv := by
    have hv' : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v :=
      (hardEnergy_finite_iff I V C h hh Mh hMh B S BF κ e v).mp hv
    apply (kinetic_integrable
      (fun i => covariant I V C h hh Mh hMh e i (reference I V BF κ v))).congr
    filter_upwards [ae_all_iff.mpr (fun i =>
      derivative_coe I V BF κ C h hh Mh hMh e hhard v hv' i)] with x hx
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (congrArg (fun w : PhotonFock => ‖w‖ ^ 2) (hx i)).symm
  hard_form v hv := by
    have hv' : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v :=
      (hardEnergy_finite_iff I V C h hh Mh hMh B S BF κ e v).mp hv
    have hi := reference_value I V BF κ v hv'
    have hd : (∫ x, (1 / 2 : ℝ) * ∑ i,
        ‖derivative I V BF κ C h hh Mh hMh e v i x‖ ^ 2) =
        kineticEnergy I V C h hh Mh hMh e (reference I V BF κ v) := by
      calc
        _ = ∫ x, (1 / 2 : ℝ) * ∑ i,
            ‖covariant I V C h hh Mh hMh e i (reference I V BF κ v) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [ae_all_iff.mpr (fun i =>
            derivative_coe I V BF κ C h hh Mh hMh e hhard v hv' i)] with x hx
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun w : PhotonFock => ‖w‖ ^ 2) (hx i)
        _ = _ := kinetic_integral _
    have hvalue := (hardEnergy_rankOne I V C h hh Mh hMh B S BF κ e v).trans
      ((congrArg (fun w : WaveSpace I =>
        (normalEnergy I V C h hh Mh hMh B S e).expectation
          ((B.realization (WaveSpace I)).rank.rankOne w)) hi.symm).trans
        (normalEnergy_rankOne I V C h hh Mh hMh B S e (reference I V BF κ v)))
    refine hvalue.trans (congrArg ENNReal.ofReal ?_)
    rw [hd]
    unfold energy rest
    ring
  full_form v hv := by
    have hv' : ∃ u : Reference I V, inclusion I V u = insertion volume BF κ v :=
      (hardEnergy_finite_iff I V C h hh Mh hMh B S BF κ e v).mp hv
    have hi := reference_value I V BF κ v hv'
    have hd : (∫ x, (1 / 2 : ℝ) * ∑ i,
        ‖vacuumDerivative Ω (χ i x) e (derivative I V BF κ C h hh Mh hMh e v i x) (v x)‖ ^ 2) =
        kineticEnergy I V C k hk Mk hMk e (reference I V BF κ v) := by
      exact (kinetic_integral_congr (μ := volume)
        (fun i x => ‖vacuumDerivative Ω (χ i x) e
          (derivative I V BF κ C h hh Mh hMh e v i x) (v x)‖ ^ 2)
        (fun i x => ‖covariant I V C k hk Mk hMk e i (reference I V BF κ v) x‖ ^ 2)
        (fun i => full_kinetic_ae I V C k h s hk hh hs
          Mk Mh Ms hMk hMh hMs hsplit BF κ e hhard hsoft Ω χ hΩ hχ hχnorm v hv' i)).trans
        (kinetic_integral (fun i => covariant I V C k hk Mk hMk e i (reference I V BF κ v)))
    have hvalue := (congrArg (fun w : WaveSpace I =>
      (normalEnergy I V C k hk Mk hMk B S e).expectation
        ((B.realization (WaveSpace I)).rank.rankOne w)) hi.symm).trans
      (normalEnergy_rankOne I V C k hk Mk hMk B S e (reference I V BF κ v))
    refine hvalue.trans (congrArg ENNReal.ofReal ?_)
    rw [hd]
    unfold energy rest
    ring

end Physical

end GptLean.PhysicalPFVacuumForm
