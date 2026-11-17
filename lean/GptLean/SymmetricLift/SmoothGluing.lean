import GptLean.SymmetricLift
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Algebra.Support

/-!
Smooth operator gluing for the symmetric tensor lift. Smoothness here is
in the operator norm, not only smoothness after evaluating on each vector.
The local weights are allowed to vanish outside their chart. Their closed
supports ensure that this zero extension is smooth across chart boundaries.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace GptLean.SymmetricLift

open WithLp Filter
open scoped Topology ContDiff

variable {X H K : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {ι : Type*} [Fintype ι]

local instance smoothGluingRealH : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance smoothGluingRealK : NormedSpace ℝ K := NormedSpace.restrictScalars ℝ ℂ K

/-- Bundling a finite family of operators is continuous in the operator norm. -/
def piOperators : (ι → H →L[ℂ] K) →L[ℂ] H →L[ℂ] (ι → K) := by
  let B : (ι → H →L[ℂ] K) →ₗ[ℂ] H →L[ℂ] (ι → K) :=
    {
      toFun := fun (L : ι → H →L[ℂ] K) => ContinuousLinearMap.pi L
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  exact B.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := ι → H →L[ℂ] K)
    (F := H →L[ℂ] (ι → K)) 1 (fun L => by
    change ‖ContinuousLinearMap.pi L‖ ≤ 1 * ‖L‖
    simpa only [one_mul] using ContinuousLinearMap.norm_pi_le_of_le
      (𝕜 := ℂ) (E := H) (M := fun _ : ι => K) (L := L)
      (fun i => norm_le_pi_norm L i) (norm_nonneg L))

theorem contDiffOn_piOperators {D : Set X} {L : ι → X → H →L[ℂ] K}
    (hL : ∀ i, ContDiffOn ℝ ∞ (L i) D) :
    ContDiffOn ℝ ∞ (fun x => ContinuousLinearMap.pi (fun i => L i x)) D := by
  have h : ContDiff ℝ ∞ (piOperators (H := H) (K := K) (ι := ι)) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := ι → H →L[ℂ] K)
      (F := H →L[ℂ] (ι → K)) (n := ∞) piOperators).restrict_scalars ℝ
  exact h.comp_contDiffOn (contDiffOn_pi.mpr hL)

theorem contDiffOn_precompose {D : Set X} {L : X → H →L[ℂ] K}
    (hL : ContDiffOn ℝ ∞ L D) (Q : H →L[ℂ] H) :
    ContDiffOn ℝ ∞ (fun x => (L x).comp Q) D := by
  exact (((ContinuousLinearMap.compL ℂ H H K).flip Q).restrictScalars ℝ).contDiff.comp_contDiffOn hL

theorem contDiffOn_postcompose {A B J : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedSpace ℝ A] [IsScalarTower ℝ ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedSpace ℝ B] [IsScalarTower ℝ ℂ B]
    [NormedAddCommGroup J] [NormedSpace ℂ J] [NormedSpace ℝ J] [IsScalarTower ℝ ℂ J]
    {D : Set X} {L : X → A →L[ℂ] B}
    (hL : ContDiffOn ℝ ∞ L D) (Q : B →L[ℂ] J) :
    ContDiffOn ℝ ∞ (fun x => Q.comp (L x)) D := by
  exact ((ContinuousLinearMap.compL ℂ A B J Q).restrictScalars ℝ).contDiff.comp_contDiffOn hL

/-- The actual continuous-linear operator used for finite Hilbert gluing. -/
def smoothGlue (P : H →L[ℂ] H) (χ : ι → ℝ) (V : ι → H →L[ℂ] K) :
    H →L[ℂ] GlueTarget H K ι :=
  (prodContinuousLinearEquiv 2 ℂ H (PiLp 2 (fun _ : ι => K))).symm.toContinuousLinearMap.comp
    (P.prod ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => χ i • (V i).comp (ContinuousLinearMap.id ℂ H - P)))))

theorem smoothGlue_apply (P : H →L[ℂ] H) (χ : ι → ℝ) (V : ι → H →L[ℂ] K) (u : H) :
    smoothGlue P χ V u = glue P.toLinearMap χ (fun i => (V i).toLinearMap) u := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · rfl
  · apply (WithLp.ext_iff 2).mpr
    funext i
    simp [smoothGlue, glue, Complex.coe_smul]

/-- Actual operator-norm smoothness of the global gluing map. -/
theorem smoothGlue_contDiffOn_of_weighted (P : H →L[ℂ] H) {D : Set X}
    (χ : ι → X → ℝ) (V : ι → X → H →L[ℂ] K)
    (hlocal : ∀ i, ContDiffOn ℝ ∞
      (fun x => χ i x • (V i x).comp (ContinuousLinearMap.id ℂ H - P)) D) :
    ContDiffOn ℝ ∞ (fun x => smoothGlue P (fun i => χ i x) (fun i => V i x)) D := by
  have hpi := contDiffOn_postcompose (contDiffOn_piOperators hlocal)
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap
  let A : ((H →L[ℂ] H) × (H →L[ℂ] PiLp 2 (fun _ : ι => K))) →L[ℂ]
      H →L[ℂ] (H × PiLp 2 (fun _ : ι => K)) :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) (E := H) (F := H)
      (G := PiLp 2 (fun _ : ι => K)) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ContDiff ℝ ∞ A :=
    (ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := (H →L[ℂ] H) × (H →L[ℂ] PiLp 2 (fun _ : ι => K)))
      (F := H →L[ℂ] (H × PiLp 2 (fun _ : ι => K))) (n := ∞) A).restrict_scalars ℝ
  have hp := hA.comp_contDiffOn
    ((contDiffOn_const (c := P)).prodMk hpi)
  exact contDiffOn_postcompose hp
    (prodContinuousLinearEquiv 2 ℂ H (PiLp 2 (fun _ : ι => K))).symm.toContinuousLinearMap

theorem smoothGlue_contDiffOn (P : H →L[ℂ] H) {D : Set X}
    (χ : ι → X → ℝ) (V : ι → X → H →L[ℂ] K)
    (hχ : ∀ i, ContDiffOn ℝ ∞ (χ i) D)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) D) :
    ContDiffOn ℝ ∞ (fun x => smoothGlue P (fun i => χ i x) (fun i => V i x)) D :=
  smoothGlue_contDiffOn_of_weighted P χ V
    (fun i => (hχ i).smul (contDiffOn_precompose (hV i) _))

/-- A weight whose closed support is inside its chart gives a genuinely
smooth zero extension, even if the unweighted chart map is arbitrary outside. -/
theorem weighted_contDiffOn_of_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D O : Set X} (hD : IsOpen D) (hO : IsOpen O)
    {χ : X → ℝ} {V : X → E}
    (hχ : ContDiffOn ℝ ∞ χ D) (hV : ContDiffOn ℝ ∞ V (D ∩ O))
    (hsupport : tsupport χ ∩ D ⊆ O) :
    ContDiffOn ℝ ∞ (fun x => χ x • V x) D := by
  intro x hx
  by_cases hs : x ∈ tsupport χ
  · exact ((hχ.contDiffAt (hD.mem_nhds hx)).smul
      (hV.contDiffAt ((hD.inter hO).mem_nhds ⟨hx, hsupport ⟨hs, hx⟩⟩))).contDiffWithinAt
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hs
    have heq : (fun y => χ y • V y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
      filter_upwards [hz] with y hy
      simp [hy]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The global family is smooth when each local family is smooth only on
its own chart and its weight has closed support inside that chart. -/
theorem smoothGlue_contDiffOn_supported (P : H →L[ℂ] H)
    {D : Set X} (hD : IsOpen D) (O : ι → Set X) (hO : ∀ i, IsOpen (O i))
    (χ : ι → X → ℝ) (V : ι → X → H →L[ℂ] K)
    (hχ : ∀ i, ContDiffOn ℝ ∞ (χ i) D)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (D ∩ O i))
    (hsupport : ∀ i, tsupport (χ i) ∩ D ⊆ O i) :
    ContDiffOn ℝ ∞ (fun x => smoothGlue P (fun i => χ i x) (fun i => V i x)) D := by
  apply smoothGlue_contDiffOn_of_weighted
  intro i
  exact weighted_contDiffOn_of_support hD (hO i) (hχ i)
    (contDiffOn_precompose (hV i) _) (hsupport i)

/-- Evaluating a complex operator family commutes with the real derivative. -/
theorem hasFDerivAt_operator_apply {V : X → H →L[ℂ] K} {x : X}
    {dV : X →L[ℝ] (H →L[ℂ] K)} (hV : HasFDerivAt V dV x) (u : H) :
    HasFDerivAt (fun y => V y u)
      (((ContinuousLinearMap.apply ℂ K u).restrictScalars ℝ).comp dV) x :=
  ((ContinuousLinearMap.apply ℂ K u).restrictScalars ℝ).hasFDerivAt.comp x hV

end GptLean.SymmetricLift
