import PfHk.PauliFormLinear
import PfHk.PauliFormBounds
import PfHk.PauliOrbitalForm
import Mathlib.Analysis.Normed.Operator.Banach

/-! The topology of the actual spin--photon form domain. Scalar
multiplication is continuous on the complete reference space by its
closed L2 graph. The reference norm is controlled by the ordinary
electronic and radiation energies. -/

noncomputable section
attribute [-instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner

namespace PfHk.PauliFormTopology

open MeasureTheory Filter Topology GptLean GptLean.PhysicalFock
  GptLean.PhysicalPFReference PfHk.PhysicalLocalEnergy
  PfHk.PhysicalExternalFormLinear PfHk.PauliGroundState PfHk.PauliFormBounds
  PfHk.PauliSpin

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 50000

private theorem continuous_bundle {S X H : Type*} [Fintype S] [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X) :
    Continuous (FiniteFiberL2.bundle (S := S) (H := H) (μ := μ)) :=
  FiniteFiberL2.isometry.continuous.comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => Lp H 2 μ)).symm.continuous

private theorem contraction_continuous {Q H : Type*} [TopologicalSpace Q]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : ℕ}
    (d : Fin 3 → SpinIndex N → Q → H) (hd : ∀ a s, Continuous (d a s))
    (n : Fin N) (s : SpinIndex N) :
    Continuous (fun u => PauliCurrentAlgebra.contraction n (fun a t => d a t u) s) := by
  unfold PauliCurrentAlgebra.contraction
  simp only [Finset.sum_apply]
  apply continuous_finsetSum
  intro a _
  fin_cases a <;> simp only [sigmaFamily] <;> split_ifs <;> fun_prop

private theorem form_zero {Q : Type*} [AddCommGroup Q] [Module ℂ Q]
    (q : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) : q 0 0 = 0 := (q 0).map_zero

private theorem finite_reference_bound {S Q E : Type*} [Fintype S] [Fintype Q]
    [NormedAddCommGroup E] (u : S → E) (m : S → ℝ) (d : Q → S → ℝ) (r : S → ℝ)
    (hb : ∀ s R, 0 ≤ R → m s ≤ R → (∀ q, d q s ≤ R) → r s ≤ R → ‖u s‖ ≤ 2 * R) :
    ‖u‖ ^ 2 ≤ 4 * ((∑ s, m s ^ 2) + (∑ q, ∑ s, d q s ^ 2) + ∑ s, r s ^ 2) := by
  let T := (∑ s, m s ^ 2) + (∑ q, ∑ s, d q s ^ 2) + ∑ s, r s ^ 2
  have hm : 0 ≤ ∑ s, m s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : 0 ≤ ∑ q, ∑ s, d q s ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr : 0 ≤ ∑ s, r s ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : 0 ≤ T := add_nonneg (add_nonneg hm hd) hr
  have hmi (s : S) : m s ^ 2 ≤ T :=
    (Finset.single_le_sum (fun s _ => sq_nonneg (m s)) (Finset.mem_univ s)).trans
      ((le_add_of_nonneg_right hd).trans (le_add_of_nonneg_right hr))
  have hdi (q : Q) (s : S) : d q s ^ 2 ≤ T := by
    have h₁ : d q s ^ 2 ≤ ∑ s, d q s ^ 2 :=
      Finset.single_le_sum (fun s _ => sq_nonneg (d q s)) (Finset.mem_univ s)
    have h₂ : (∑ s, d q s ^ 2) ≤ ∑ q, ∑ s, d q s ^ 2 :=
      Finset.single_le_sum (fun q _ => Finset.sum_nonneg fun s _ => sq_nonneg (d q s))
        (Finset.mem_univ q)
    exact (h₁.trans h₂).trans
      ((le_add_of_nonneg_left hm).trans (le_add_of_nonneg_right hr))
  have hri (s : S) : r s ^ 2 ≤ T :=
    (Finset.single_le_sum (fun s _ => sq_nonneg (r s)) (Finset.mem_univ s)).trans
      (le_add_of_nonneg_left (add_nonneg hm hd))
  have hn : ‖u‖ ≤ 2 * Real.sqrt T := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro s
    exact hb s (Real.sqrt T) (Real.sqrt_nonneg _)
      (Real.le_sqrt_of_sq_le (hmi s)) (fun q => Real.le_sqrt_of_sq_le (hdi q s))
      (Real.le_sqrt_of_sq_le (hri s))
  calc
    ‖u‖ ^ 2 ≤ (2 * Real.sqrt T) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hn 2
    _ = 4 * T := by rw [mul_pow, Real.sq_sqrt hT]; norm_num

variable {N : ℕ}

attribute [local irreducible] referenceSubspace inclusion ordinary radiation
  roughMultiply potential rawCovariant rawContraction rawEnergy rawForm
  normSquared ordinaryEnergy radiationEnergy PauliFormLinear.form

theorem roughLinear_continuous {I : Type} [Fintype I] [DecidableEq I]
    (V f : Position I → ℝ)
    (hf : ∀ u : Reference I V, HasMultiplier f (inclusion I V u)) :
    Continuous (roughLinear V f hf) := by
  apply LinearMap.continuous_of_seq_closed_graph (𝕜 := ℂ)
    (E := Reference I V) (F := WaveSpace I) (roughLinear V f hf)
  intro u x y hu hy
  have hg (v : Reference I V) :
      (inclusion I V v, roughLinear V f hf v) ∈
        PhysicalMultiplicationGraph.graph volume (fun X => (f X : ℂ)) := by
    filter_upwards [roughMultiply_ae f (inclusion I V v) (hf v)] with X hX
    exact hX.trans (Complex.coe_smul (f X) (inclusion I V v X)).symm
  have hlim := ((inclusion I V).continuous.tendsto x |>.comp hu).prodMk_nhds hy
  have hm := (PhysicalMultiplicationGraph.graph_closed volume (H := PhotonFock)
    (fun X => (f X : ℂ))).mem_of_tendsto hlim (Eventually.of_forall fun n => hg (u n))
  have hmx : ∀ᵐ X ∂volume, y X = (f X : ℂ) • inclusion I V x X := hm
  have hgx : ∀ᵐ X ∂volume, roughLinear V f hf x X = (f X : ℂ) • inclusion I V x X := hg x
  apply Lp.ext
  filter_upwards [hmx, hgx] with X hy hx
  exact hy.trans hx.symm

theorem normSquared_nonneg (u : Ref N) : 0 ≤ normSquared u :=
  by unfold normSquared; exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSquared_continuous : Continuous (normSquared (N := N)) := by
  unfold normSquared
  exact continuous_finsetSum _ fun s _ =>
    ((inclusion (Fin N × Fin 3) (fun _ => 0)).continuous.comp (continuous_apply s)).norm.pow 2

theorem wave_continuous : Continuous (PauliReference.wave (N := N)) := by
  let J : Ref N →L[ℂ] (SpinIndex N → WaveSpace (Fin N × Fin 3)) :=
    ContinuousLinearMap.pi fun s =>
      (inclusion (Fin N × Fin 3) (fun _ => 0)).comp (ContinuousLinearMap.proj s)
  exact (continuous_bundle (S := SpinIndex N) (H := PhotonFock) volume).comp J.continuous

theorem reference_norm_le (u : Reference (Fin N × Fin 3) (fun _ => 0))
    (R : ℝ) (hR : 0 ≤ R)
    (hi : ‖inclusion (Fin N × Fin 3) (fun _ => 0) u‖ ≤ R)
    (hd : ∀ q, ‖ordinary (Fin N × Fin 3) (fun _ => 0) q u‖ ≤ R)
    (hr : ‖radiation (Fin N × Fin 3) (fun _ => 0) u‖ ≤ R) : ‖u‖ ≤ 2 * R := by
  have he : ‖electronic (Fin N × Fin 3) (fun _ => 0) u‖ ≤ R := by
    rw [ElectronicH1Complex.norm_eq_max]
    apply max_le
    · simpa only [inclusion, ContinuousLinearMap.comp_apply] using hi
    · apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro q
      simpa only [ordinary, ContinuousLinearMap.comp_apply,
        ElectronicH1Complex.derivative_apply, ElectronicH1Complex.gradient_apply] using hd q
  have hrad := (radiationSource_norm_le (Fin N × Fin 3) (fun _ => 0) u).trans
    (add_le_add hi hr)
  have hp : ‖potentialSource (Fin N × Fin 3) (fun _ => 0) u‖ ≤ R := by
    have hzero : ‖potential (Fin N × Fin 3) (fun _ => 0) u‖ = 0 :=
      (congrArg (fun w : WaveSpace (Fin N × Fin 3) => ‖w‖)
        (PauliOrbitalForm.potential_zero u)).trans (norm_zero : ‖(0 : WaveSpace (Fin N × Fin 3))‖ = 0)
    exact (potentialSource_norm (Fin N × Fin 3) (fun _ => 0) u).le.trans
      (max_le hi (hzero.le.trans hR))
  change max ‖electronic (Fin N × Fin 3) (fun _ => 0) u‖
    (max ‖radiationSource (Fin N × Fin 3) (fun _ => 0) u‖
      ‖potentialSource (Fin N × Fin 3) (fun _ => 0) u‖) ≤ 2 * R
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

theorem reference_norm_sq_le (u : Ref N) :
    ‖u‖ ^ 2 ≤ 4 * (normSquared u + ordinaryEnergy u + radiationEnergy u) := by
  simpa only [normSquared, ordinaryEnergy, radiationEnergy] using
    finite_reference_bound u
      (fun s => ‖inclusion (Fin N × Fin 3) (fun _ => 0) (u s)‖)
      (fun q s => ‖ordinary (Fin N × Fin 3) (fun _ => 0) q (u s)‖)
      (fun s => ‖radiation (Fin N × Fin 3) (fun _ => 0) (u s)‖)
      (fun s R hR hi hd hr => reference_norm_le (u s) R hR hi hd hr)

variable (C : CanonicalSectorCCR photonMeasure)
  (κ : (Fin N × Fin 3) → Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ q, AEStronglyMeasurable (κ q) volume)
  (M : ℝ) (hκbound : ∀ q, ∀ᵐ X ∂volume, ‖κ q X‖ ≤ M) (e : ℝ)
  (A : (Fin N × Fin 3) → Position (Fin N × Fin 3) → ℝ)
  (positive negative : Position (Fin N × Fin 3) → ℝ)
  (D : ∀ u : Ref N, Domain A positive negative u)

theorem rawCovariant_continuous (q : Fin N × Fin 3) (s : SpinIndex N) :
    Continuous (fun u : Ref N => rawCovariant C κ hκ M hκbound e A positive negative u (D u) q s) := by
  unfold rawCovariant externalCovariant
  have hm := roughLinear_continuous (fun _ => 0) (A q)
    (fun z => (D (fun _ => z) s).vector q)
  exact ((covariant (Fin N × Fin 3) (fun _ => 0) C κ hκ M hκbound e q).continuous.add hm).comp
    (continuous_apply s)

theorem rawContraction_continuous (n : Fin N) (s : SpinIndex N) :
    Continuous (fun u : Ref N => rawContraction C κ hκ M hκbound e A positive negative u (D u) n s) := by
  unfold rawContraction
  exact contraction_continuous
    (fun a t u => rawCovariant C κ hκ M hκbound e A positive negative u (D u) (n, a) t)
    (fun a t => rawCovariant_continuous C κ hκ M hκbound e A positive negative D (n, a) t) n s

theorem rawEnergy_continuous :
    Continuous (fun u : Ref N => rawEnergy C κ hκ M hκbound e A positive negative u (D u)) := by
  simp_rw [rawEnergy_eq]
  have hc := continuous_finsetSum Finset.univ fun n _ =>
    continuous_finsetSum Finset.univ fun s _ =>
      (rawContraction_continuous C κ hκ M hκbound e A positive negative D n s).norm.pow 2
  have hr := continuous_finsetSum (Finset.univ : Finset (SpinIndex N)) fun s _ =>
    ((radiation (Fin N × Fin 3) (fun _ => 0)).continuous.comp (continuous_apply s)).norm.pow 2
  have hp := continuous_finsetSum Finset.univ fun s _ =>
    ((roughLinear_continuous (fun _ => 0) positive (fun z => (D (fun _ => z) s).positive)).comp
      (continuous_apply s)).norm.pow 2
  have hn := continuous_finsetSum Finset.univ fun s _ =>
    ((roughLinear_continuous (fun _ => 0) negative (fun z => (D (fun _ => z) s).negative)).comp
      (continuous_apply s)).norm.pow 2
  exact (((hc.const_mul (1 / 2 : ℝ)).add hr).add hp).sub hn

theorem rawEnergy_zero : rawEnergy C κ hκ M hκbound e A positive negative 0 (D 0) = 0 := by
  have h := form_zero (Q := Ref N) (PauliFormLinear.form C κ hκ M hκbound e A positive negative D)
  have he := PauliFormLinear.form_apply C κ hκ M hκbound e A positive negative D (0 : Ref N) 0
  unfold rawEnergy
  exact congrArg Complex.re (he.symm.trans h)

end PfHk.PauliFormTopology

attribute [instance] GptLean.SymmetricLift.TensorHilbert.normed
  GptLean.SymmetricLift.TensorHilbert.inner
