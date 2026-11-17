import GptLean.Repair.FiniteCoordinateMollification
import GptLean.Repair.ScalarFormOperations
import GptLean.SymmetricLift.LocalL2Pullback
import GptLean.SymmetricLift.TensorApproximation

/-! Particle pullback of actual local weak derivatives. The proof mollifies
the one-particle field, pulls back the smooth fields, and passes their tested
identities to the local L2 limit. No product Sobolev premise is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace GptLean.Representability

open MeasureTheory Filter GptLean.SymmetricLift GptLean.Repair
open scoped ENNReal Topology ContDiff

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local strong convergence of a field and its weak gradients preserves
every compact smooth distributional test identity. -/
theorem hasWeakH1Local_of_localL2_limit
    {f : EuclideanSpace ℝ I → E} {df : I → EuclideanSpace ℝ I → E}
    {fn : ℕ → EuclideanSpace ℝ I → E}
    {dfn : ℕ → I → EuclideanSpace ℝ I → E}
    (hn : ∀ n, HasWeakH1Local (fn n) (dfn n))
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K))
    (hdf : ∀ i K, IsCompact K → MemLp (df i) 2 (volume.restrict K))
    (hc : ∀ K, IsCompact K → Tendsto
      (fun n => eLpNorm (fn n - f) 2 (volume.restrict K)) atTop (𝓝 0))
    (hdc : ∀ i K, IsCompact K → Tendsto
      (fun n => eLpNorm (dfn n i - df i) 2 (volume.restrict K)) atTop (𝓝 0)) :
    HasWeakH1Local f df := by
  refine ⟨hf, hdf, ?_⟩
  intro i φ hφ hs
  let K := tsupport φ
  let ν := volume.restrict K
  let φ' := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφ' : Continuous φ' :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ2 : MemLp φ 2 ν := (hφ.continuous.memLp_of_hasCompactSupport hs).restrict K
  have hφ'2 : MemLp φ' 2 ν :=
    (hφ'.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ _)).restrict K
  have hr (g : EuclideanSpace ℝ I → E) :
      (∫ x, φ x • g x) = ∫ x, φ x • g x ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_smul])).symm
  have hdr (g : EuclideanSpace ℝ I → E) :
      (∫ x, φ' x • g x) = ∫ x, φ' x • g x ∂ν :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx => by dsimp [φ']; rw [fderiv_of_notMem_tsupport ℝ hx]; simp)).symm
  have hw (n : ℕ) : (∫ x, φ x • dfn n i x ∂ν) =
      -(∫ x, φ' x • fn n x ∂ν) := by
    have h := (hn n).weak i φ hφ hs
    change (∫ x, φ x • dfn n i x) = -(∫ x, φ' x • fn n x) at h
    simpa only [hr, hdr] using h
  change (∫ x, φ x • df i x) = -(∫ x, φ' x • f x)
  rw [hr, hdr]
  exact weak_derivative_identity_closed_eLpNorm hφ2 hφ'2
    (fun n => (hn n).function_memLp K hs)
    (fun n => (hn n).derivative_memLp i K hs) (hf K hs) (hdf i K hs)
    (hc K hs) (hdc i K hs) (Eventually.of_forall hw)

/-- The weak gradient of a field depending on one selected particle. -/
def particlePullbackGradient {N : ℕ} (i : Fin N)
    (dt : Fin 3 → EuclideanSpace ℝ (Fin 3) → E)
    (q : Fin N × Fin 3) (x : Configuration N) : E :=
  if q.1 = i then dt q.2 (particle x i) else 0

omit [NormedSpace ℝ E] in
private theorem particlePullbackGradient_eq {N : ℕ} (i : Fin N)
    (dt : Fin 3 → EuclideanSpace ℝ (Fin 3) → E) (q : Fin N × Fin 3) (hqi : q.1 = i) :
    particlePullbackGradient i dt q = fun x => dt q.2 (particle x i) := by
  funext x
  simp only [particlePullbackGradient, hqi, ↓reduceIte]

omit [NormedSpace ℝ E] in
private theorem particlePullbackGradient_zero {N : ℕ} (i : Fin N)
    (dt : Fin 3 → EuclideanSpace ℝ (Fin 3) → E) (q : Fin N × Fin 3) (hqi : q.1 ≠ i) :
    particlePullbackGradient i dt q = 0 := by
  funext x
  simp only [particlePullbackGradient, hqi, ↓reduceIte, Pi.zero_apply]

variable [CompleteSpace E]

/-- Pullback to physical configuration space preserves local weak H1
regularity, with a zero derivative in every other particle coordinate. -/
theorem hasWeakH1Local_particlePullback {N : ℕ} (i : Fin N)
    {t : EuclideanSpace ℝ (Fin 3) → E}
    {dt : Fin 3 → EuclideanSpace ℝ (Fin 3) → E}
    (ht : HasWeakH1Local t dt) :
    HasWeakH1Local (fun x : Configuration N => t (particle x i))
      (particlePullbackGradient i dt) := by
  have hti := finite_localMemLp_two_locallyIntegrable ht.function_memLp
  have hdti (μ : Fin 3) :=
    finite_localMemLp_two_locallyIntegrable (ht.derivative_memLp μ)
  let tn := finiteMollification t
  let dtn := fun n μ => finiteMollification (dt μ) n
  let fn := fun n (x : Configuration N) => tn n (particle x i)
  let dfn := fun n => particlePullbackGradient i (dtn n)
  have htn (n : ℕ) : ContDiff ℝ ∞ (tn n) := finiteMollification_contDiff hti n
  have hfn (n : ℕ) : ContDiff ℝ ∞ (fn n) :=
    (htn n).comp (particleLinear i).toContinuousLinearMap.contDiff
  have hderiv (n : ℕ) (q : Fin N × Fin 3) (x : Configuration N) :
      fderiv ℝ (fn n) x (EuclideanSpace.single q 1) = dfn n q x := by
    have hd := ((htn n).differentiable (by simp) (particle x i)).hasFDerivAt.comp x
      (particleLinear i).toContinuousLinearMap.hasFDerivAt
    change HasFDerivAt (fn n) _ x at hd
    rw [hd.fderiv]
    change fderiv ℝ (tn n) (particle x i) (particle (EuclideanSpace.single q 1) i) = _
    rcases q with ⟨j, μ⟩
    by_cases hji : j = i
    · subst j
      rw [particle_single_same]
      change fderiv ℝ (tn n) (particle x i) (EuclideanSpace.single μ 1) =
        if i = i then dtn n μ (particle x i) else 0
      rw [ite_eq_left rfl]
      exact ((htn n).differentiable (by simp) _).lineDeriv_eq_fderiv.symm.trans
        (finiteMollification_hasLineDerivAt hti (ht.weak μ) n _).lineDeriv
    · rw [particle_single_ne j μ (Ne.symm hji), map_zero]
      simp only [dfn, particlePullbackGradient, hji, ↓reduceIte]
  have hn (n : ℕ) : HasWeakH1Local (fn n) (dfn n) :=
    (weakH1Local_of_contDiff (hfn n)).congr (Eventually.of_forall fun _ => rfl)
      (fun q => Eventually.of_forall fun x => hderiv n q x)
  have hpull {a : EuclideanSpace ℝ (Fin 3) → E}
      (ha : ∀ K, IsCompact K → MemLp a 2 (volume.restrict K))
      (K : Set (Configuration N)) (hK : IsCompact K) :
      MemLp (fun x => a (particle x i)) 2 (volume.restrict K) := by
    have h := memLp_two_comp_surjective_linearMap_on_compact (μ := volume)
      (particleLinear i) (particleLinear_surjective i)
      (finite_localMemLp_two_locallyIntegrable ha).aestronglyMeasurable ha hK
    simpa only [Function.comp_def, particleLinear] using! h
  have hconv {a : EuclideanSpace ℝ (Fin 3) → E}
      (ha : ∀ K, IsCompact K → MemLp a 2 (volume.restrict K))
      (K : Set (Configuration N)) (hK : IsCompact K) :
      Tendsto (fun n => eLpNorm
        (fun x => finiteMollification a n (particle x i) - a (particle x i))
        2 (volume.restrict K)) atTop (𝓝 0) := by
    have hai := finite_localMemLp_two_locallyIntegrable ha
    have h := tendsto_eLpNorm_two_comp_surjective_linearMap (μ := volume)
      (particleLinear i) (particleLinear_surjective i)
      (fun n => (finiteMollification_contDiff hai n).continuous.aestronglyMeasurable.sub
        hai.aestronglyMeasurable)
      (fun _ hC => finiteMollification_tendsto_eLpNorm_sub ha hC) hK
    simpa only [Function.comp_def, particleLinear, Pi.sub_apply] using! h
  apply hasWeakH1Local_of_localL2_limit hn
  · exact hpull ht.function_memLp
  · intro q K hK
    by_cases hqi : q.1 = i
    · rw [particlePullbackGradient_eq i dt q hqi]
      exact hpull (ht.derivative_memLp q.2) K hK
    · rw [particlePullbackGradient_zero i dt q hqi]
      exact MemLp.zero
  · intro K hK
    exact hconv ht.function_memLp K hK
  · intro q K hK
    change Tendsto (fun n => eLpNorm
      (particlePullbackGradient i (dtn n) q - particlePullbackGradient i dt q)
      2 (volume.restrict K)) atTop (𝓝 0)
    by_cases hqi : q.1 = i
    · simp_rw [particlePullbackGradient_eq i _ q hqi]
      exact hconv (ht.derivative_memLp q.2) K hK
    · simp_rw [particlePullbackGradient_zero i _ q hqi, sub_self, eLpNorm_zero]
      exact tendsto_const_nhds

end GptLean.Representability
