import GptLean.PhotonLocalizationEstimatesAssembly

/-!
Electronic localization from the universal bounded scalar covariant
product calculus. Permutation invariance is required, so the construction
applies on the fermionic sector.
-/

noncomputable section

namespace GptLean.PhotonLocalization

open Filter Topology MeasureTheory ElectronicLocalization
open PhotonLocalizationChannel
open scoped InnerProductSpace ENNReal

section UniversalScalarCalculus

open PhotonLocalizationKernelCutoffs SymmetricLift

variable {H X K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Gaussian.RankOneData H X} {Tr : RemovalState.PositiveTraceData X}

/-- The bounded differentiable scalar class needed by the covariant
product rule. The derivative bound uses the actual electronic coordinate
directions. Symmetry is recorded separately when the Hilbert space is
fermionic. -/
def ElectronicScalarAdmissible (electrons : ℕ)
    (f : (Fin electrons → ElectronicPosition) → ℝ) : Prop :=
  Differentiable ℝ f ∧ ∃ C : ℝ, 0 ≤ C ∧
    (∀ x, |f x| ≤ C) ∧ ∀ x (i : Fin electrons × Fin 3),
      |fderiv ℝ f x (Pi.single i.1 (EuclideanSpace.single i.2 1))| ≤ C

def ElectronicScalarSymmetric (electrons : ℕ)
    (f : (Fin electrons → ElectronicPosition) → ℝ) : Prop :=
  ∀ (x : Fin electrons → ElectronicPosition) (π : Equiv.Perm (Fin electrons)),
    f (x ∘ π) = f x

/-- Every branch of the constructed symmetric partition belongs to the
universal scalar multiplier class. This follows from its proved square
normalization and total derivative metric. -/
theorem symmetricElectronicPartition_admissible (electrons l : ℕ)
    (a : Fin electrons → Bool) :
    ElectronicScalarAdmissible electrons
      (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a) := by
  classical
  let c : ℝ := 3 * electrons * electronicPartitionConstant / (2 * ((l : ℝ) + 1) ^ 2)
  have hc : 0 ≤ c := by
    have := electronicPartitionConstant_nonneg
    dsimp [c]
    positivity
  refine ⟨symmetricElectronicPartition_differentiable _ a,
    1 + Real.sqrt (2 * c), by positivity, ?_, ?_⟩
  · intro x
    have hs := (symmetricElectronicPartition_hasSum_sq ((l : ℝ) + 1) x).tsum_eq
    rw [tsum_fintype] at hs
    have hb : (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a x) ^ 2 ≤ 1 := by
      calc
        _ ≤ ∑ b : Fin electrons → Bool,
            (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) b x) ^ 2 :=
          Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
        _ = 1 := hs
    have ha : |symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a x| ≤ 1 := by
      apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
      simpa only [sq_abs, one_pow] using hb
    exact ha.trans (by linarith [Real.sqrt_nonneg (2 * c)])
  · intro x i
    let d : (Fin electrons × Fin 3) → (Fin electrons → Bool) → ℝ := fun j b =>
      fderiv ℝ (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) b) x
        (Pi.single j.1 (EuclideanSpace.single j.2 1))
    have h1 : d i a ^ 2 ≤ ∑ b, d i b ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
    have h2 : (∑ b, d i b ^ 2) ≤ ∑ j, ∑ b, d j b ^ 2 :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.mem_univ _)
    have hm : (1 / 2 : ℝ) * ∑ j, ∑ b, d j b ^ 2 ≤ c :=
      symmetricElectronicPartition_ims_metric l x
    have hd : d i a ^ 2 ≤ 2 * c := by linarith
    have habs : |d i a| ≤ Real.sqrt (2 * c) := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rwa [sq_abs, Real.sq_sqrt (by positivity)]
    exact habs.trans (by linarith)

/-- Universal form/product calculus for one source vector and arbitrary
bounded differentiable permutation-invariant scalar multipliers.
Its hypotheses contain no article cutoff radius or selected branch. -/
structure SymmetricScalarFormSource (electrons : ℕ)
    (energy : RemovalState.PositiveForm Tr)
    (μ : Measure (Fin electrons → ElectronicPosition))
    (multiplier : ((Fin electrons → ElectronicPosition) → ℝ) → H →L[ℂ] H)
    (v : H) where
  derivative : (Fin electrons × Fin 3) → (Fin electrons → ElectronicPosition) → K
  wave : (Fin electrons → ElectronicPosition) → K
  scalar : (Fin electrons → ElectronicPosition) → ℝ
  source_integrable : Integrable
    (fun x => (1 / 2 : ℝ) * ∑ i, ‖derivative i x‖ ^ 2 + scalar x) μ
  mass_integrable : Integrable (fun x => ‖wave x‖ ^ 2) μ
  mass_eq : (∫ x, ‖wave x‖ ^ 2 ∂μ) = ‖v‖ ^ 2
  original_form : (energy.expectation (A.rankOne v)).toReal =
    ∫ x, (1 / 2 : ℝ) * ∑ i, ‖derivative i x‖ ^ 2 + scalar x ∂μ
  multiplier_integrable : ∀ f, ElectronicScalarAdmissible electrons f →
    ElectronicScalarSymmetric electrons f → Integrable (fun x =>
      (1 / 2 : ℝ) * ∑ i : Fin electrons × Fin 3,
        ‖(f x : ℂ) • derivative i x - Complex.I •
          (fderiv ℝ f x (Pi.single i.1 (EuclideanSpace.single i.2 1)) : ℂ) • wave x‖ ^ 2 +
        f x ^ 2 * scalar x) μ
  multiplier_finite : ∀ f, ElectronicScalarAdmissible electrons f →
    ElectronicScalarSymmetric electrons f → energy.expectation (A.rankOne (multiplier f v)) < ⊤
  multiplier_form : ∀ f, ElectronicScalarAdmissible electrons f →
    ElectronicScalarSymmetric electrons f →
    (energy.expectation (A.rankOne (multiplier f v))).toReal = ∫ x,
      (1 / 2 : ℝ) * ∑ i : Fin electrons × Fin 3,
        ‖(f x : ℂ) • derivative i x - Complex.I •
          (fderiv ℝ f x (Pi.single i.1 (EuclideanSpace.single i.2 1)) : ℂ) • wave x‖ ^ 2 +
        f x ^ 2 * scalar x ∂μ

/-- Specialization of the universal scalar graph calculus to the actual
symmetric partition. All branch domain and form identities are obtained
from one source representative and the same multiplier calculus. -/
def SymmetricScalarFormSource.partition
    {electrons : ℕ} {energy : RemovalState.PositiveForm Tr}
    {μ : Measure (Fin electrons → ElectronicPosition)}
    {multiplier : ((Fin electrons → ElectronicPosition) → ℝ) → H →L[ℂ] H} {v : H}
    (S : SymmetricScalarFormSource (A := A) (K := K) electrons energy μ multiplier v)
    (l : ℕ) : ElectronicIMSSource (A := A) (K := K) energy μ
      (symmetricMultiplier (electronicPair ((l : ℝ) + 1)))
      (fun i : Fin electrons × Fin 3 => Pi.single i.1 (EuclideanSpace.single i.2 1))
      (fun a => multiplier (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a)) v where
  derivative := S.derivative
  wave := S.wave
  scalar := S.scalar
  branch_integrable a := S.multiplier_integrable _
    (symmetricElectronicPartition_admissible electrons l a)
    (symmetricElectronicPartition_perm _ a)
  source_integrable := S.source_integrable
  mass_integrable := S.mass_integrable
  mass_eq := S.mass_eq
  original_form := S.original_form
  branch_finite a := S.multiplier_finite _
    (symmetricElectronicPartition_admissible electrons l a)
    (symmetricElectronicPartition_perm _ a)
  branch_form a := S.multiplier_form _
    (symmetricElectronicPartition_admissible electrons l a)
    (symmetricElectronicPartition_perm _ a)

/-- Actual symmetric electronic cutoffs from an arbitrary scalar
multiplier calculus. No family of cutoff-domain conclusions or IMS
inequalities is taken as an argument. -/
noncomputable def ElectronicCutoffData.ofScalarCalculus
    (electrons : ℕ) (energy : RemovalState.PositiveForm Tr)
    (μ : Measure (Fin electrons → ElectronicPosition))
    (multiplier : ((Fin electrons → ElectronicPosition) → ℝ) → H →L[ℂ] H)
    (compression : ((Fin electrons → ElectronicPosition) → ℝ) → X →L[ℝ] X)
    (hcompression : ∀ f, ElectronicScalarAdmissible electrons f →
      ElectronicScalarSymmetric electrons f → ∀ v,
      compression f (A.rankOne v) = A.rankOne (multiplier f v))
    (source : ∀ v, energy.expectation (A.rankOne v) < ⊤ →
      Nonempty (SymmetricScalarFormSource (A := A) (K := K) electrons energy μ multiplier v)) :
    ElectronicCutoffData (A := A) (Ω := Fin electrons → ElectronicPosition)
      (K := K) (α := Fin electrons → Bool) (ι := Fin electrons × Fin 3) energy :=
  ElectronicCutoffData.ofPhysicalPartition electrons energy μ
    (fun l a => multiplier (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) a))
    (fun l => compression (symmetricMultiplier (electronicPair ((l : ℝ) + 1)) (fun _ => false)))
    (fun l => hcompression _ (symmetricElectronicPartition_admissible electrons l _)
      (symmetricElectronicPartition_perm _ _))
    (fun l v hv => ⟨(source v hv).some.partition l⟩)

end UniversalScalarCalculus

end GptLean.PhotonLocalization
