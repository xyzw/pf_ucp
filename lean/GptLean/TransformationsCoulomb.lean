import GptLean.TransformationsTranslationStates
import GptLean.TransformationsDilationReference
import GptLean.PhysicalCoulombH1

/-!
The actual Coulomb interaction `∑_{i<j} |xᵢ - xⱼ|⁻¹` is invariant under
simultaneous translations of all electrons and homogeneous of degree `-1`
under dilations. Consequently the translation theorems apply to the actual
Coulomb model with the actual form-factor kernels, with no remaining
hypothesis on the potential or the kernels, and the dilation identities apply
to its Coulomb coordinate.
-/

noncomputable section

namespace GptLean.TransformationsCoulomb

open MeasureTheory PhysicalFock PhysicalPFReference SymmetricLift PhysicalPairSpace
  PhysicalNormalTrace PhysicalClosedForms TransformationsTranslation

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000

theorem particle_smul {N : ℕ} (x : Configuration N) (r : ℝ) (j : Fin N) :
    particle (r • x) j = r • particle x j := by
  ext a
  rfl

/-- Simultaneous translations of all electrons leave the Coulomb interaction invariant. -/
theorem potential_add_diag {N : ℕ} (x : Configuration N) (b : PhysicalPairSpace.Position) :
    PhysicalCoulombH1.potential N (x + diag b) = PhysicalCoulombH1.potential N x := by
  unfold PhysicalCoulombH1.potential
  simp only [particle_add_diag, add_sub_add_right_eq_sub]

/-- The Coulomb interaction is homogeneous of degree `-1`. -/
theorem potential_smul {N : ℕ} (x : Configuration N) {r : ℝ} (hr : 0 < r) :
    PhysicalCoulombH1.potential N (r • x) = r⁻¹ * PhysicalCoulombH1.potential N x := by
  unfold PhysicalCoulombH1.potential
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [particle_smul, particle_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mul_inv]
  · rw [mul_zero]

/-- The scaled Coulomb interaction `c ∑_{i<j} |xᵢ - xⱼ|⁻¹`. -/
abbrev coulomb (N : ℕ) (c : ℝ) : PhysicalPFReference.Position (Fin N × Fin 3) → ℝ :=
  fun x => c * PhysicalCoulombH1.potential N x

theorem coulomb_translation {N : ℕ} (c : ℝ) :
    ∀ x b, coulomb N c (x + diag b) = coulomb N c x := fun x b => by
  simp only [coulomb, potential_add_diag]

theorem coulomb_dilation {N : ℕ} (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ x, coulomb N c (r • x) = r⁻¹ * coulomb N c x := fun x => by
  simp only [coulomb, potential_smul x hr]
  ring

variable {N : ℕ} (c : ℝ) (b : PhysicalPairSpace.Position)
  (C : CanonicalSectorCCR photonMeasure) (e : ℝ) (i : Fin N)
  (B : StandardNormalTraceBackground) (S : StandardClosedFormBackground)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
  (F : PhotonLocalizationPhysicalKernels.FormFactors photonMeasure (Fin 3))
  (hF : F.momentum = Prod.fst) (J : Lp ℂ 2 photonMeasure ≃ₗᵢ[ℝ] T)

/-- **Translation invariance of `F_LL`** for the actual Coulomb Pauli--Fierz model
with the actual form-factor kernels:
`F_LL(ρ(· - b), j(· - b)) = F_LL(ρ, j)`. -/
theorem search_translation_coulomb (d : Pair) :
    DFT.search (TransformationsPureStates.pureModel (coulomb N c) C
        (PhysicalProfiles.momentumKernel F hF J) (PhysicalProfiles.momentumKernel_continuous F hF J)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.momentumKernel_bound F hF J)
        B S e i) (TransformationsPotentials.translatePair b d) =
      DFT.search (TransformationsPureStates.pureModel (coulomb N c) C
        (PhysicalProfiles.momentumKernel F hF J) (PhysicalProfiles.momentumKernel_continuous F hF J)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.momentumKernel_bound F hF J)
        B S e i) d :=
  search_translation_physical b (coulomb N c) (coulomb_translation c) C e i B S F hF J d

/-- **Translation invariance of the Lieb functional** for the actual Coulomb model. -/
theorem lieb_translation_coulomb (d : Pair) :
    DFT.lieb (TransformationsPureStates.pureModel (coulomb N c) C
        (PhysicalProfiles.momentumKernel F hF J) (PhysicalProfiles.momentumKernel_continuous F hF J)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.momentumKernel_bound F hF J)
        B S e i) (fun u p => PhysicalPairDuality.pairPotential u p)
        (TransformationsPotentials.translatePair b d) =
      DFT.lieb (TransformationsPureStates.pureModel (coulomb N c) C
        (PhysicalProfiles.momentumKernel F hF J) (PhysicalProfiles.momentumKernel_continuous F hF J)
        (PhysicalProfiles.kernelBound F hF J) (PhysicalProfiles.momentumKernel_bound F hF J)
        B S e i) (fun u p => PhysicalPairDuality.pairPotential u p) d :=
  lieb_translation b (coulomb N c) (coulomb_translation c) C _ _ _ _ e i
    (TransformationsKernelCovariance.kernelMap_translation F hF J b) B S d

section Dilation

open TransformationsDilation TransformationsFock

variable {I : Type} [Fintype I] [DecidableEq I] {r : ℝ} (hr : 0 < r)
  (C : CanonicalSectorCCR photonMeasure)

/-- A kernel-level dilation relation `κ_Λ(x) = λ Υ_λ† κ_{Λ/λ}(λ x)` gives the
field relation used by `energy_dilate`. -/
theorem kernel_relation (κ κ' : I → PhysicalPFReference.Position I → WeightedPhotonKernel)
    (hrel : ∀ i x, κ i x = r • kernelDilation r⁻¹ (inv_pos.mpr hr) (κ' i (r • x))) :
    ∀ i x q, kernelField C (κ i x) (TransformationsFock.radiationDilation r⁻¹ (inv_pos.mpr hr) q) =
      r • fockDilation r⁻¹ (inv_pos.mpr hr) (kernelField C (κ' i (r • x)) q) := by
  intro i x q
  have h : kernelField C (r • kernelDilation r⁻¹ (inv_pos.mpr hr) (κ' i (r • x))) =
      r • kernelField C (kernelDilation r⁻¹ (inv_pos.mpr hr) (κ' i (r • x))) :=
    (kernelFieldMap C).map_smul r (kernelDilation r⁻¹ (inv_pos.mpr hr) (κ' i (r • x)))
  exact (congrArg (fun k => kernelField C k (TransformationsFock.radiationDilation r⁻¹
    (inv_pos.mpr hr) q)) (hrel i x)).trans ((congrArg (fun L : RadiationGraphSpace →L[ℂ] PhotonFock =>
      L (TransformationsFock.radiationDilation r⁻¹ (inv_pos.mpr hr) q)) h).trans
        (congrArg (fun y => r • y) (kernelField_dilation r⁻¹ (inv_pos.mpr hr) C _ q)))

include hr in
theorem photon_radiation_factor :
    ‖((Real.sqrt r⁻¹ : ℝ) : ℂ)⁻¹‖ ^ 2 = r := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (inv_nonneg.mpr hr.le), inv_inv]

variable {N : ℕ} (c : ℝ)
  (κ κ' : Fin N × Fin 3 → PhysicalPFReference.Position (Fin N × Fin 3) → WeightedPhotonKernel)
  (hκ : ∀ i, AEStronglyMeasurable (κ i) volume) (hκ' : ∀ i, AEStronglyMeasurable (κ' i) volume)
  (M M' : ℝ) (hbound : ∀ i, ∀ᵐ x ∂volume, ‖κ i x‖ ≤ M)
  (hbound' : ∀ i, ∀ᵐ x ∂volume, ‖κ' i x‖ ≤ M')
  (hrel : ∀ i x, κ i x = r • kernelDilation r⁻¹ (inv_pos.mpr hr) (κ' i (r • x)))

/-- The physical dilation `V_λ = S_λ ⊗ Γ(Υ_λ†)` on the Coulomb reference domain. -/
abbrev physicalDilation (u : Reference (Fin N × Fin 3) (coulomb N c)) :
    Reference (Fin N × Fin 3) (coulomb N c) :=
  dilate hr (fockDilation r⁻¹ (inv_pos.mpr hr))
    (TransformationsFock.radiationDilation r⁻¹ (inv_pos.mpr hr))
    (radiationGraphInclusion_dilation r⁻¹ (inv_pos.mpr hr)) (coulomb N c)
    (coulomb_dilation c hr) u

include hrel in
/-- **The dilation identity `energy-scaling`** for the actual Coulomb model:
`E_Λ(V_λ u) = λ² K_{Λ/λ}(u) + λ R(u) + λ C(u)`. -/
theorem energy_scaling (e : ℝ) (u : Reference (Fin N × Fin 3) (coulomb N c)) :
    energy (Fin N × Fin 3) (coulomb N c) C κ hκ M hbound e (physicalDilation hr c u) =
      r ^ 2 * kineticEnergy (Fin N × Fin 3) (coulomb N c) C κ' hκ' M' hbound' e u +
        r * ‖radiation (Fin N × Fin 3) (coulomb N c) u‖ ^ 2 +
        r * ‖potential (Fin N × Fin 3) (coulomb N c) u‖ ^ 2 := by
  have h := energy_dilate hr (fockDilation r⁻¹ (inv_pos.mpr hr))
    (TransformationsFock.radiationDilation r⁻¹ (inv_pos.mpr hr)) _
    (radiationGraphInclusion_dilation r⁻¹ (inv_pos.mpr hr))
    (radiationGraphDerivative_dilation r⁻¹ (inv_pos.mpr hr)) (coulomb N c)
    (coulomb_dilation c hr) C κ κ' hκ hκ' M M' hbound hbound'
    (kernel_relation hr C κ κ' hrel) e u
  exact h.trans (congrArg (fun t : ℝ =>
    r ^ 2 * kineticEnergy (Fin N × Fin 3) (coulomb N c) C κ' hκ' M' hbound' e u +
      t * ‖radiation (Fin N × Fin 3) (coulomb N c) u‖ ^ 2 +
      r * ‖potential (Fin N × Fin 3) (coulomb N c) u‖ ^ 2) (photon_radiation_factor hr))

end Dilation

end GptLean.TransformationsCoulomb
