import GptLean.PhysicalFockRadiationCore
import GptLean.SymmetricLift.L2Dominated
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Bounded energy cutoffs on the concrete photon Fock space. Both the cutoff
and its square-root radiation multiplier are actual sector multipliers.
The cutoff maps every Fock vector to the radiation graph and converges in
that graph on its domain.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal

set_option backward.isDefEq.respectTransparency.types false

private theorem symmetric_multiplier (n : ℕ) (a : (Fin n → PhotonMode) → ℝ)
    (ha : AEStronglyMeasurable a (SectorMeasure photonMeasure n))
    (B : ℝ) (hb : ∀ᵐ k ∂SectorMeasure photonMeasure n, |a k| ≤ B)
    (hs : ∀ π k, a (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = a k)
    (u : Sector photonMeasure n) :
    PhotonLocalization.realL2Multiplier a ha B hb u.val ∈ symmetricSubspace photonMeasure n := by
  intro π
  apply Lp.ext
  let v := PhotonLocalization.realL2Multiplier a ha B hb u.val
  have hv := PhotonLocalization.realL2Multiplier_apply a ha B hb u.val
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => photonMeasure) π
  filter_upwards [permutation_ae photonMeasure n π v, hv,
    hp.quasiMeasurePreserving.ae hv, symmetric_ae photonMeasure n u π]
    with k hpk hvk hvp hus
  change (permutation photonMeasure n π v) k = v k
  rw [hpk, hvk]
  change v (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = _
  rw [hvp, hs]
  exact congrArg (a k • ·) hus.symm

def symmetricMultiplier (n : ℕ) (a : (Fin n → PhotonMode) → ℝ)
    (ha : AEStronglyMeasurable a (SectorMeasure photonMeasure n))
    (B : ℝ) (hb : ∀ᵐ k ∂SectorMeasure photonMeasure n, |a k| ≤ B)
    (hs : ∀ π k, a (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = a k) :
    Sector photonMeasure n →L[ℂ] Sector photonMeasure n :=
  ((PhotonLocalization.realL2Multiplier a ha B hb).comp
    (sectorInclusion photonMeasure n).toContinuousLinearMap).codRestrict
      (symmetricSubspace photonMeasure n) (symmetric_multiplier n a ha B hb hs)

theorem symmetricMultiplier_ae (n : ℕ) (a : (Fin n → PhotonMode) → ℝ)
    (ha : AEStronglyMeasurable a (SectorMeasure photonMeasure n))
    (B : ℝ) (hb : ∀ᵐ k ∂SectorMeasure photonMeasure n, |a k| ≤ B)
    (hs : ∀ π k, a (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = a k)
    (u : Sector photonMeasure n) :
    (symmetricMultiplier n a ha B hb hs u).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => a k • u.val k :=
  PhotonLocalization.realL2Multiplier_apply a ha B hb u.val

theorem symmetricMultiplier_norm_le (n : ℕ) (a : (Fin n → PhotonMode) → ℝ)
    (ha : AEStronglyMeasurable a (SectorMeasure photonMeasure n))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ k ∂SectorMeasure photonMeasure n, |a k| ≤ B)
    (hs : ∀ π k, a (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = a k) :
    ‖symmetricMultiplier n a ha B hb hs‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  exact PhotonLocalization.realL2Multiplier_norm_le a ha B hb u.val

def energyCutoffWeight (M n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  if Real.sqrt (sectorDispersion n k) ≤ (M : ℝ) + 1 then 1 else 0

def energyRootCutoffWeight (M n : ℕ) (k : Fin n → PhotonMode) : ℝ :=
  Real.sqrt (sectorDispersion n k) * energyCutoffWeight M n k

theorem energyCutoffWeight_measurable (M n : ℕ) : Measurable (energyCutoffWeight M n) :=
  Measurable.ite (measurableSet_le (sectorDispersion_measurable n).sqrt measurable_const)
    measurable_const measurable_const

theorem energyRootCutoffWeight_measurable (M n : ℕ) :
    Measurable (energyRootCutoffWeight M n) :=
  (sectorDispersion_measurable n).sqrt.mul (energyCutoffWeight_measurable M n)

theorem energyCutoffWeight_bound (M n : ℕ) (k : Fin n → PhotonMode) :
    |energyCutoffWeight M n k| ≤ 1 := by
  unfold energyCutoffWeight
  split_ifs <;> norm_num

theorem energyRootCutoffWeight_bound (M n : ℕ) (k : Fin n → PhotonMode) :
    |energyRootCutoffWeight M n k| ≤ (M : ℝ) + 1 := by
  unfold energyRootCutoffWeight energyCutoffWeight
  split_ifs with h
  · simpa only [mul_one, abs_of_nonneg (Real.sqrt_nonneg _)] using h
  · simp only [mul_zero, abs_zero]
    positivity

theorem energyCutoffWeight_permutation (M n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    energyCutoffWeight M n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      energyCutoffWeight M n k := by
  simp only [energyCutoffWeight, sectorDispersion_permutation]

theorem energyRootCutoffWeight_permutation (M n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    energyRootCutoffWeight M n
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      energyRootCutoffWeight M n k := by
  simp only [energyRootCutoffWeight, sectorDispersion_permutation,
    energyCutoffWeight_permutation]

def sectorEnergyCutoff (M n : ℕ) : Sector photonMeasure n →L[ℂ] Sector photonMeasure n :=
  symmetricMultiplier n (energyCutoffWeight M n)
    (energyCutoffWeight_measurable M n).aestronglyMeasurable 1
    (ae_of_all _ (energyCutoffWeight_bound M n)) (energyCutoffWeight_permutation M n)

def sectorEnergyRootCutoff (M n : ℕ) : Sector photonMeasure n →L[ℂ] Sector photonMeasure n :=
  symmetricMultiplier n (energyRootCutoffWeight M n)
    (energyRootCutoffWeight_measurable M n).aestronglyMeasurable ((M : ℝ) + 1)
    (ae_of_all _ (energyRootCutoffWeight_bound M n)) (energyRootCutoffWeight_permutation M n)

theorem sectorEnergyCutoff_norm_le (M n : ℕ) : ‖sectorEnergyCutoff M n‖ ≤ 1 :=
  symmetricMultiplier_norm_le _ _ _ _ zero_le_one _ _

theorem sectorEnergyRootCutoff_norm_le (M n : ℕ) :
    ‖sectorEnergyRootCutoff M n‖ ≤ (M : ℝ) + 1 :=
  symmetricMultiplier_norm_le _ _ _ _ (by positivity) _ _

theorem sectorEnergyCutoff_ae (M n : ℕ) (u : Sector photonMeasure n) :
    (sectorEnergyCutoff M n u).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => energyCutoffWeight M n k • u.val k :=
  symmetricMultiplier_ae _ _ _ _ _ _ _

def energyCutoff (M : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  lp.mapCLM 2 (sectorEnergyCutoff M) zero_le_one (sectorEnergyCutoff_norm_le M)

def energyRootCutoff (M : ℕ) : PhotonFock →L[ℂ] PhotonFock :=
  lp.mapCLM 2 (sectorEnergyRootCutoff M) (by positivity) (sectorEnergyRootCutoff_norm_le M)

theorem energyCutoff_norm_le (M : ℕ) : ‖energyCutoff M‖ ≤ 1 :=
  lp.norm_mapCLM_le _ _ _ _

theorem energyRootCutoff_norm_le (M : ℕ) : ‖energyRootCutoff M‖ ≤ (M : ℝ) + 1 :=
  lp.norm_mapCLM_le _ _ _ _

theorem energyCutoff_ae (M n : ℕ) (u : PhotonFock) :
    (energyCutoff M u n).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => energyCutoffWeight M n k • (u n).val k :=
  symmetricMultiplier_ae _ _ _ _ _ _ _

theorem energyRootCutoff_ae (M n : ℕ) (u : PhotonFock) :
    (energyRootCutoff M u n).val =ᵐ[SectorMeasure photonMeasure n]
      fun k => energyRootCutoffWeight M n k • (u n).val k :=
  symmetricMultiplier_ae _ _ _ _ _ _ _

theorem energyCutoff_graph (M : ℕ) (u : PhotonFock) :
    (energyCutoff M u, energyRootCutoff M u) ∈ radiationRoot.graph := by
  apply (radiationRoot_graph_iff _ _).mpr
  intro n
  filter_upwards [energyCutoff_ae M n u, energyRootCutoff_ae M n u] with k hv hd
  rw [hv, hd]
  simp only [energyRootCutoffWeight, mul_smul, Complex.real_smul]

/-- The bounded energy cutoff has its range in the actual radiation graph. -/
def radiationEnergyCutoff (M : ℕ) : PhotonFock →L[ℂ] RadiationGraphSpace :=
  ((energyCutoff M).prod (energyRootCutoff M)).codRestrict radiationRoot.graph
    (energyCutoff_graph M)

@[simp] theorem inclusion_radiationEnergyCutoff (M : ℕ) (u : PhotonFock) :
    radiationGraphInclusion (radiationEnergyCutoff M u) = energyCutoff M u := rfl

@[simp] theorem derivative_radiationEnergyCutoff (M : ℕ) (u : PhotonFock) :
    radiationGraphDerivative (radiationEnergyCutoff M u) = energyRootCutoff M u := rfl

theorem energyRootCutoff_commute (M : ℕ) (q : RadiationGraphSpace) :
    energyRootCutoff M (radiationGraphInclusion q) =
      energyCutoff M (radiationGraphDerivative q) := by
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [energyRootCutoff_ae M n (radiationGraphInclusion q),
    energyCutoff_ae M n (radiationGraphDerivative q),
    (radiationRoot_graph_iff _ _).mp q.property n] with k hr hv hq
  rw [hr, hv]
  change energyRootCutoffWeight M n k • (q.val.1 n).val k =
    energyCutoffWeight M n k • (q.val.2 n).val k
  rw [hq]
  simp only [energyRootCutoffWeight, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem energyCutoffWeight_tendsto (n : ℕ) (k : Fin n → PhotonMode) :
    Tendsto (fun M => energyCutoffWeight M n k) atTop (𝓝 1) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.sqrt (sectorDispersion n k))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop M] with m hm
  have h : Real.sqrt (sectorDispersion n k) ≤ (m : ℝ) + 1 :=
    hM.trans ((Nat.cast_le.mpr hm).trans (le_add_of_nonneg_right zero_le_one))
  simp only [energyCutoffWeight, h, ↓reduceIte]

theorem sectorEnergyCutoff_tendsto (n : ℕ) (u : Sector photonMeasure n) :
    Tendsto (fun M => sectorEnergyCutoff M n u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ u.val).mpr
  apply SymmetricLift.tendsto_eLpNorm_two_of_dominated_sq
    (b := fun k => ‖u.val k‖ ^ 2)
    (fun M => Lp.aestronglyMeasurable (sectorEnergyCutoff M n u).val)
    (Lp.aestronglyMeasurable u.val)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u.val)).mp (Lp.memLp u.val))
  · intro M
    filter_upwards [sectorEnergyCutoff_ae M n u] with k hk
    rw [hk, norm_smul, Real.norm_eq_abs]
    apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (energyCutoffWeight_bound M n k) (norm_nonneg (u.val k))
  · exact ae_of_all _ fun _ => le_rfl
  · filter_upwards [ae_all_iff.mpr (fun M => sectorEnergyCutoff_ae M n u)] with k hk
    simpa only [hk, one_smul] using (energyCutoffWeight_tendsto n k).smul_const (u.val k)

theorem energyCutoff_tendsto (u : PhotonFock) :
    Tendsto (fun M => energyCutoff M u) atTop (𝓝 u) := by
  have hsum : Summable (fun n => 4 * ‖u n‖ ^ 2) :=
    (coordinate_mass_hasSum (Sector photonMeasure) u).summable.mul_left 4
  have ht := tendsto_tsum_of_dominated_convergence hsum
    (f := fun M n => ‖sectorEnergyCutoff M n (u n) - u n‖ ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun n => by simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((sectorEnergyCutoff_tendsto n (u n)).sub (tendsto_const_nhds (x := u n))).norm.pow 2)
    (Eventually.of_forall fun M n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hc : ‖sectorEnergyCutoff M n (u n)‖ ≤ ‖u n‖ := by
        simpa only [one_mul] using
          (sectorEnergyCutoff M n).le_of_opNorm_le (sectorEnergyCutoff_norm_le M n) (u n)
      have hd := norm_sub_le (sectorEnergyCutoff M n (u n)) (u n)
      have hn := norm_nonneg (sectorEnergyCutoff M n (u n) - u n)
      nlinarith [norm_nonneg (u n)])
  have hsquare : Tendsto (fun M => ‖energyCutoff M u - u‖ ^ 2) atTop (𝓝 0) := by
    have heq (M : ℕ) :
        (∑' n, ‖sectorEnergyCutoff M n (u n) - u n‖ ^ 2) =
          ‖energyCutoff M u - u‖ ^ 2 :=
      (coordinate_mass_hasSum (Sector photonMeasure) (energyCutoff M u - u)).tsum_eq
    simpa only [heq, tsum_zero] using ht
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero, dist_eq_norm] using hnorm

/-- Convergence holds in both coordinates of the closed radiation graph. -/
theorem radiationEnergyCutoff_tendsto (q : RadiationGraphSpace) :
    Tendsto (fun M => radiationEnergyCutoff M (radiationGraphInclusion q))
      atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun M =>
    (energyCutoff M q.val.1, energyRootCutoff M q.val.1)) atTop (𝓝 q.val)
  have hc (M : ℕ) : energyRootCutoff M q.val.1 = energyCutoff M q.val.2 :=
    energyRootCutoff_commute M q
  simp only [hc]
  exact (energyCutoff_tendsto q.val.1).prodMk_nhds (energyCutoff_tendsto q.val.2)

def radiationGraphCutoff (M : ℕ) : RadiationGraphSpace →L[ℂ] RadiationGraphSpace :=
  (radiationEnergyCutoff M).comp radiationGraphInclusion

theorem radiationGraphCutoff_norm_le (M : ℕ) : ‖radiationGraphCutoff M‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  have hv : ‖energyCutoff M q.val.1‖ ≤ ‖q.val.1‖ := by
    simpa only [one_mul] using
      (energyCutoff M).le_of_opNorm_le (energyCutoff_norm_le M) q.val.1
  have hd : ‖energyCutoff M q.val.2‖ ≤ ‖q.val.2‖ := by
    simpa only [one_mul] using
      (energyCutoff M).le_of_opNorm_le (energyCutoff_norm_le M) q.val.2
  change max ‖energyCutoff M q.val.1‖ ‖energyRootCutoff M q.val.1‖ ≤
    1 * max ‖q.val.1‖ ‖q.val.2‖
  rw [show energyRootCutoff M q.val.1 = energyCutoff M q.val.2 from
    energyRootCutoff_commute M q, one_mul]
  exact max_le_max hv hd

theorem radiationGraphCutoff_tendsto (q : RadiationGraphSpace) :
    Tendsto (fun M => radiationGraphCutoff M q) atTop (𝓝 q) :=
  radiationEnergyCutoff_tendsto q

end GptLean.PhysicalFock
