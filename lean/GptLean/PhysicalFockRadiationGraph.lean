import GptLean.PhysicalFockRadiation
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
The actual closed square-root radiation graph on the same photon Fock space.

Its domain consists of vectors whose sectorwise square-root momentum
multiplier is another vector in this Fock space. Closedness follows from
almost-everywhere subsequences of L² limits. The squared norm of the
multiplier output equals the momentum form, and number sectors preserve the
graph with exact commutation.
-/

noncomputable section

namespace GptLean.PhysicalFock

open MeasureTheory Filter Topology
open scoped ENNReal

section ScalarGraph

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ)

private def scalarMultiplierGraph : Submodule ℂ (Lp ℂ 2 μ × Lp ℂ 2 μ) where
  carrier := {uv | ∀ᵐ x ∂μ, uv.2 x = a x * uv.1 x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simp only [Prod.fst_zero, Prod.snd_zero, hx, Pi.zero_apply, mul_zero]
  add_mem' := by
    intro u v hu hv
    filter_upwards [hu, hv, Lp.coeFn_add u.1 v.1, Lp.coeFn_add u.2 v.2]
      with x hux hvx hx hy
    change (u.2 + v.2) x = a x * (u.1 + v.1) x
    rw [hx, hy, Pi.add_apply, Pi.add_apply, hux, hvx, mul_add]
  smul_mem' := by
    intro c u hu
    filter_upwards [hu, Lp.coeFn_smul c u.1, Lp.coeFn_smul c u.2] with x hux hx hy
    change (c • u.2) x = a x * (c • u.1) x
    rw [hx, hy, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hux]
    ring

private theorem scalarMultiplierGraph_fst_zero (uv : Lp ℂ 2 μ × Lp ℂ 2 μ)
    (huv : uv ∈ scalarMultiplierGraph μ a) (hzero : uv.1 = 0) : uv.2 = 0 := by
  apply Lp.ext
  filter_upwards [huv, Lp.coeFn_zero ℂ 2 μ] with x hx hz
  rw [hzero, hz, Pi.zero_apply, mul_zero] at hx
  exact hx.trans (by rw [hz, Pi.zero_apply])

private theorem scalarMultiplierGraph_closed :
    IsClosed (scalarMultiplierGraph μ a : Set (Lp ℂ 2 μ × Lp ℂ 2 μ)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro uv z huv hz
  have hfst := (continuous_fst.tendsto z).comp hz
  have hsnd := (continuous_snd.tendsto z).comp hz
  obtain ⟨ns, hns, hfstAE⟩ := (tendstoInMeasure_of_tendsto_Lp hfst).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hsndAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hsnd.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hfstAE, hsndAE, ae_all_iff.mpr huv] with x hfx hgx hgraph
  have hm : Tendsto (fun j => a x * (uv (ns (ms j))).1 x) atTop (𝓝 (a x * z.1 x)) :=
    tendsto_const_nhds.mul (hfx.comp hms.tendsto_atTop)
  exact tendsto_nhds_unique hgx
    (hm.congr (fun j => (hgraph (ns (ms j))).symm))

end ScalarGraph

/-- Continuous extraction of the concrete n-photon wave function. -/
def sectorWavefunction (n : ℕ) : PhotonFock →L[ℂ] FullSector photonMeasure n :=
  (sectorInclusion photonMeasure n).toContinuousLinearMap.comp
    (lp.evalCLM ℂ (Sector photonMeasure) 2 n)

@[simp] theorem sectorWavefunction_apply (n : ℕ) (u : PhotonFock) :
    sectorWavefunction n u = (u n).val := rfl

private def rootCoordinatePair (n : ℕ) :
    PhotonFock × PhotonFock →L[ℂ] FullSector photonMeasure n × FullSector photonMeasure n :=
  (sectorWavefunction n).prodMap (sectorWavefunction n)

private def radiationRootGraph : Submodule ℂ (PhotonFock × PhotonFock) :=
  ⨅ n, (scalarMultiplierGraph (SectorMeasure photonMeasure n)
    (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))).comap
      (rootCoordinatePair n).toLinearMap

private theorem mem_radiationRootGraph (u v : PhotonFock) :
    (u, v) ∈ radiationRootGraph ↔ ∀ n, ∀ᵐ k ∂SectorMeasure photonMeasure n,
      (v n).val k = (Real.sqrt (sectorDispersion n k) : ℂ) * (u n).val k := by
  simp only [radiationRootGraph, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

private theorem radiationRootGraph_fst_zero (uv : PhotonFock × PhotonFock)
    (huv : uv ∈ radiationRootGraph) (hzero : uv.1 = 0) : uv.2 = 0 := by
  apply lp.ext
  funext n
  apply Subtype.ext
  apply scalarMultiplierGraph_fst_zero (SectorMeasure photonMeasure n)
    (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    (rootCoordinatePair n uv)
  · exact (Submodule.mem_iInf _).mp huv n
  · change sectorWavefunction n uv.1 = 0
    rw [hzero, map_zero]

private theorem radiationRootGraph_closed :
    IsClosed (radiationRootGraph : Set (PhotonFock × PhotonFock)) := by
  have he : (radiationRootGraph : Set (PhotonFock × PhotonFock)) =
      {uv | ∀ n, rootCoordinatePair n uv ∈
    scalarMultiplierGraph (SectorMeasure photonMeasure n)
      (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))} := by
    ext uv
    change uv ∈ radiationRootGraph ↔ ∀ n, rootCoordinatePair n uv ∈
      scalarMultiplierGraph (SectorMeasure photonMeasure n)
        (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))
    simp only [radiationRootGraph, Submodule.mem_iInf, Submodule.mem_comap]
    rfl
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun n =>
    (scalarMultiplierGraph_closed (SectorMeasure photonMeasure n)
      (fun k => (Real.sqrt (sectorDispersion n k) : ℂ))).preimage
      (rootCoordinatePair n).continuous

/-- The maximal square-root momentum multiplication operator on this Fock space. -/
def radiationRoot : PhotonFock →ₗ.[ℂ] PhotonFock := radiationRootGraph.toLinearPMap

private theorem radiationRoot_graph : radiationRoot.graph = radiationRootGraph :=
  Submodule.toLinearPMap_graph_eq _ radiationRootGraph_fst_zero

theorem radiationRoot_graph_iff (u v : PhotonFock) :
    (u, v) ∈ radiationRoot.graph ↔ ∀ n, ∀ᵐ k ∂SectorMeasure photonMeasure n,
      (v n).val k = (Real.sqrt (sectorDispersion n k) : ℂ) * (u n).val k := by
  rw [radiationRoot_graph]
  exact mem_radiationRootGraph u v

theorem radiationRoot_domain_iff (u : PhotonFock) :
    u ∈ radiationRoot.domain ↔ ∃ v : PhotonFock, ∀ n, ∀ᵐ k ∂SectorMeasure photonMeasure n,
      (v n).val k = (Real.sqrt (sectorDispersion n k) : ℂ) * (u n).val k := by
  rw [LinearPMap.mem_domain_iff]
  exact exists_congr fun v => radiationRoot_graph_iff u v

theorem radiationRoot_closed : radiationRoot.IsClosed := by
  change IsClosed (radiationRoot.graph : Set (PhotonFock × PhotonFock))
  rw [radiationRoot_graph]
  exact radiationRootGraph_closed

theorem sectorRadiationForm_eq_root_norm (n : ℕ) (u v : Sector photonMeasure n)
    (h : ∀ᵐ k ∂SectorMeasure photonMeasure n,
      v.val k = (Real.sqrt (sectorDispersion n k) : ℂ) * u.val k) :
    sectorRadiationForm n u = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← sector_mass_lintegral n v]
  unfold sectorRadiationForm
  apply lintegral_congr_ae
  filter_upwards [h] with k hk
  rw [hk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sectorDispersion_nonneg n k),
    ENNReal.ofReal_mul (sectorDispersion_nonneg n k)]

/-- The squared norm of the multiplier output is exactly the momentum form. -/
theorem radiationRoot_energy (u : radiationRoot.domain) :
    radiationForm u.val = ENNReal.ofReal (‖radiationRoot u‖ ^ 2) := by
  have h := (radiationRoot_graph_iff u.val (radiationRoot u)).mp (radiationRoot.mem_graph u)
  unfold radiationForm
  simp_rw [sectorRadiationForm_eq_root_norm _ _ _ (h _)]
  simpa only [weightedForm, one_mul] using massForm_eq (Sector photonMeasure) (radiationRoot u)

theorem radiationRoot_sector_graph (n : ℕ) (u : radiationRoot.domain) :
    (photonSector photonMeasure n u.val,
      photonSector photonMeasure n (radiationRoot u)) ∈ radiationRoot.graph := by
  apply (radiationRoot_graph_iff _ _).mpr
  intro m
  by_cases hmn : m = n
  · subst m
    simpa only [photonSector, sector_coordinate] using
      (radiationRoot_graph_iff u.val (radiationRoot u)).mp (radiationRoot.mem_graph u) n
  · simp only [photonSector, sector_coordinate_ne _ n m hmn]
    filter_upwards [Lp.coeFn_zero ℂ 2 (SectorMeasure photonMeasure m)] with k hk
    change (0 : FullSector photonMeasure m) k =
      (Real.sqrt (sectorDispersion m k) : ℂ) * (0 : FullSector photonMeasure m) k
    rw [hk, Pi.zero_apply, mul_zero]

/-- The sector compatibility hypothesis required by the compactness endpoint. -/
theorem radiationRoot_sector_graph_of_mem (n : ℕ) (v w : PhotonFock)
    (h : (v, w) ∈ radiationRoot.graph) :
    (photonSector photonMeasure n v, photonSector photonMeasure n w) ∈ radiationRoot.graph := by
  obtain ⟨u, hu, hw⟩ := radiationRoot.mem_graph_iff.mp h
  simpa only [hu, hw] using radiationRoot_sector_graph n u

theorem sectorDispersion_permutation (n : ℕ) (π : Equiv.Perm (Fin n))
    (k : Fin n → PhotonMode) :
    sectorDispersion n (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      sectorDispersion n k := by
  unfold sectorDispersion
  rw [← Equiv.sum_comp π (fun i =>
    ‖((MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) i).1‖)]
  simp only [MeasurableEquiv.piCongrLeft_apply_apply]

/-- Finite momentum energy supplies an actual symmetric square-root multiplier output. -/
theorem exists_sectorRoot_of_finite (n : ℕ) (u : Sector photonMeasure n)
    (hE : sectorRadiationForm n u < ⊤) :
    ∃ v : Sector photonMeasure n, ∀ᵐ k ∂SectorMeasure photonMeasure n,
      v.val k = (Real.sqrt (sectorDispersion n k) : ℂ) * u.val k := by
  let f : (Fin n → PhotonMode) → ℂ :=
    fun k => (Real.sqrt (sectorDispersion n k) : ℂ) * u.val k
  have hc : Measurable (fun k => (Real.sqrt (sectorDispersion n k) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (sectorDispersion_measurable n).sqrt
  have hm : AEStronglyMeasurable f (SectorMeasure photonMeasure n) :=
    hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u.val)
  have he (k : Fin n → PhotonMode) : ‖f k‖ ^ 2 = sectorDispersion n k * ‖u.val k‖ ^ 2 := by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (sectorDispersion_nonneg n k)]
  have hf : MemLp f 2 (SectorMeasure photonMeasure n) := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    refine ⟨hm.norm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun k => sq_nonneg (‖f k‖))).mpr
    simpa only [he, ENNReal.ofReal_mul (sectorDispersion_nonneg n _), sectorRadiationForm] using hE
  let v : FullSector photonMeasure n := hf.toLp f
  have hv : v =ᵐ[SectorMeasure photonMeasure n] f := hf.coeFn_toLp
  have hvs : v ∈ symmetricSubspace photonMeasure n := by
    intro π
    apply Lp.ext
    have hp := measurePreserving_piCongrLeft (fun _ : Fin n => photonMeasure) π
    filter_upwards [permutation_ae photonMeasure n π v, hv,
      hp.quasiMeasurePreserving.ae hv, symmetric_ae photonMeasure n u π]
      with k hpv hvk hvp hus
    change (permutation photonMeasure n π v) k = v k
    rw [hpv, hvk]
    change v (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) = f k
    rw [hvp]
    simp only [f, sectorDispersion_permutation]
    rw [show u.val (MeasurableEquiv.piCongrLeft (fun _ : Fin n => PhotonMode) π k) =
      u.val k from hus.symm]
  exact ⟨⟨v, hvs⟩, hv⟩

/-- Every finite-energy Fock vector belongs to the actual square-root domain. -/
theorem radiationRoot_domain_of_finite (u : PhotonFock) (hE : radiationForm u < ⊤) :
    u ∈ radiationRoot.domain := by
  have hn (n : ℕ) : sectorRadiationForm n (u n) < ⊤ :=
    (ENNReal.le_tsum n).trans_lt hE
  choose v hv using fun n => exists_sectorRoot_of_finite n (u n) (hn n)
  have he (n : ℕ) : sectorRadiationForm n (u n) = ENNReal.ofReal (‖v n‖ ^ 2) :=
    sectorRadiationForm_eq_root_norm n (u n) (v n) (hv n)
  have hs : Summable (fun n => ‖v n‖ ^ 2) := by
    have ht : ∑' n, ENNReal.ofReal (‖v n‖ ^ 2) ≠ ⊤ := by
      simpa only [← he, radiationForm] using hE.ne
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht
  have hvlp : Memℓp v 2 := memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)
  exact (radiationRoot_domain_iff u).mpr ⟨⟨v, hvlp⟩, hv⟩

theorem radiationRoot_domain_iff_finite (u : PhotonFock) :
    u ∈ radiationRoot.domain ↔ radiationForm u < ⊤ := by
  constructor
  · intro hu
    rw [radiationRoot_energy ⟨u, hu⟩]
    exact ENNReal.ofReal_lt_top
  · exact radiationRoot_domain_of_finite u

end GptLean.PhysicalFock
