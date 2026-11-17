import GptLean.Gaussian.WienerSegal
import GptLean.Repair.TraceChannel
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Sequences

/-!
Covariant slicing from an actual Wiener--Itô--Segal unitary into a Bochner
L2 space. The representative, its linearity almost everywhere, its norm and
its inner products are derived from the unitary. Separate hard and soft
intertwinings on a core imply covariant intertwining there. A closed fibre
graph then extends this to every graph limit, with fibre domain membership
as part of the conclusion.

The physical choice of the unitary, core, hard operator and soft multiplication
operator remains explicit background. No identity on the full covariant
domain or exchange of a current series with its integral is assumed.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace GptLean.Gaussian

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Q H K : Type*} [MeasurableSpace Q] {μ : Measure Q}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The standard L2 representative of the unitary image. -/
def unitaryFiber (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : H) : Q → K := U ψ

theorem unitaryFiber_memLp (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : H) :
    MemLp (unitaryFiber U ψ) 2 μ := Lp.memLp _

theorem unitaryFiber_sub_smul (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (ψ φ : H) (e : ℂ) :
    unitaryFiber U (ψ - e • φ) =ᵐ[μ]
      fun q => unitaryFiber U ψ q - e • unitaryFiber U φ q := by
  simp only [unitaryFiber, map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (U ψ) (e • U φ), Lp.coeFn_smul e (U φ)] with q hq hφ
  simp only [Pi.sub_apply, Pi.smul_apply] at hq hφ
  rw [hq, hφ]

theorem unitaryFiber_norm_sq_integrable (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : H) :
    Integrable (fun q => ‖unitaryFiber U ψ q‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (unitaryFiber_memLp U ψ).1).mp
    (unitaryFiber_memLp U ψ)

theorem unitaryFiber_norm_sq (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : H) :
    ∫ q, ‖unitaryFiber U ψ q‖ ^ 2 ∂μ = ‖ψ‖ ^ 2 := by
  have h := GptLean.Repair.toL2_norm_sq (unitaryFiber_memLp U ψ)
  simp only [unitaryFiber] at h
  rw [Lp.toLp_coeFn] at h
  simpa only [unitaryFiber, U.norm_map] using h.symm

theorem unitaryFiber_lintegral_norm_sq (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : H) :
    ∫⁻ q, ENNReal.ofReal (‖unitaryFiber U ψ q‖ ^ 2) ∂μ =
      ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (unitaryFiber_norm_sq_integrable U ψ)
    (Eventually.of_forall (fun _ => sq_nonneg _)), unitaryFiber_norm_sq]

theorem unitaryFiber_inner (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ φ : H) :
    inner ℂ ψ φ = ∫ q, inner ℂ (unitaryFiber U ψ q) (unitaryFiber U φ q) ∂μ := by
  rw [← U.inner_map_map ψ φ, L2.inner_def]
  rfl

/-- The earlier Gaussian interface is obtained from the actual unitary.
Only the standard field multiplication intertwining is supplied. -/
def WienerSegalData.ofUnitary {G : Type*} (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (fieldDomain : G → H → Prop) (field : G → H → H)
    (coordinate : G → Q → ℝ)
    (hfield : ∀ g ψ, fieldDomain g ψ → unitaryFiber U (field g ψ) =ᵐ[μ]
      fun q => coordinate g q • unitaryFiber U ψ q) : WienerSegalData Q H K G μ where
  toFiber := unitaryFiber U
  measurable_fiber ψ := (unitaryFiber_memLp U ψ).1
  norm_sq := unitaryFiber_lintegral_norm_sq U
  fieldDomain := fieldDomain
  field := field
  coordinate := coordinate
  intertwining := hfield

/-- The source bounded test obtained by conjugating the actual fibre test. -/
def unitaryTest (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (B : K →L[ℂ] K) : H →L[ℂ] H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((B.compLpL 2 μ).comp U.toContinuousLinearEquiv.toContinuousLinearMap)

theorem unitaryTest_fiber (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (ψ : H) :
    unitaryFiber U (unitaryTest U B ψ) =ᵐ[μ] fun q => B (unitaryFiber U ψ q) := by
  change ⇑(U (U.symm (B.compLpL 2 μ (U ψ)))) =ᵐ[μ] _
  rw [U.apply_symm_apply]
  exact B.coeFn_compLpL _

theorem unitaryTest_norm_le (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (ψ : H) : ‖unitaryTest U B ψ‖ ≤ ‖B‖ * ‖ψ‖ := by
  change ‖U.symm (B.compLp (U ψ))‖ ≤ _
  rw [U.symm.norm_map]
  simpa only [U.norm_map] using B.norm_compLp_le (U ψ)

/-- A bounded current test is integrable, and unitarity gives its exact slice integral. -/
theorem unitary_tested_current (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (ψ dψ : H) :
    Integrable (fun q => inner ℂ (unitaryFiber U ψ q) (B (unitaryFiber U dψ q))) μ ∧
    inner ℂ ψ (unitaryTest U B dψ) =
      ∫ q, inner ℂ (unitaryFiber U ψ q) (B (unitaryFiber U dψ q)) ∂μ := by
  have heq := unitaryTest_fiber U B dψ
  constructor
  · apply (L2.integrable_inner (𝕜 := ℂ) (U ψ) (U (unitaryTest U B dψ))).congr
    filter_upwards [heq] with q hq
    exact congrArg (inner ℂ (unitaryFiber U ψ q)) hq
  · rw [unitaryFiber_inner U]
    apply integral_congr_ae
    filter_upwards [heq] with q hq
    rw [hq]

/-- Covariant core intertwining follows from the two component intertwinings.
The fibres of the source vector belong to the intersection of the hard and
soft domains, hence to the domain of their difference. -/
theorem unitary_covariant_core_graph
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (A F : H →ₗ.[ℂ] H)
    (Aq Fq : Q → K →ₗ.[ℂ] K) (e : ℂ) (ψ : (A - e • F).domain)
    (hA : ∀ᵐ q ∂μ, (unitaryFiber U (ψ : H) q,
      unitaryFiber U (A ⟨ψ, ψ.property.1⟩) q) ∈ (Aq q).graph)
    (hF : ∀ᵐ q ∂μ, (unitaryFiber U (ψ : H) q,
      unitaryFiber U (F ⟨ψ, ψ.property.2⟩) q) ∈ (Fq q).graph) :
    ∀ᵐ q ∂μ, (unitaryFiber U (ψ : H) q,
      unitaryFiber U ((A - e • F) ψ) q) ∈ (Aq q - e • Fq q).graph := by
  have heq := unitaryFiber_sub_smul U (A ⟨ψ, ψ.property.1⟩)
    (F ⟨ψ, ψ.property.2⟩) e
  filter_upwards [hA, hF, heq] with q hAq hFq hq
  rcases (Aq q).mem_graph_iff.mp hAq with ⟨a, ha, hda⟩
  rcases (Fq q).mem_graph_iff.mp hFq with ⟨f, hf, hdf⟩
  dsimp only at ha hf hda hdf
  have ham : unitaryFiber U (ψ : H) q ∈ (Aq q).domain := by
    rw [← ha]
    exact a.property
  have hfm : unitaryFiber U (ψ : H) q ∈ (Fq q).domain := by
    rw [← hf]
    exact f.property
  refine (Aq q - e • Fq q).mem_graph_iff.mpr ⟨⟨unitaryFiber U (ψ : H) q,
    ⟨ham, hfm⟩⟩, rfl, ?_⟩
  change Aq q ⟨unitaryFiber U (ψ : H) q, _⟩ -
    e • Fq q ⟨unitaryFiber U (ψ : H) q, _⟩ = _
  have hea : (⟨unitaryFiber U (ψ : H) q, ham⟩ : (Aq q).domain) = a :=
    Subtype.ext ha.symm
  have hef : (⟨unitaryFiber U (ψ : H) q, hfm⟩ : (Fq q).domain) = f :=
    Subtype.ext hf.symm
  rw [hea, hef, hda, hdf]
  exact hq.symm

/-- L2 convergence of vectors and derivatives transports a fibre graph
identity to the limit. Closedness proves fibre domain membership as well as
the derivative identity. The two subsequences share one exceptional null set. -/
theorem unitary_closed_graph_limit
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (C : Q → K →ₗ.[ℂ] K)
    (hC : ∀ᵐ q ∂μ, (C q).IsClosed)
    {ψ dψ : H} {ψn dψn : ℕ → H}
    (hψ : Tendsto ψn atTop (𝓝 ψ)) (hdψ : Tendsto dψn atTop (𝓝 dψ))
    (hgraph : ∀ n, ∀ᵐ q ∂μ,
      (unitaryFiber U (ψn n) q, unitaryFiber U (dψn n) q) ∈ (C q).graph) :
    ∀ᵐ q ∂μ, ∃ v : (C q).domain,
      (v : K) = unitaryFiber U ψ q ∧ C q v = unitaryFiber U dψ q := by
  obtain ⟨ns, hns, hψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((U.continuous.tendsto ψ).comp hψ)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hdψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      (((U.continuous.tendsto dψ).comp hdψ).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hC, hψae, hdψae, ae_all_iff.mpr hgraph] with q hc hq hdq hg
  apply ((C q).mem_graph_iff
    (x := (unitaryFiber U ψ q, unitaryFiber U dψ q))).mp
  apply hc.mem_of_tendsto
    ((hq.comp hms.tendsto_atTop).prodMk_nhds hdq)
  exact Eventually.of_forall (fun n => hg (ns (ms n)))

/-- A graph core suffices for slicing every vector in the full source domain. -/
theorem unitary_closed_graph_of_core
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (D : H →ₗ.[ℂ] H)
    (C : Q → K →ₗ.[ℂ] K) (hC : ∀ᵐ q ∂μ, (C q).IsClosed)
    (core : Set D.domain)
    (hdense : ∀ ψ : D.domain, ∃ ψn : ℕ → D.domain,
      (∀ n, ψn n ∈ core) ∧
      Tendsto (fun n => (ψn n : H)) atTop (𝓝 (ψ : H)) ∧
      Tendsto (fun n => D (ψn n)) atTop (𝓝 (D ψ)))
    (hcore : ∀ ψ ∈ core, ∀ᵐ q ∂μ,
      (unitaryFiber U (ψ : H) q, unitaryFiber U (D ψ) q) ∈ (C q).graph)
    (ψ : D.domain) :
    ∀ᵐ q ∂μ, ∃ v : (C q).domain,
      (v : K) = unitaryFiber U (ψ : H) q ∧ C q v = unitaryFiber U (D ψ) q := by
  obtain ⟨ψn, hn, hψ, hdψ⟩ := hdense ψ
  exact unitary_closed_graph_limit U C hC hψ hdψ (fun n => hcore _ (hn n))

/-- The standard operator-core predicate supplies the approximating sequence.
No graph convergence data need be given separately for individual vectors. -/
theorem unitary_closed_graph_of_hasCore
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (D : H →ₗ.[ℂ] H) (hD : D.IsClosed)
    (C : Q → K →ₗ.[ℂ] K) (hC : ∀ᵐ q ∂μ, (C q).IsClosed)
    (S : Submodule ℂ H) (hS : D.HasCore S)
    (hcore : ∀ ψ : S, ∀ᵐ q ∂μ,
      (unitaryFiber U (ψ : H) q,
        unitaryFiber U (D ⟨ψ, hS.le_domain ψ.property⟩) q) ∈ (C q).graph)
    (ψ : D.domain) :
    ∀ᵐ q ∂μ, ∃ v : (C q).domain,
      (v : K) = unitaryFiber U (ψ : H) q ∧ C q v = unitaryFiber U (D ψ) q := by
  have hcl : (D.domRestrict S).IsClosable :=
    hD.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hmem : ((ψ : H), D ψ) ∈ closure ((D.domRestrict S).graph : Set (H × H)) := by
    change ((ψ : H), D ψ) ∈ (D.domRestrict S).graph.topologicalClosure
    rw [hcl.graph_closure_eq_closure_graph, hS.closure_eq]
    exact D.mem_graph ψ
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose un hun hdun using fun n => (D.domRestrict S).mem_graph_iff.mp (hw n)
  let vn (n : ℕ) : D.domain := ⟨un n, (un n).property.2⟩
  have hvn (n : ℕ) : (vn n : H) = (w n).1 := hun n
  have hdvn (n : ℕ) : D (vn n) = (w n).2 := by
    exact hdun n
  have hv : Tendsto (fun n => (vn n : H)) atTop (𝓝 (ψ : H)) := by
    simpa only [hvn, Function.comp_def] using
      (continuous_fst.tendsto ((ψ : H), D ψ)).comp hwlim
  have hdv : Tendsto (fun n => D (vn n)) atTop (𝓝 (D ψ)) := by
    simpa only [hdvn, Function.comp_def] using
      (continuous_snd.tendsto ((ψ : H), D ψ)).comp hwlim
  apply unitary_closed_graph_limit U C hC hv hdv
  intro n
  exact hcore ⟨un n, (un n).property.1⟩

/-- Full covariant slicing from primitive core intertwinings. The source
operator agrees with hard minus soft on its standard graph core. The fibre
operator is the closed extension of the corresponding algebraic difference.
The all-domain intertwining and the fibre domain assertion are conclusions. -/
theorem unitary_covariant_slicing_of_hasCore
    (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (A F D : H →ₗ.[ℂ] H) (e : ℂ)
    (hD : D.IsClosed) (S : Submodule ℂ H) (hS : D.HasCore S)
    (hcommon : S ≤ (A - e • F).domain)
    (hsource : ∀ φ : S, D ⟨φ, hS.le_domain φ.property⟩ =
      (A - e • F) ⟨φ, hcommon φ.property⟩)
    (Aq Fq : Q → K →ₗ.[ℂ] K)
    (hclosed : ∀ᵐ q ∂μ, (Aq q - e • Fq q).IsClosable)
    (hA : ∀ φ : S, ∀ᵐ q ∂μ, (unitaryFiber U (φ : H) q,
      unitaryFiber U (A ⟨φ, (hcommon φ.property).1⟩) q) ∈ (Aq q).graph)
    (hF : ∀ φ : S, ∀ᵐ q ∂μ, (unitaryFiber U (φ : H) q,
      unitaryFiber U (F ⟨φ, (hcommon φ.property).2⟩) q) ∈ (Fq q).graph)
    (ψ : D.domain) :
    ∀ᵐ q ∂μ, ∃ v : (Aq q - e • Fq q).closure.domain,
      (v : K) = unitaryFiber U (ψ : H) q ∧
      (Aq q - e • Fq q).closure v = unitaryFiber U (D ψ) q := by
  apply unitary_closed_graph_of_hasCore U D hD
    (fun q => (Aq q - e • Fq q).closure)
    (hclosed.mono (fun _ h => h.closure_isClosed)) S hS _ ψ
  intro φ
  have hg := unitary_covariant_core_graph U A F Aq Fq e
    ⟨φ, hcommon φ.property⟩ (hA φ) (hF φ)
  filter_upwards [hg] with q hq
  have hq' := LinearPMap.le_graph_of_le (Aq q - e • Fq q).le_closure hq
  simpa only [hsource φ] using hq'

/-- Tonelli gives the mixed kinetic identity for any countable source family,
including infinite energy. Apply this to the covariant derivative vectors. -/
theorem unitary_kinetic_tonelli (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (dψ : ℕ → H) :
    ∫⁻ q, ∑' n, ENNReal.ofReal (‖unitaryFiber U (dψ n) q‖ ^ 2) ∂μ =
      ∑' n, ENNReal.ofReal (‖dψ n‖ ^ 2) := by
  have hm (n : ℕ) : AEMeasurable
      (fun q => ENNReal.ofReal (‖unitaryFiber U (dψ n) q‖ ^ 2)) μ :=
    (((unitaryFiber_memLp U (dψ n)).1.norm.pow 2).aemeasurable).ennreal_ofReal
  rw [lintegral_tsum hm]
  simp only [unitaryFiber_lintegral_norm_sq]

/-- Finite total quadratic source mass proves integrability and summability
of the actual fibre quadratic series. -/
theorem unitary_quadratic_series (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ : ℕ → H)
    (hs : Summable (fun n => ‖ψ n‖ ^ 2)) :
    Integrable (fun q => ∑' n, ‖unitaryFiber U (ψ n) q‖ ^ 2) μ ∧
    (∀ᵐ q ∂μ, Summable (fun n => ‖unitaryFiber U (ψ n) q‖ ^ 2)) ∧
    (∫ q, ∑' n, ‖unitaryFiber U (ψ n) q‖ ^ 2 ∂μ) = ∑' n, ‖ψ n‖ ^ 2 := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun q => ‖unitaryFiber U (ψ n) q‖ ^ 2) μ :=
    (unitaryFiber_memLp U (ψ n)).1.norm.pow 2
  have ht : ∑' n, ∫⁻ q, ‖‖unitaryFiber U (ψ n) q‖ ^ 2‖ₑ ∂μ ≠ ⊤ := by
    simp only [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _),
      unitaryFiber_lintegral_norm_sq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨integrable_series hm ht, ae_summable_of_finite_total hm ht, ?_⟩
  rw [bochner_series_integral hm ht]
  simp only [unitaryFiber_norm_sq]

/-- Finite mass and kinetic energy justify the current series interchange
and prove absolute integrability of the terms, rather than postulating it. -/
theorem unitary_current_series (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ dψ : ℕ → H)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkin : Summable (fun n => ‖dψ n‖ ^ 2)) :
    HasSum (fun n => inner ℂ (ψ n) (dψ n))
      (∫ q, ∑' n, inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q) ∂μ) ∧
    Summable (fun n => ∫ q,
      ‖inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)‖ ∂μ) := by
  obtain ⟨hmint, hm, -⟩ := unitary_quadratic_series U ψ hmass
  obtain ⟨hkint, hk, -⟩ := unitary_quadratic_series U dψ hkin
  have hc : ∀ᵐ q ∂μ, Summable (fun n =>
      inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)) := by
    filter_upwards [hm, hk] with q hmq hkq
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ ((hmq.add hkq).div_const 2)
    intro n
    have hi := norm_inner_le_norm (𝕜 := ℂ)
      (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)
    nlinarith [sq_nonneg (‖unitaryFiber U (ψ n) q‖ - ‖unitaryFiber U (dψ n) q‖)]
  simpa only [← unitaryFiber_inner] using GptLean.Repair.integrated_inner_series
    (fun n => (unitaryFiber_memLp U (ψ n)).1)
    (fun n => (unitaryFiber_memLp U (dψ n)).1)
    (hm.mono (fun _ h => h.hasSum)) (hk.mono (fun _ h => h.hasSum))
    (hc.mono (fun _ h => h.hasSum)) hmint hkint

theorem unitary_current_series_integrable (U : H ≃ₗᵢ[ℂ] Lp K 2 μ) (ψ dψ : ℕ → H)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkin : Summable (fun n => ‖dψ n‖ ^ 2)) :
    Integrable (fun q => ∑' n,
      inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)) μ := by
  have ha := (unitary_current_series U ψ dψ hmass hkin).2
  have hi (n : ℕ) : (∫⁻ q,
      ‖inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)‖ₑ ∂μ) =
      ENNReal.ofReal (∫ q,
        ‖inner ℂ (unitaryFiber U (ψ n) q) (unitaryFiber U (dψ n) q)‖ ∂μ) := by
    simp only [← ofReal_norm]
    exact (ofReal_integral_eq_lintegral_ofReal
      (L2.integrable_inner (𝕜 := ℂ) (U (ψ n)) (U (dψ n))).norm
      (Eventually.of_forall (fun _ => norm_nonneg _))).symm
  apply integrable_series (fun n =>
    (unitaryFiber_memLp U (ψ n)).1.inner (unitaryFiber_memLp U (dψ n)).1)
  simp only [hi]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun _ => integral_nonneg (fun _ => norm_nonneg _)) ha]
  exact ENNReal.ofReal_ne_top

/-- The mixed current formula includes arbitrary bounded electronic tests.
Absolute integrability follows from source mass and covariant energy alone. -/
theorem unitary_tested_current_series (U : H ≃ₗᵢ[ℂ] Lp K 2 μ)
    (B : K →L[ℂ] K) (ψ dψ : ℕ → H)
    (hmass : Summable (fun n => ‖ψ n‖ ^ 2))
    (hkin : Summable (fun n => ‖dψ n‖ ^ 2)) :
    HasSum (fun n => inner ℂ (ψ n) (unitaryTest U B (dψ n)))
      (∫ q, ∑' n, inner ℂ (unitaryFiber U (ψ n) q)
        (B (unitaryFiber U (dψ n) q)) ∂μ) ∧
    Summable (fun n => ∫ q,
      ‖inner ℂ (unitaryFiber U (ψ n) q) (B (unitaryFiber U (dψ n) q))‖ ∂μ) := by
  have hBkin : Summable (fun n => ‖unitaryTest U B (dψ n)‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hkin.mul_left (‖B‖ ^ 2))
    intro n
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (unitaryTest_norm_le U B (dψ n)) 2
  obtain ⟨hs, ha⟩ := unitary_current_series U ψ
    (fun n => unitaryTest U B (dψ n)) hmass hBkin
  have hall := ae_all_iff.mpr (fun n => unitaryTest_fiber U B (dψ n))
  constructor
  · convert hs using 1
    apply integral_congr_ae
    filter_upwards [hall] with q hq
    simp only [hq]
  · convert ha using 1
    funext n
    apply integral_congr_ae
    filter_upwards [unitaryTest_fiber U B (dψ n)] with q hq
    rw [hq]

/-- The soft field contribution to the current is the real field times
the density. This identity applies pointwise in the electronic variables. -/
theorem real_soft_current_shift (v d : K) (e a : ℝ) :
    (inner ℂ v (d - ((e * a : ℝ) : ℂ) • v)).re =
      (inner ℂ v d).re - e * a * ‖v‖ ^ 2 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Global L2 control proves the Fubini passage for the unsummed current
on Gaussian parameter times electronic configuration space. -/
theorem current_fubini {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [SFinite μ] [SFinite ν] {p d : Q × X → K}
    (hp : MemLp p 2 (μ.prod ν)) (hd : MemLp d 2 (μ.prod ν)) :
    Integrable (fun y => inner ℂ (p y) (d y)) (μ.prod ν) ∧
    (∫ q, ∫ x, inner ℂ (p (q, x)) (d (q, x)) ∂ν ∂μ) =
      ∫ x, ∫ q, inner ℂ (p (q, x)) (d (q, x)) ∂μ ∂ν := by
  have hi : Integrable (fun y => inner ℂ (p y) (d y)) (μ.prod ν) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (hp.toLp p) (hd.toLp d)).congr
    filter_upwards [hp.coeFn_toLp, hd.coeFn_toLp] with y hy hdᵧ
    rw [hy, hdᵧ]
  exact ⟨hi, integral_integral_swap hi⟩

end GptLean.Gaussian
