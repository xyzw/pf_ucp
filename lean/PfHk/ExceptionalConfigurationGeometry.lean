import PfHk.ConfigurationGeometry
import GptLean.PhysicalSourceCoordinates
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Collision-free configurations whose particles lie in a connected open
full-measure one-body set. Connectivity is proved from local collision
avoidance and product connectedness, without any further geometry input. -/

noncomputable section
namespace PfHk.ExceptionalConfigurationGeometry

open MeasureTheory Set GptLean.SymmetricLift
open GptLean.PhysicalSourceCoordinates (Position Spectator split split_measurePreserving)
open scoped Topology Convex

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 80000

/-- Configurations whose particle coordinates remain in the one-body region. -/
def particleDomain (Ω : Set Position) (N : ℕ) : Set (Configuration N) :=
  {X | ∀ n, (split n X).1 ∈ Ω}

/-- The regular configuration domain away from the exceptional one-body set. -/
def configurationDomain (Ω : Set Position) (N : ℕ) : Set (Configuration N) :=
  distinctConfigurations N ∩ particleDomain Ω N

@[simp] theorem mem_configurationDomain {Ω : Set Position} {N : ℕ} {X : Configuration N} :
    X ∈ configurationDomain Ω N ↔
      X ∈ distinctConfigurations N ∧ ∀ n, (split n X).1 ∈ Ω := Iff.rfl

theorem particleDomain_isOpen {Ω : Set Position} (hΩ : IsOpen Ω) (N : ℕ) :
    IsOpen (particleDomain Ω N) := by
  have heq : particleDomain Ω N =
      ⋂ n : Fin N, (fun X : Configuration N => (split n X).1) ⁻¹' Ω := by
    ext X
    simp [particleDomain]
  rw [heq]
  exact isOpen_iInter_of_finite fun n => hΩ.preimage (continuous_fst.comp (split n).continuous)

theorem configurationDomain_isOpen {Ω : Set Position} (hΩ : IsOpen Ω) (N : ℕ) :
    IsOpen (configurationDomain Ω N) :=
  (ConfigurationGeometry.regular_isOpen N).inter (particleDomain_isOpen hΩ N)

theorem particleDomain_ae {Ω : Set Position}
    (hfull : ∀ᵐ x : Position ∂volume, x ∈ Ω) (N : ℕ) :
    ∀ᵐ X : Configuration N ∂volume, X ∈ particleDomain Ω N := by
  have hn : ∀ n : Fin N, ∀ᵐ X : Configuration N ∂volume, (split n X).1 ∈ Ω := by
    intro n
    have hp : ∀ᵐ p : Position × Spectator n ∂(volume.prod volume), p.1 ∈ Ω :=
      (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure Position)) (ν := (volume : Measure (Spectator n)))).ae hfull
    exact (split_measurePreserving n).quasiMeasurePreserving.ae hp
  exact ae_all_iff.mpr hn

theorem configurationDomain_ae {Ω : Set Position}
    (hfull : ∀ᵐ x : Position ∂volume, x ∈ Ω) (N : ℕ) :
    ∀ᵐ X : Configuration N ∂volume, X ∈ configurationDomain Ω N :=
  (ConfigurationGeometry.regular_ae N).and (particleDomain_ae hfull N)

private def assemble {N : ℕ} (x : Fin N → Position) : Configuration N :=
  WithLp.toLp 2 (fun i => x i.1 i.2)

private theorem assemble_continuous (N : ℕ) : Continuous (assemble (N := N)) := by
  exact (PiLp.continuous_toLp _ _).comp
    (continuous_pi fun i => (PiLp.continuous_apply _ _ i.2).comp (continuous_apply i.1))

theorem particleDomain_isPreconnected {Ω : Set Position} (hΩ : IsPreconnected Ω) (N : ℕ) :
    IsPreconnected (particleDomain Ω N) := by
  have himage : assemble '' (Set.pi Set.univ (fun _ : Fin N => Ω)) = particleDomain Ω N := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩ n
      exact hx n (Set.mem_univ n)
    · intro hX
      refine ⟨fun n => (split n X).1, fun n _ => hX n, ?_⟩
      rfl
  rw [← himage]
  exact (isPreconnected_univ_pi (fun _ : Fin N => hΩ)).image assemble
    (assemble_continuous N).continuousOn

/-- A ball remains path connected after removing the collision diagonals. -/
theorem ball_regular_isPathConnected {N : ℕ} (x : Configuration N) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r ∩ distinctConfigurations N) := by
  have hdense : Dense (distinctConfigurations N) :=
    (volume : Measure (Configuration N)).dense_of_ae (ConfigurationGeometry.regular_ae N)
  obtain ⟨a, haB, haR⟩ := hdense.inter_open_nonempty (Metric.ball x r)
    Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩
  refine ⟨a, ⟨haB, haR⟩, ?_⟩
  intro b hb
  have hg := (ConfigurationGeometry.ae_segment_regular haR).and
    (ConfigurationGeometry.ae_segment_regular hb.2)
  have hgdense : Dense {z | segment ℝ a z ⊆ distinctConfigurations N ∧
      segment ℝ b z ⊆ distinctConfigurations N} := (volume : Measure (Configuration N)).dense_of_ae hg
  obtain ⟨z, hzB, hzA, hzB'⟩ := hgdense.inter_open_nonempty (Metric.ball x r)
    Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩
  have haz : JoinedIn (Metric.ball x r ∩ distinctConfigurations N) a z := by
    apply JoinedIn.of_segment_subset
    exact fun y hy => ⟨(convex_ball x r).segment_subset haB hzB hy, hzA hy⟩
  have hbz : JoinedIn (Metric.ball x r ∩ distinctConfigurations N) b z := by
    apply JoinedIn.of_segment_subset
    exact fun y hy => ⟨(convex_ball x r).segment_subset hb.1 hzB hy, hzB' hy⟩
  exact haz.trans hbz.symm

/-- Removing a dense set's complement preserves connectedness on an
open domain when every ball intersects that set in a preconnected set. -/
private theorem preconnected_inter_of_local_removal {E : Type*} [MetricSpace E]
    {U R : Set E} (hU : IsOpen U) (hcU : IsPreconnected U)
    (hdR : Dense R)
    (hball : ∀ x : E, ∀ r : ℝ, 0 < r → IsPreconnected (Metric.ball x r ∩ R)) :
    IsPreconnected (U ∩ R) := by
  rcases (U ∩ R).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · rw [h]
    exact isPreconnected_empty
  let C := connectedComponentIn (U ∩ R) a
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hCsub : C ⊆ U ∩ R := connectedComponentIn_subset _ _
  have hlocal : ∀ x ∈ closure C ∩ U, ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ R ⊆ C ∧ Metric.ball x r ⊆ closure C := by
    intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx.2
    obtain ⟨y, hyB, hyC⟩ := mem_closure_iff.mp hx.1 (Metric.ball x r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hBR : Metric.ball x r ∩ R ⊆ C := by
      have hyBR : y ∈ Metric.ball x r ∩ R := ⟨hyB, (hCsub hyC).2⟩
      have hsub : Metric.ball x r ∩ R ⊆ U ∩ R :=
        fun z hz => ⟨hrU hz.1, hz.2⟩
      have h := (hball x r hr).subset_connectedComponentIn hyBR hsub
      have heq : connectedComponentIn (U ∩ R) y = C :=
        (connectedComponentIn_eq hyC).symm
      exact heq ▸ h
    exact ⟨r, hr, hBR, (hdR.open_subset_closure_inter Metric.isOpen_ball).trans
      (closure_mono hBR)⟩
  have hint : closure C ∩ U ⊆ interior (closure C) := by
    intro x hx
    obtain ⟨r, hr, _, hsub⟩ := hlocal x hx
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hsub)
  have hUclosure : U ⊆ closure C := by
    have haint : a ∈ interior (closure C) :=
      hint ⟨subset_closure haC, ha.1⟩
    have h := hcU.subset_of_closure_inter_subset isOpen_interior ⟨a, ha.1, haint⟩
      (fun x hx => hint ⟨by
        simpa only [closure_closure] using
          (closure_mono (interior_subset (s := closure C))) hx.1, hx.2⟩)
    exact h.trans interior_subset
  have hUC : U ∩ R ⊆ C := by
    intro x hx
    obtain ⟨r, hr, hsub, _⟩ := hlocal x ⟨hUclosure hx.1, hx.1⟩
    exact hsub ⟨Metric.mem_ball_self hr, hx.2⟩
  have heq : U ∩ R = C := Set.Subset.antisymm hUC hCsub
  rw [heq]
  exact isPreconnected_connectedComponentIn

theorem configurationDomain_isPreconnected {Ω : Set Position} (hΩ : IsOpen Ω)
    (hcΩ : IsPreconnected Ω) (N : ℕ) : IsPreconnected (configurationDomain Ω N) := by
  rw [configurationDomain, Set.inter_comm]
  exact preconnected_inter_of_local_removal (particleDomain_isOpen hΩ N)
    (particleDomain_isPreconnected hcΩ N)
    ((volume : Measure (Configuration N)).dense_of_ae (ConfigurationGeometry.regular_ae N))
    (fun x r hr => (ball_regular_isPathConnected x hr).isConnected.isPreconnected)

theorem configurationDomain_isConnected (N : ℕ) {Ω : Set Position} (hΩ : IsOpen Ω)
    (hcΩ : IsConnected Ω) (hfull : ∀ᵐ x : Position ∂volume, x ∈ Ω) :
    IsConnected (configurationDomain Ω N) :=
  ⟨(configurationDomain_ae hfull N).exists, configurationDomain_isPreconnected hΩ hcΩ.isPreconnected N⟩

end PfHk.ExceptionalConfigurationGeometry
