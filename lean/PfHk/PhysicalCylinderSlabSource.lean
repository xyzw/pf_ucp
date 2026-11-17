import PfHk.PhysicalCylinderSource
import PfHk.CarlemanSourcePair
import PfHk.CompactSlabOperators

/-! The physical transformed source as an actual L2 vector on every
compact logarithmic slab, together with its exact real source pairing. -/

noncomputable section
namespace PfHk.PhysicalCylinderSource

open MeasureTheory GptLean GptLean.PhysicalFock GptLean.PhysicalPolarization
  GptLean.SymmetricLift GptLean.Representability PfHk.PhysicalOperatorDomain
  PfHk.PolarCalculus PfHk.CenteredRadialGauge PfHk.OrdinaryPolarSobolevChart
open PfHk.SphereAngularField (Sphere)
open scoped ENNReal InnerProductSpace
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 20000
local instance sourceSlabRealInner : InnerProductSpace ℝ PhotonFock :=
  InnerProductSpace.rclikeToReal ℂ _

theorem continuous_slab_memLp {N : ℕ} {H : Type*} [NormedAddCommGroup H]
    (h : Slab N → H) (hh : Continuous h) (a b : ℝ) :
    MemLp h 2 (slabMeasure N a b) := by
  letI : IsFiniteMeasure (slabMeasure N a b) := by
    unfold slabMeasure
    infer_instance
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_univ : IsCompact (Set.univ : Set (Sphere N)))).exists_bound_of_continuousOn hh.continuousOn
  apply MemLp.of_bound hh.aestronglyMeasurable M
  have ht : ∀ᵐ p ∂slabMeasure N a b, p.1 ∈ Set.Icc a b :=
    (Measure.quasiMeasurePreserving_fst (ν := sphereMeasure (Fin N × Fin 3))).ae
      (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with p hp
  exact hM p ⟨hp, Set.mem_univ p.2⟩

variable {N : ℕ} (F : Frame) (χ : ArticleCutoff) (e : ℝ)
  (O : Configuration N) (W : ConcreteWeylLaw photonMeasure)
  {s : Set (Configuration N)}
  {f : PhysicalPFReference.WaveSpace (Fin N × Fin 3)} (g : CompactSource s f)

def slabSource (c a b : ℝ) : PhotonSlab N a b :=
  (continuous_slab_memLp (value F χ e O W g c) (value_continuous F χ e O W g c) a b).toLp
    (value F χ e O W g c)

theorem slabSource_ae (c a b : ℝ) : slabSource F χ e O W g c a b =ᵐ[slabMeasure N a b]
    value F χ e O W g c :=
  (continuous_slab_memLp (value F χ e O W g c) (value_continuous F χ e O W g c) a b).coeFn_toLp

theorem source_pair (p : Slab N) (v : PhotonFock) :
    inner ℝ (Real.exp (-conformalExponent (Fin N × Fin 3)*p.1) •
      unitary F χ e O W (logarithmicPoint p) v)
      (value F χ e O W g (conformalExponent (Fin N × Fin 3)) p) =
      2*logarithmicJacobian (Fin N × Fin 3) p.1*
        inner ℝ v (g.representative (logarithmicPoint p)) :=
  conformal_source_pair (Fin N × Fin 3) (unitary F χ e O W (logarithmicPoint p)) p.1 v
    (g.representative (logarithmicPoint p))

end PfHk.PhysicalCylinderSource
