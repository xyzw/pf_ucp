import GptLean.ElectronicH1Symmetry
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Symmetry of mixed weak derivative pairings on the actual electronic
H1 graph. Smooth integration by parts and Schwarz symmetry extend by the
already established density of the compact smooth core. -/

noncomputable section
namespace PfHk.ElectronicH1MixedPairing

open MeasureTheory GptLean.ElectronicH1Space GptLean.ElectronicH1Reindex
  GptLean.ElectronicH1Symmetry
open scoped ENNReal ContDiff InnerProductSpace

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 200000

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I] [DecidableEq I]

omit [CompleteSpace H] in
private theorem smooth_mixed
    (f g : EuclideanSpace ℝ I → H) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) (i j : I) :
    (∫ x, ⟪fderiv ℝ f x (EuclideanSpace.single i 1),
      fderiv ℝ g x (EuclideanSpace.single j 1)⟫_ℂ) =
    ∫ x, ⟪fderiv ℝ f x (EuclideanSpace.single j 1),
      fderiv ℝ g x (EuclideanSpace.single i 1)⟫_ℂ := by
  let D (k : I) (x : EuclideanSpace ℝ I) := fderiv ℝ g x (EuclideanSpace.single k 1)
  have hg' : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hd (k : I) : ContDiff ℝ ∞ (D k) := hg'.clm_apply contDiff_const
  have hs (k : I) : HasCompactSupport (D k) := hsg.fderiv_apply ℝ _
  have hij (x : EuclideanSpace ℝ I) :
      fderiv ℝ (D j) x (EuclideanSpace.single i 1) =
      fderiv ℝ (D i) x (EuclideanSpace.single j 1) := by
    dsimp [D]
    rw [fderiv_clm_apply (hg'.differentiable (by simp) x) (differentiableAt_const _),
      fderiv_clm_apply (hg'.differentiable (by simp) x) (differentiableAt_const _)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      ((hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hi := smooth_integration_by_parts f (D j) hf (hd j) hsf (hs j) i
  have hj := smooth_integration_by_parts f (D i) hf (hd i) hsf (hs i) j
  have heq : (∫ x, ⟪f x, fderiv ℝ (D j) x (EuclideanSpace.single i 1)⟫_ℂ) =
      ∫ x, ⟪f x, fderiv ℝ (D i) x (EuclideanSpace.single j 1)⟫_ℂ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => congrArg (inner ℂ (f x)) (hij x))
  exact neg_injective (hi.symm.trans (heq.trans hj))

theorem smoothCore_pairing (u v : H1 H I)
    (hu : u ∈ genericSmoothCore H I) (hv : v ∈ genericSmoothCore H I) (i j : I) :
    ⟪derivative i u, derivative j v⟫_ℂ = ⟪derivative j u, derivative i v⟫_ℂ := by
  obtain ⟨f, hf, hs, rfl⟩ := hu
  obtain ⟨g, hg, ht, rfl⟩ := hv
  have hfrep (k : I) := (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ (EuclideanSpace.single k 1))
      (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hgrep (k : I) := (((hg.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (ht.fderiv_apply ℝ (EuclideanSpace.single k 1))
      (p := (2 : ℝ≥0∞)) (μ := volume)).coeFn_toLp
  have hrep (a b : I) :
      ⟪derivative a (ofSmoothCompact f hf hs), derivative b (ofSmoothCompact g hg ht)⟫_ℂ =
        ∫ x, ⟪fderiv ℝ f x (EuclideanSpace.single a 1),
          fderiv ℝ g x (EuclideanSpace.single b 1)⟫_ℂ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hfrep a, hgrep b] with x hx hy
    exact congrArg₂ (inner ℂ) hx hy
  rw [hrep, hrep]
  exact smooth_mixed f g hf hg hs ht i j

theorem pairing (u v : H1 H I) (i j : I) :
    ⟪derivative i u, derivative j v⟫_ℂ = ⟪derivative j u, derivative i v⟫_ℂ := by
  have hc : IsClosed {p : H1 H I × H1 H I |
      ⟪derivative i p.1, derivative j p.2⟫_ℂ =
        ⟪derivative j p.1, derivative i p.2⟫_ℂ} :=
    isClosed_eq (((derivative i).continuous.comp continuous_fst).inner
      ((derivative j).continuous.comp continuous_snd))
      (((derivative j).continuous.comp continuous_fst).inner
        ((derivative i).continuous.comp continuous_snd))
  exact (closure_minimal
    (fun p hp => smoothCore_pairing p.1 p.2 hp.1 hp.2 i j) hc)
    ((dense_genericSmoothCore.prod dense_genericSmoothCore) (u, v))

theorem complex_pairing
    (u v : GptLean.ElectronicH1Complex.ComplexH1 H I) (i j : I) :
    ⟪GptLean.ElectronicH1Complex.derivative i u,
      GptLean.ElectronicH1Complex.derivative j v⟫_ℂ =
    ⟪GptLean.ElectronicH1Complex.derivative j u,
      GptLean.ElectronicH1Complex.derivative i v⟫_ℂ :=
  pairing (GptLean.ElectronicH1Complex.realEquiv u)
    (GptLean.ElectronicH1Complex.realEquiv v) i j

end PfHk.ElectronicH1MixedPairing
