import GptLean.PhysicalFockTensorAnnihilation

/-!
The full annihilation form pulls back along the actual Fock split.

The proof uses the tensor pair-sector expansion, the bounded sector
intertwining identity and nonnegative Tonelli sums. It applies to every
Fock vector, including vectors of infinite annihilation form.
-/

noncomputable section
namespace GptLean.PhysicalFock

open MeasureTheory
open scoped ENNReal InnerProductSpace
open TensorCoordinates TensorSectors PhotonLocalizationFockChannel

set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
  (C : CanonicalSectorCCR μ) (B : ConcreteExponentialLaw μ)

theorem annihilationBlock_norm (n : ℕ) (f : Lp ℂ 2 μ) (u : Fock μ) :
    ‖annihilationBlock μ n f u‖ = ‖annihilationSector μ n f (u (n + 1))‖ :=
  lp.norm_single (E := Sector μ) (p := 2) (by norm_num) n _

theorem annihilationForm_eq_blocks (f : Lp ℂ 2 μ) (u : Fock μ) :
    annihilationForm μ f u = ∑' n, ENNReal.ofReal (‖annihilationBlock μ n f u‖ ^ 2) := by
  apply tsum_congr
  intro n
  exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ 2)) (annihilationBlock_norm μ n f u).symm

include C B in
/-- The pair coordinate of retained annihilation comes from its matching source block. -/
theorem split_pair_annihilation
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (f : Lp ℂ 2 μ) (u : Fock μ) (r s : ℕ) :
    firstTensorMap (annihilationSector μ r f)
        (pairCoefficients (Sector μ) (B.split μ j u) (r + 1, s)) =
      pairCoefficients (Sector μ)
        (B.split μ j (annihilationBlock μ (r + s) ((retainedMap j).adjoint f) u)) (r, s) := by
  let v := photonSector μ (r + s + 1) u
  have hred : pairCoefficients (Sector μ) (B.split μ j u) (r + 1, s) =
      pairCoefficients (Sector μ) (B.split μ j v) (r + 1, s) := by
    simpa only [Nat.add_right_comm r 1 s] using
      split_pair_eq_sector μ B j u (r + 1, s)
  have hblock : annihilationFinite μ (r + s + 1) ((retainedMap j).adjoint f) v =
      annihilationBlock μ (r + s) ((retainedMap j).adjoint f) u :=
    annihilationFinite_single μ (r + s + 1) (r + s) (by omega)
      ((retainedMap j).adjoint f) (u (r + s + 1))
  calc
    _ = firstTensorMap (annihilationSector μ r f)
        (pairCoefficients (Sector μ) (B.split μ j v) (r + 1, s)) :=
      congrArg (firstTensorMap (annihilationSector μ r f)) hred
    _ = pairCoefficients (Sector μ)
        (retainedOperator (annihilationFinite μ (r + s + 1) f) (B.split μ j v)) (r, s) :=
      (pair_retained_annihilationFinite μ (r + s + 1) r s (by omega) f (B.split μ j v)).symm
    _ = pairCoefficients (Sector μ) (B.split μ j
        (annihilationFinite μ (r + s + 1) ((retainedMap j).adjoint f) v)) (r, s) :=
      congrArg (pairCoordinate (Sector μ) (r, s))
        (retained_annihilation_split_sector μ C B j (r + s + 1) (r + s + 1)
          le_rfl f u)
    _ = _ := congrArg (fun w : Fock μ => pairCoordinate (Sector μ) (r, s) (B.split μ j w)) hblock

include B in
theorem split_annihilationBlock_pair_zero
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (n r s : ℕ) (hn : r + s ≠ n) (f : Lp ℂ 2 μ) (u : Fock μ) :
    pairCoefficients (Sector μ) (B.split μ j (annihilationBlock μ n f u)) (r, s) = 0 := by
  have hself : photonSector μ n (annihilationBlock μ n f u) = annihilationBlock μ n f u := by
    change lp.single 2 n ((lp.single 2 n (annihilationSector μ n f (u (n + 1)))) n) = _
    rw [lp.single_apply_self]
    rfl
  exact (congrArg (fun w : Fock μ => pairCoordinate (Sector μ) (r, s) (B.split μ j w)) hself).symm.trans
    (split_sector_pair_zero μ B j n (annihilationBlock μ n f u) (r, s) hn)

include C B in
/-- Exact full tensor form pullback, with no finite-form or graph-domain premise. -/
theorem tensorAnnihilationForm_split
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (f : Lp ℂ 2 μ) (u : Fock μ) :
    tensorAnnihilationForm μ f (B.split μ j u) =
      annihilationForm μ ((retainedMap j).adjoint f) u := by
  let w : ℕ → Fock μ := fun n => annihilationBlock μ n ((retainedMap j).adjoint f) u
  let t : ℕ → ℕ → ℕ → ℝ≥0∞ := fun n r s =>
    ENNReal.ofReal (‖pairCoefficients (Sector μ) (B.split μ j (w n)) (r, s)‖ ^ 2)
  have hp (r s : ℕ) : ENNReal.ofReal (‖firstTensorMap (annihilationSector μ r f)
      (pairCoefficients (Sector μ) (B.split μ j u) (r + 1, s))‖ ^ 2) = ∑' n, t n r s := by
    have he := congrArg (fun z : TensorSpace (Sector μ r) (Sector μ s) =>
      ENNReal.ofReal (‖z‖ ^ 2)) (split_pair_annihilation μ C B j f u r s)
    apply he.trans
    symm
    apply tsum_eq_single (r + s)
    intro n hn
    have hz := congrArg (fun z : TensorSpace (Sector μ r) (Sector μ s) =>
      ENNReal.ofReal (‖z‖ ^ 2))
      (split_annihilationBlock_pair_zero μ B j n r s (Ne.symm hn) ((retainedMap j).adjoint f) u)
    exact hz.trans (by simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero])
  calc
    _ = ∑' r, ∑' s, ∑' n, t n r s :=
      (tensorAnnihilationForm_eq_pairs μ f (B.split μ j u)).trans
        (tsum_congr (fun r => tsum_congr (hp r)))
    _ = ∑' r, ∑' n, ∑' s, t n r s := tsum_congr (fun _ => ENNReal.tsum_comm)
    _ = ∑' n, ∑' r, ∑' s, t n r s := ENNReal.tsum_comm
    _ = ∑' n, ENNReal.ofReal (‖w n‖ ^ 2) := by
      apply tsum_congr
      intro n
      exact (pair_norm_sum μ (B.split μ j (w n))).symm.trans
        (congrArg (fun q : ℝ => ENNReal.ofReal (q ^ 2)) ((B.split μ j).norm_map (w n)))
    _ = _ := (annihilationForm_eq_blocks μ ((retainedMap j).adjoint f) u).symm

/-- Environmental coordinates of the actual tensor annihilation form. -/
theorem tensorAnnihilationForm_coordinates
    (W : TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ] lp (fun _ : ℕ => Fock μ) 2)
    (hW : ∀ (A : Fock μ →L[ℂ] Fock μ) (z : TensorSpace (Fock μ) (Fock μ))
      (a : ℕ), W (retainedOperator A z) a = A (W z a))
    (f : Lp ℂ 2 μ) (z : TensorSpace (Fock μ) (Fock μ)) :
    ∑' a, annihilationForm μ f (W z a) = tensorAnnihilationForm μ f z := by
  have hn (n : ℕ) : (∑' a, ENNReal.ofReal (‖annihilationBlock μ n f (W z a)‖ ^ 2)) =
      ENNReal.ofReal (‖retainedOperator (annihilationBlock μ n f) z‖ ^ 2) := by
    have hs := coordinate_mass_hasSum (fun _ : ℕ => Fock μ)
      (W (retainedOperator (annihilationBlock μ n f) z))
    have he := ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg
      (‖W (retainedOperator (annihilationBlock μ n f) z) a‖)) hs.summable
    calc
      _ = ∑' a, ENNReal.ofReal (‖W (retainedOperator (annihilationBlock μ n f) z) a‖ ^ 2) :=
        tsum_congr (fun a => congrArg (fun v : Fock μ => ENNReal.ofReal (‖v‖ ^ 2))
          (hW (annihilationBlock μ n f) z a).symm)
      _ = _ := he.symm.trans (congrArg ENNReal.ofReal
        (hs.tsum_eq.trans (congrArg (fun q : ℝ => q ^ 2) (W.norm_map _))))
  calc
    _ = ∑' a, ∑' n, ENNReal.ofReal (‖annihilationBlock μ n f (W z a)‖ ^ 2) :=
      tsum_congr (fun a => annihilationForm_eq_blocks μ f (W z a))
    _ = ∑' n, ∑' a, ENNReal.ofReal (‖annihilationBlock μ n f (W z a)‖ ^ 2) := ENNReal.tsum_comm
    _ = _ := tsum_congr hn

include C B in
theorem factorization_annihilationForm
    (W : TensorSpace (Fock μ) (Fock μ) →ₗᵢ[ℂ] lp (fun _ : ℕ => Fock μ) 2)
    (hW : ∀ (A : Fock μ →L[ℂ] Fock μ) (z : TensorSpace (Fock μ) (Fock μ))
      (a : ℕ), W (retainedOperator A z) a = A (W z a))
    (j : Lp ℂ 2 μ →ₗᵢ[ℂ] WithLp 2 (Lp ℂ 2 μ × Lp ℂ 2 μ))
    (f : Lp ℂ 2 μ) (u : Fock μ) :
    ∑' a, annihilationForm μ f ((B.factorization μ W).factor j u a) =
      annihilationForm μ ((retainedMap j).adjoint f) u :=
  (tensorAnnihilationForm_coordinates μ W hW f (B.split μ j u)).trans
    (tensorAnnihilationForm_split μ C B j f u)

/-- Full rank-one form pullback on the concrete physical photon channel. -/
theorem photonFactorization_annihilationForm
    (BF : StandardSymmetricFockExponential) (CCR : CanonicalSectorCCR photonMeasure)
    (j : Lp ℂ 2 photonMeasure →ₗᵢ[ℂ]
      WithLp 2 (Lp ℂ 2 photonMeasure × Lp ℂ 2 photonMeasure))
    (f : Lp ℂ 2 photonMeasure) (u : PhotonFock) :
    ∑' a, annihilationForm photonMeasure f ((photonFactorization BF).factor j u a) =
      annihilationForm photonMeasure ((retainedMap j).adjoint f) u :=
  factorization_annihilationForm photonMeasure CCR (photonExponential BF)
    (environmentalCoordinates PhotonFock) environmentalCoordinates_retainedOperator j f u

end GptLean.PhysicalFock
