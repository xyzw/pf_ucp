import GptLean.PhysicalGroundStateReversal
import GptLean.PhysicalMeanFieldsGauge

/-!
The mean photon amplitude of a ground state (`prop-ground-state-fields`
(ii) and (iii)).

For `f ∈ D(ω)` with weighted kernel `K = (ω f, √ω f)`, the displaced vector
`W(t f) Ψ` is a pure state with the same density. Its combined current is
`j - e t ρ c_f`, with the classical field `c_f^a(y) = 2 Re ⟨G^a_y, f⟩`. In the
shifted energy the external vector potential therefore contributes
`-e t ∫ ρ A · c_f`, and the internal energy contributes `2 t Re ⟨a(ω f) Ψ, Ψ⟩`
and `-e t ∫ c_f · j_c` at first order. Minimality of the ground state makes
the linear coefficient vanish. With `f` and `i f` this gives the article's
identity `⟨Ψ, a(ω f) Ψ⟩ = e ∑_a ∫ ⟨f, G^a_y⟩ j^a(y) dy` for the physical
current `j = j_c + ρ A`. If `⟨G^a_y, g⟩` is real, the mean transverse electric
field `-2 Im ⟨Ψ, a(ω g) Ψ⟩` along `g` vanishes.
-/

noncomputable section

namespace GptLean.PhysicalGroundState

open MeasureTheory Filter PhysicalPairSpace PhysicalPairDuality PhysicalFock PhysicalPFReference
  PhysicalWeyl Representability
open scoped ENNReal InnerProductSpace

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

section Algebra

/-- The first variation along displacements, in abstract form. -/
theorem weyl_linear {E₀ P₀ R J Λ Q k n e : ℝ} (hn : n = 1)
    (h : ∀ t : ℝ, E₀ + P₀ ≤ (E₀ + 2 * (t * R) + t ^ 2 * k * n +
      (-(e * t) * J + (e ^ 2 * t ^ 2 / 2) * Q)) + (P₀ - e * t * Λ)) :
    2 * R = e * (J + Λ) := by
  have h0 := linear_zero (X := 2 * R - e * (J + Λ)) (Y := k + e ^ 2 / 2 * Q) (fun t => by
    have ht := h t
    subst hn
    ring_nf at ht ⊢
    linarith)
  linarith

theorem amplitude_from_twice {A S : ℝ} {e : ℝ} (h : 2 * A = e * (2 * S)) : A = e * S := by
  linarith

end Algebra

variable {N : ℕ} (i : Fin N) (F : PhysicalPolarization.Frame)
  (χ : PhysicalPolarization.ArticleCutoff) (C : CanonicalSectorCCR photonMeasure)
  (B : PhysicalNormalTrace.StandardNormalTraceBackground)
  (S : PhysicalClosedForms.StandardClosedFormBackground) (e : ℝ)
  (W : ConcreteWeylLaw photonMeasure)

set_option hygiene false in
local notation "Vp" => PhysicalRemoval.potential N 1
set_option hygiene false in
local notation "κF" => PhysicalRemovalKernels.full F χ N
set_option hygiene false in
local notation "hκF" => PhysicalRemovalKernels.full_measurable F χ N
set_option hygiene false in
local notation "MF" => PhysicalRemovalKernels.bound F χ
set_option hygiene false in
local notation "hbF" => PhysicalRemovalKernels.full_bound F χ N
set_option hygiene false in
local notation "Kf" => PhysicalProfiles.momentumKernel (PhysicalPolarization.formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hKf" => PhysicalProfiles.momentumKernel_continuous
  (PhysicalPolarization.formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "MK" => PhysicalProfiles.kernelBound (PhysicalPolarization.formFactors F χ) rfl
  (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "hMK" => PhysicalProfiles.momentumKernel_bound
  (PhysicalPolarization.formFactors F χ) rfl (LinearIsometryEquiv.refl ℝ _)
set_option hygiene false in
local notation "vpair" => PhysicalPFPairSeries.vectorPair i Vp C κF hκF MF hbF e

/-- The article kernel `G^a_y` of the field component `a` at `y`, as an `L²` photon function. -/
abbrev kernelAt (a : Fin 3) (y : PhysicalPairSpace.Position) : Lp ℂ 2 photonMeasure :=
  (fieldKernel F χ (a, y)).val.1

/-- The classical field vector `c_f(y) = (2 Re ⟨G^a_y, f⟩)_a`. -/
def classicalField3 (f : Lp ℂ 2 photonMeasure) (y : PhysicalPairSpace.Position) : Vector :=
  WithLp.toLp 2 (fun a => classicalVector F χ f a y)

theorem classicalVector_I (f : Lp ℂ 2 photonMeasure) (a : Fin 3) (y : PhysicalPairSpace.Position) :
    classicalVector F χ (Complex.I • f) a y = 2 * (⟪f, kernelAt F χ a y⟫_ℂ).im := by
  unfold classicalVector
  rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, ← inner_conj_symm f,
    Complex.conj_im]
  ring

theorem classicalVector_eq (f : Lp ℂ 2 photonMeasure) (a : Fin 3) (y : PhysicalPairSpace.Position) :
    classicalVector F χ f a y = 2 * (⟪f, kernelAt F χ a y⟫_ℂ).re := by
  unfold classicalVector
  rw [re_inner_comm]

/-- The physical current `j = j_c + ρ A` of a pair. -/
abbrev physicalCurrent (a : Potential) (d : Pair) (y : PhysicalPairSpace.Position) : Vector :=
  currentL1 d y + densityL1 d y • a.2.val y

section Generic

theorem physicalCurrent_integrable (a : Potential) (d : Pair) :
    Integrable (physicalCurrent a d) volume :=
  (L1.integrable_coeFn _).add (integrable_density_smul a d)

theorem physicalCurrent_component_integrable (a : Potential) (d : Pair) (b : Fin 3) :
    Integrable (fun y => physicalCurrent a d y b) volume :=
  (EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp (physicalCurrent_integrable a d)

theorem density_component_integrable (a : Potential) (d : Pair) (b : Fin 3) :
    Integrable (fun y => densityL1 d y * a.2.val y b) volume := by
  refine ((EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp
    (integrable_density_smul a d)).congr (ae_of_all _ fun y => ?_)
  simp

/-- The classical coupling of the current and of the vector potential combine to
the physical current. -/
theorem classical_coupling (a : Potential) (f : Lp ℂ 2 photonMeasure) (d : Pair) :
    (∑ b, ∫ y, classicalVector F χ f b y * currentL1 d y b) +
      ∫ y, densityL1 d y * inner ℝ (a.2.val y) (classicalField3 F χ f y) =
    ∑ b, ∫ y, classicalVector F χ f b y * physicalCurrent a d y b := by
  have hc (b : Fin 3) : AEStronglyMeasurable (classicalVector F χ f b) volume :=
    (classicalVector_continuous F χ f b).aestronglyMeasurable
  have hcb (b : Fin 3) : ∀ᵐ y ∂volume, ‖classicalVector F χ f b y‖ ≤
      2 * PhysicalRemovalKernels.bound F χ * ‖f‖ :=
    ae_of_all _ (classicalVector_bound F χ f b)
  have hj (b : Fin 3) : Integrable (fun y => classicalVector F χ f b y * currentL1 d y b) volume :=
    ((EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp
      (L1.integrable_coeFn (currentL1 d))).bdd_mul (hc b) (hcb b)
  have hA (b : Fin 3) : Integrable (fun y => classicalVector F χ f b y *
      (densityL1 d y * a.2.val y b)) volume :=
    (density_component_integrable a d b).bdd_mul (hc b) (hcb b)
  have hΛ : (∫ y, densityL1 d y * inner ℝ (a.2.val y) (classicalField3 F χ f y)) =
      ∑ b, ∫ y, classicalVector F χ f b y * (densityL1 d y * a.2.val y b) := by
    rw [← integral_finsetSum _ fun b _ => hA b]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [classicalField3, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hΛ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_add (hj b) (hA b)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [physicalCurrent, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The pairing of a pair whose current is shifted by `-s ρ c`. -/
theorem pairPotential_of_shift (a : Potential) (s : ℝ) (c : PhysicalPairSpace.Position → Vector)
    {P P' : Pair} (hρ : densityL1 P' = densityL1 P)
    (hj : ∀ᵐ y ∂volume, currentL1 P' y = currentL1 P y - (s * densityL1 P y) • c y) :
    pairPotential a P' =
      pairPotential a P - s * ∫ y, densityL1 P y * inner ℝ (a.2.val y) (c y) := by
  have hdiff : pairPotential a (P' - P) =
      -(s * ∫ y, densityL1 P y * inner ℝ (a.2.val y) (c y)) := by
    rw [pairPotential_eq_integral]
    have hρ0 : densityL1 (P' - P) = 0 := (map_sub _ _ _).trans (sub_eq_zero.mpr hρ)
    have hρi : (∫ x, a.1.val x * densityL1 (P' - P) x) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [Filter.EventuallyEq.of_eq (congrArg
        (fun g : Lp ℝ 1 (volume : Measure PhysicalPairSpace.Position) =>
          (g : PhysicalPairSpace.Position → ℝ)) hρ0),
        Lp.coeFn_zero ℝ 1 (volume : Measure PhysicalPairSpace.Position)] with x h₁ h₂
      rw [h₁, h₂, Pi.zero_apply, mul_zero]
    rw [hρi, zero_add, ← integral_const_mul, ← integral_neg]
    have hjd : currentL1 (P' - P) = currentL1 P' - currentL1 P := map_sub _ _ _
    apply integral_congr_ae
    filter_upwards [Filter.EventuallyEq.of_eq (congrArg
        (fun g : Lp Vector 1 (volume : Measure PhysicalPairSpace.Position) =>
          (g : PhysicalPairSpace.Position → Vector)) hjd),
      Lp.coeFn_sub (currentL1 P') (currentL1 P), hj] with y h₁ h₂ h₃
    refine (congrArg (fun v : Vector => inner ℝ (a.2.val y) v)
      (h₁.trans (h₂.trans ((congrArg (· - currentL1 P y) h₃).trans
        (sub_sub_cancel_left _ _))))).trans ?_
    rw [inner_neg_right, inner_smul_right]
    ring
  have h := (map_sub (pairPotential a) P' P).symm.trans hdiff
  linarith

end Generic

section Displacement

variable {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
  (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p)

/-- **The current of a displaced vector**, almost everywhere:
`j_{W(t f) u} = j_u - e t ρ_u c_f`. -/
theorem current_weylRef_ae (t : ℝ) (u : Reference (Fin N × Fin 3) Vp) :
    ∀ᵐ y ∂volume, currentL1 (vpair (weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)) y =
      currentL1 (vpair u) y - (e * t * densityL1 (vpair u) y) • classicalField3 F χ f y := by
  have hcomp (b : Fin 3) : (fun y =>
      currentL1 (vpair (weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)) y b) =ᵐ[volume]
      fun y => currentL1 (vpair u) y b -
        e * t * (densityL1 (vpair u) y * classicalVector F χ f b y) := by
    have hjb : Integrable (fun y => currentL1 (vpair u) y b) volume :=
      (EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp (L1.integrable_coeFn _)
    have hj'b : Integrable (fun y => currentL1
        (vpair (weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)) y b) volume :=
      (EuclideanSpace.proj b : Vector →L[ℝ] ℝ).integrable_comp (L1.integrable_coeFn _)
    have hρc : Integrable (fun y => densityL1 (vpair u) y * classicalVector F χ f b y) volume :=
      (L1.integrable_coeFn (densityL1 (vpair u))).mul_bdd
        (classicalVector_continuous F χ f b).aestronglyMeasurable
        (ae_of_all _ (classicalVector_bound F χ f b))
    apply RemovalConstraints.ae_eq_of_boundedSpatialTests hj'b
      (hjb.sub (hρc.const_mul (e * t)))
    intro w
    have hw := w.measurable
    have hwL : ∀ y, ‖w.weight y‖ ≤ 1 := w.bounded
    have h := tested_current_weylRef i Vp C κF hκF MF hbF e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) b (classicalVector F χ ((t : ℂ) • f) b)
      (classicalVector_continuous F χ _ b).aestronglyMeasurable (classicalVector_bound F χ _ b)
      (fun z => rfl) w.weight hw hwL u
    refine h.trans ?_
    have hi₁ : Integrable (fun y => w.weight y * currentL1 (vpair u) y b) volume :=
      hjb.bdd_mul hw (ae_of_all _ hwL)
    have hi₂ : Integrable (fun y => w.weight y *
        (densityL1 (vpair u) y * classicalVector F χ f b y)) volume :=
      hρc.bdd_mul hw (ae_of_all _ hwL)
    have hsplit : (∫ y, w.weight y * (currentL1 (vpair u) y b -
        e * t * (densityL1 (vpair u) y * classicalVector F χ f b y))) =
        (∫ y, w.weight y * currentL1 (vpair u) y b) -
          e * t * ∫ y, w.weight y * (densityL1 (vpair u) y * classicalVector F χ f b y) := by
      rw [← integral_const_mul, ← integral_sub hi₁ (hi₂.const_mul _)]
      exact integral_congr_ae (ae_of_all _ fun y => by ring)
    refine Eq.trans ?_ hsplit.symm
    have hc : (∫ y, (w.weight y * classicalVector F χ ((t : ℂ) • f) b y) *
        densityL1 (vpair u) y) =
        t * ∫ y, w.weight y * (densityL1 (vpair u) y * classicalVector F χ f b y) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [classicalVector_smul]
      ring
    rw [hc]
    ring
  filter_upwards [ae_all_iff.mpr hcomp] with y hy
  apply PiLp.ext
  intro b
  refine (hy b).trans ?_
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, classicalField3]
  ring

/-- **The pairing of a displaced pair**: `⟨a, p_{W(t f) u}⟩ = ⟨a, p_u⟩ - e t ∫ ρ A · c_f`. -/
theorem pairPotential_weylRef (a : Potential) (t : ℝ) (u : Reference (Fin N × Fin 3) Vp) :
    pairPotential a (vpair (weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)) =
      pairPotential a (vpair u) -
        e * t * ∫ y, densityL1 (vpair u) y * inner ℝ (a.2.val y) (classicalField3 F χ f y) :=
  pairPotential_of_shift a (e * t) (classicalField3 F χ f)
    (densityL1_vectorPair_weylRef i Vp C κF hκF MF hbF e W ((t : ℂ) • K)
      (scaled_kernel hK (t : ℂ)) u)
    (current_weylRef_ae i F χ C e W K hK t u)

end Displacement

/-- The mean photon amplitude `⟨Ψ, a(K) Ψ⟩` of a pure state of the article model. -/
def stateAmplitude (p : State F χ C B S e (N := N)) (K : WeightedPhotonKernel) : ℂ :=
  ⟪inclusion (Fin N × Fin 3) Vp (stateVector F χ C B S e p),
    annihilationRef Vp K (stateVector F χ C B S e p)⟫_ℂ

include W in
/-- **First variation along displacements.** At a ground state,
`2 Re ⟨a(ω f) Ψ, Ψ⟩ = e ∑_a ∫ c_f^a j^a` with the physical current `j = j_c + ρ A`. -/
theorem ground_real_amplitude {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p) :
    2 * (⟪annihilationRef Vp K (stateVector F χ C B S e p),
        inclusion (Fin N × Fin 3) Vp (stateVector F χ C B S e p)⟫_ℂ).re =
      e * ∑ b, ∫ y, classicalVector F χ f b y *
        physicalCurrent a ((model i F χ C B S e).density p) y b := by
  let u := stateVector F χ C B S e p
  have hu : inclusion (Fin N × Fin 3) Vp u = p.val := stateVector_spec F χ C B S e p
  have hnorm : ‖p.val‖ = 1 := p.property.1
  have hferm : inclusion (Fin N × Fin 3) Vp u ∈
      PhysicalElectronicFermions.fermionicSubspace N PhotonFock :=
    (congrArg (fun v => v ∈ PhysicalElectronicFermions.fermionicSubspace N PhotonFock) hu).mpr
      (TransformationsPureStates.pure_fermionic Vp C Kf hKf MK hMK B S e p)
  have hdp : (model i F χ C B S e).density p = vpair u :=
    TransformationsPureStates.pure_density Vp C Kf hKf MK hMK B S e i p u hu
  have hEp : (model i F χ C B S e).energy p =
      energy (Fin N × Fin 3) Vp C κF hκF MF hbF e u :=
    TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S e i p u hu
  have hlin := weyl_linear (E₀ := energy (Fin N × Fin 3) Vp C κF hκF MF hbF e u)
    (P₀ := pairPotential a (vpair u))
    (R := (⟪annihilationRef Vp K u, inclusion (Fin N × Fin 3) Vp u⟫_ℂ).re)
    (J := currentShift Vp C κF hκF MF hbF e f u)
    (Λ := ∫ y, densityL1 (vpair u) y * inner ℝ (a.2.val y) (classicalField3 F χ f y))
    (Q := densityShift Vp κF f u) (k := ‖K.val.2‖ ^ 2)
    (n := ‖inclusion (Fin N × Fin 3) Vp u‖ ^ 2) (e := e)
    (by rw [hu, hnorm, one_pow]) (fun t => by
      let w := weylRef Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u
      have hwn : ‖inclusion (Fin N × Fin 3) Vp w‖ = 1 :=
        (congrArg norm (weylWave_inclusion Vp W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u)).symm.trans
          (((weylWave W ((t : ℂ) • f)).norm_map _).trans ((congrArg norm hu).trans hnorm))
      have hwf := inclusion_weylRef_fermionic W ((t : ℂ) • K) (scaled_kernel hK (t : ℂ)) u hferm
      let q : State F χ C B S e (N := N) :=
        TransformationsPureStates.ofVector Vp C Kf hKf MK hMK B S e
          (inclusion (Fin N × Fin 3) Vp w) hwn hwf ⟨w, rfl⟩
      have hEq : (model i F χ C B S e).energy q = energy (Fin N × Fin 3) Vp C κF hκF MF hbF e w :=
        TransformationsPureStates.pure_energy Vp C Kf hKf MK hMK B S e i q w rfl
      have hdq : (model i F χ C B S e).density q = vpair w :=
        TransformationsPureStates.pure_density Vp C Kf hKf MK hMK B S e i q w rfl
      have hle := h q
      have hsp : shiftedEnergy i F χ C B S e a p =
          energy (Fin N × Fin 3) Vp C κF hκF MF hbF e u + pairPotential a (vpair u) :=
        congrArg₂ (· + ·) hEp (congrArg (pairPotential a) hdp)
      have hsq : shiftedEnergy i F χ C B S e a q =
          energy (Fin N × Fin 3) Vp C κF hκF MF hbF e w + pairPotential a (vpair w) :=
        congrArg₂ (· + ·) hEq (congrArg (pairPotential a) hdq)
      have hE := energy_scaled Vp C κF hκF MF hbF e W t K hK u
      have hP := pairPotential_weylRef i F χ C e W K hK a t u
      calc
        _ = shiftedEnergy i F χ C B S e a p := hsp.symm
        _ ≤ shiftedEnergy i F χ C B S e a q := hle
        _ = _ := hsq.trans (congrArg₂ (· + ·) hE hP))
  have hJ := currentShift_eq i F χ C e f u hferm
  have hcoup := classical_coupling F χ a f (vpair u)
  exact hlin.trans ((congrArg (fun r : ℝ => e * (r +
      ∫ y, densityL1 (vpair u) y * inner ℝ (a.2.val y) (classicalField3 F χ f y))) hJ).trans
    ((congrArg (e * ·) hcoup).trans (congrArg (fun d : Pair => e * ∑ b, ∫ y,
      classicalVector F χ f b y * physicalCurrent a d y b) hdp.symm)))

include W in
/-- **The mean photon amplitude of a ground state, `prop-ground-state-fields`.**
For `f ∈ D(ω)` with weighted kernel `K = (ω f, √ω f)`,
`⟨Ψ, a(ω f) Ψ⟩ = e ∑_a ∫ ⟨f, G^a_y⟩ j^a(y) dy`, with `j = j_c + ρ A`, stated by
real and imaginary parts. -/
theorem ground_amplitude {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) {f : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * f p) :
    (stateAmplitude F χ C B S e p K).re =
        e * ∑ b, ∫ y, (⟪f, kernelAt F χ b y⟫_ℂ).re *
          physicalCurrent a ((model i F χ C B S e).density p) y b ∧
      (stateAmplitude F χ C B S e p K).im =
        e * ∑ b, ∫ y, (⟪f, kernelAt F χ b y⟫_ℂ).im *
          physicalCurrent a ((model i F χ C B S e).density p) y b := by
  have htwice (g : Lp ℂ 2 photonMeasure) (sel : ℂ → ℝ)
      (hsel : ∀ b y, classicalVector F χ g b y = 2 * sel (⟪f, kernelAt F χ b y⟫_ℂ)) :
      e * ∑ b, ∫ y, classicalVector F χ g b y *
          physicalCurrent a ((model i F χ C B S e).density p) y b =
        e * (2 * ∑ b, ∫ y, sel (⟪f, kernelAt F χ b y⟫_ℂ) *
          physicalCurrent a ((model i F χ C B S e).density p) y b) := by
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hsel]
    ring
  constructor
  · exact amplitude_from_twice ((congrArg (2 * ·) (re_inner_comm
      (inclusion (Fin N × Fin 3) Vp (stateVector F χ C B S e p))
      (annihilationRef Vp K (stateVector F χ C B S e p)))).trans
      ((ground_real_amplitude i F χ C B S e W h K hK).trans
        (htwice f Complex.re (fun b y => classicalVector_eq F χ f b y))))
  · exact amplitude_from_twice ((congrArg (2 * ·)
      (amplitude_I Vp K (stateVector F χ C B S e p))).trans
      ((ground_real_amplitude i F χ C B S e W h (Complex.I • K)
        (scaled_kernel hK Complex.I)).trans
        (htwice (Complex.I • f) Complex.im (fun b y => classicalVector_I F χ f b y))))

/-- The mean transverse electric field `⟨Ψ, E_⊥(g) Ψ⟩ = -2 Im ⟨Ψ, a(ω g) Ψ⟩` along `g`. -/
def stateElectric (p : State F χ C B S e (N := N)) (K : WeightedPhotonKernel) : ℝ :=
  -2 * (stateAmplitude F χ C B S e p K).im

include W in
/-- **`prop-ground-state-fields` (ii).** If `⟨G^a_y, g⟩` is real for every `a`
and almost every `y`, the mean transverse electric field of a ground state
along `g` vanishes. -/
theorem ground_electric_zero {a : Potential} {p : State F χ C B S e (N := N)}
    (h : IsGroundState i F χ C B S e a p) {g : Lp ℂ 2 photonMeasure} (K : WeightedPhotonKernel)
    (hK : ∀ᵐ p ∂photonMeasure, K.val.2 p = (Real.sqrt ‖p.1‖ : ℂ) * g p)
    (hreal : ∀ b, ∀ᵐ y ∂volume, (⟪kernelAt F χ b y, g⟫_ℂ).im = 0) :
    stateElectric F χ C B S e p K = 0 := by
  have him := (ground_amplitude i F χ C B S e W h K hK).2
  have hzero : ∑ b, ∫ y, (⟪g, kernelAt F χ b y⟫_ℂ).im *
      physicalCurrent a ((model i F χ C B S e).density p) y b = 0 := by
    refine Finset.sum_eq_zero fun b _ => (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hreal b] with y hy
    rw [← inner_conj_symm, Complex.conj_im, hy, neg_zero, zero_mul]
  unfold stateElectric
  rw [him, hzero, mul_zero, mul_zero]

end GptLean.PhysicalGroundState
