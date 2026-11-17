import PfHk.PauliCarlemanAbsorption

/-! Finite coupled source integrals. Integrability of the full source and
the quarter-source smallness condition are conclusions of the two
magnetic estimates. -/

noncomputable section
namespace PfHk.PauliCarlemanSource

open MeasureTheory

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 30000

variable {S X H : Type*} [Fintype S] [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X}

def density (w : X → ℝ) (f : S → X → H) (x : X) : ℝ :=
  ∑ s, w x * ‖f s x‖ ^ 2

theorem density_nonneg (w : X → ℝ) (f : S → X → H)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) : ∀ᵐ x ∂μ, 0 ≤ density w f x :=
  hw.mono fun _ hx => Finset.sum_nonneg fun _ _ => mul_nonneg hx (sq_nonneg _)

omit [MeasurableSpace X] in
theorem density_eq (w : X → ℝ) (f : S → X → H) (x : X) :
    density w f x = w x * ∑ s, ‖f s x‖ ^ 2 := (Finset.mul_sum ..).symm

theorem component_integrable {w : X → ℝ} {f : S → X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hm : ∀ s, AEStronglyMeasurable (fun x => w x * ‖f s x‖ ^ 2) μ)
    (hi : Integrable (density w f) μ) (s : S) :
    Integrable (fun x => w x * ‖f s x‖ ^ 2) μ := by
  apply hi.mono' (hm s)
  filter_upwards [hw] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg hx (sq_nonneg _))]
  exact Finset.single_le_sum (fun t _ => mul_nonneg hx (sq_nonneg (‖f t x‖)))
    (Finset.mem_univ s)

theorem integral_eq_source {w : X → ℝ} {f : S → X → H}
    (hi : ∀ s, Integrable (fun x => w x * ‖f s x‖ ^ 2) μ) :
    (∫ x, density w f x ∂μ) = PauliCarlemanAbsorption.source (μ := μ) w f :=
  integral_finsetSum _ (fun s _ => hi s)

theorem add_bound {w : X → ℝ} {f g h : S → X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hm : ∀ s, AEStronglyMeasurable (fun x => w x * ‖h s x‖ ^ 2) μ)
    (hf : ∀ s, Integrable (fun x => w x * ‖f s x‖ ^ 2) μ)
    (hg : ∀ s, Integrable (fun x => w x * ‖g s x‖ ^ 2) μ)
    (heq : ∀ s, h s =ᵐ[μ] fun x => f s x + g s x) :
    (∀ s, Integrable (fun x => w x * ‖h s x‖ ^ 2) μ) ∧
      (∫ x, density w h x ∂μ) ≤
        2 * (∫ x, density w f x ∂μ) + 2 * ∫ x, density w g x ∂μ := by
  have hparts (s : S) := WeightedNorm.sub_integrable_bound hw (hm s) (hf s)
    (show Integrable (fun x => w x * ‖-g s x‖ ^ 2) μ by simpa only [norm_neg] using hg s)
    (show h s =ᵐ[μ] fun x => f s x - -g s x by simpa only [sub_neg_eq_add] using heq s)
  have hi (s : S) : Integrable (fun x => w x * ‖h s x‖ ^ 2) μ := (hparts s).1
  refine ⟨hi, ?_⟩
  rw [integral_eq_source hi, integral_eq_source hf, integral_eq_source hg]
  have hb := Finset.sum_le_sum (s := Finset.univ) fun s _ => (hparts s).2
  simpa only [PauliCarlemanAbsorption.source, norm_neg, Finset.sum_add_distrib,
    Finset.mul_sum] using hb

private theorem quarter_bound {F C Q Z a b : ℝ}
    (hc : C ≤ a * F) (hq : Q ≤ b * F) (hz : Z ≤ 2 * C + 2 * Q)
    (hsmall : a + b ≤ 1 / 8) (hF : 0 ≤ F) : Z ≤ F / 4 := by
  have hm := mul_le_mul_of_nonneg_right hsmall hF
  nlinarith only [hc, hq, hz, hm]

/-- Both perturbations are controlled in aggregate over the coupled
components. Full-source integrability and actual smallness are derived. -/
theorem absorb_two {w : X → ℝ} {free full classical quantum : S → X → H}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hwm : AEStronglyMeasurable w μ)
    (hmfree : ∀ s, AEStronglyMeasurable (free s) μ)
    (hmfull : ∀ s, AEStronglyMeasurable (full s) μ)
    (hmcl : ∀ s, AEStronglyMeasurable (classical s) μ)
    (hmq : ∀ s, AEStronglyMeasurable (quantum s) μ)
    (hfree : Integrable (density w free) μ)
    (hcl : Integrable (density w classical) μ)
    (hq : Integrable (density w quantum) μ)
    (hop : ∀ s, free s =ᵐ[μ] fun x => full s x - (classical s x + quantum s x))
    {a b : ℝ}
    (hclbound : (∫ x, density w classical x ∂μ) ≤ a * ∫ x, density w free x ∂μ)
    (hqbound : (∫ x, density w quantum x ∂μ) ≤ b * ∫ x, density w free x ∂μ)
    (hsmall : a + b ≤ 1 / 8) :
    Integrable (density w full) μ ∧
      (∫ x, density w (fun s x => classical s x + quantum s x) x ∂μ) ≤
        (∫ x, density w free x ∂μ) / 4 ∧
      (∫ x, density w free x ∂μ) ≤ 4 * ∫ x, density w full x ∂μ := by
  have hfi := component_integrable hw (fun s => hwm.mul ((hmfree s).norm.pow 2)) hfree
  have hci := component_integrable hw (fun s => hwm.mul ((hmcl s).norm.pow 2)) hcl
  have hqi := component_integrable hw (fun s => hwm.mul ((hmq s).norm.pow 2)) hq
  let error : S → X → H := fun s x => classical s x + quantum s x
  have herr := add_bound hw
    (fun s => hwm.mul (((hmcl s).add (hmq s)).norm.pow 2)) hci hqi
    (fun _ => Filter.EventuallyEq.rfl)
  have hfullEq (s : S) : full s =ᵐ[μ] fun x => free s x + error s x :=
    (hop s).mono fun _ hx => (eq_sub_iff_add_eq.mp hx).symm
  have hp := add_bound hw (fun s => hwm.mul ((hmfull s).norm.pow 2)) hfi herr.1 hfullEq
  have hF : 0 ≤ ∫ x, density w free x ∂μ := integral_nonneg_of_ae (density_nonneg w free hw)
  have he : (∫ x, density w error x ∂μ) ≤ (∫ x, density w free x ∂μ) / 4 :=
    quarter_bound hclbound hqbound herr.2 hsmall hF
  have he' : PauliCarlemanAbsorption.source (μ := μ) w error ≤
      PauliCarlemanAbsorption.source (μ := μ) w free / 4 := by
    exact (congrArg₂ (fun x y : ℝ => x ≤ y / 4)
      (integral_eq_source (f := error) herr.1) (integral_eq_source hfi)).mp he
  have habs := PauliCarlemanAbsorption.absorb (free := free) (full := full) (error := error)
    hw hfi hp.1 herr.1 hop he'
  refine ⟨integrable_finsetSum _ (fun s _ => hp.1 s), he, ?_⟩
  exact (congrArg₂ (fun x y : ℝ => x ≤ 4 * y)
    (integral_eq_source hfi) (integral_eq_source hp.1)).mpr habs

end PfHk.PauliCarlemanSource
