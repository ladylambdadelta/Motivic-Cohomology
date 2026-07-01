import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroAndScalarWindow.FixedLinePlemelj

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
    (a : ℝ) :
    ∀ᶠ T in atTop,
      Real.pi * T / (T - a) ≤ Real.pi + 1 := by
  have hlimit :
      Tendsto
        (fun T : ℝ => Real.pi * T / (T - a))
        atTop
        (𝓝 Real.pi) :=
    scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi a
  have hpi_lt : Real.pi < Real.pi + 1 :=
    lt_add_of_pos_right Real.pi zero_lt_one
  have heventually_lt :
      ∀ᶠ T in atTop,
        Real.pi * T / (T - a) < Real.pi + 1 :=
    Filter.eventually_of_mem
      (hlimit (Iio_mem_nhds hpi_lt))
      (fun _ hT => hT)
  exact heventually_lt.mono
    (fun _ hT => le_of_lt hT)

/-- Real exponential factor in the positive away-zero compact interval is
bounded by the endpoint exponential. -/
theorem scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
    (a : ℝ) (ha : 0 < a) (R x : ℝ) (hxR : ‖x‖ ≤ R) :
    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Real.exp (a * R) := by
  have hx_le_R : x ≤ R :=
    (le_abs_self x).trans hxR
  have hax_le_aR : a * x ≤ a * R :=
    mul_le_mul_of_nonneg_left hx_le_R ha.le
  have hnorm_eq :
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ = Real.exp (a * x) := by
    calc
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
          Complex.abs (Complex.exp ((a : ℂ) * (x : ℂ))) := by
        exact Complex.norm_eq_abs (Complex.exp ((a : ℂ) * (x : ℂ)))
      _ =
          Real.exp (((a : ℂ) * (x : ℂ)).re) := by
        exact Complex.abs_exp ((a : ℂ) * (x : ℂ))
      _ =
          Real.exp
            ((a : ℂ).re * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg Real.exp (Complex.mul_re (a : ℂ) (x : ℂ))
      _ =
          Real.exp (a * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp
              (r * (x : ℂ).re - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re a)
      _ =
          Real.exp (a * x -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp (a * r - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re x)
      _ =
          Real.exp (a * x - 0 * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => Real.exp (a * x - r * (x : ℂ).im))
          (Complex.ofReal_im a)
      _ =
          Real.exp (a * x - 0) := by
        exact congrArg Real.exp (congrArg (fun r : ℝ => a * x - r)
          (zero_mul (x : ℂ).im))
      _ =
          Real.exp (a * x) := by
        exact congrArg Real.exp (sub_zero (a * x))
  exact (le_of_eq hnorm_eq).trans (Real.exp_le_exp.mpr hax_le_aR)

/-- Reciprocal factor in the positive away-zero Jordan majorant is bounded by
the away-from-zero threshold. -/
theorem scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
    (T x δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hδx : δ ≤ x) :
    (T * x)⁻¹ ≤ (T * δ)⁻¹ := by
  have hTδ_pos : 0 < T * δ :=
    mul_pos hT hδ
  have hTδ_le_Tx : T * δ ≤ T * x :=
    mul_le_mul_of_nonneg_left hδx hT.le
  exact inv_anti₀ hTδ_pos hTδ_le_Tx

/-- Product assembly for the positive upper-arc Jordan majorant away from
zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
    (a : ℝ) (ha : 0 < a) (R δ B : ℝ) (hδ : 0 < δ)
    (hB_nonneg : 0 ≤ B)
    (hpref :
      ∀ᶠ T in atTop,
        Real.pi * T / (T - a) ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let C : ℝ := B * δ⁻¹ * Real.exp (a * R)
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ :=
    inv_nonneg_of_nonneg hδ.le
  have hexp_nonneg : 0 ≤ Real.exp (a * R) :=
    (Real.exp_pos (a * R)).le
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg hB_nonneg hδ_inv_nonneg) hexp_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  exact
    (hpref.and (eventually_gt_atTop (max a 1))).mono
      (fun T hTpair =>
        fun x hδx hxR =>
          let Pref : ℝ := Real.pi * T / (T - a)
          let Rec : ℝ := (T * x)⁻¹
          let E : ℝ := ‖Complex.exp ((a : ℂ) * (x : ℂ))‖
          have hpref_le : Pref ≤ B := hTpair.1
          have hmax : max a 1 < T := hTpair.2
          have haT : a < T := (le_max_left a 1).trans_lt hmax
          have h_one_lt_T : 1 < T := (le_max_right a 1).trans_lt hmax
          have hT_pos : 0 < T := zero_lt_one.trans h_one_lt_T
          have hden_pos : 0 < T - a := sub_pos.mpr haT
          have hpref_nonneg : 0 ≤ Pref := by
            unfold Pref
            exact div_nonneg
              (mul_nonneg Real.pi_nonneg hT_pos.le)
              hden_pos.le
          have hrec_le_Tδ :
              Rec ≤ (T * δ)⁻¹ := by
            unfold Rec
            exact
              scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
                T x δ hT_pos hδ hδx
          have hδ_le_Tδ : δ ≤ T * δ := by
            calc
              δ = 1 * δ := by
                exact (one_mul δ).symm
              _ ≤ T * δ := by
                exact mul_le_mul_of_nonneg_right h_one_lt_T.le hδ.le
          have hTδ_inv_le : (T * δ)⁻¹ ≤ δ⁻¹ :=
            inv_anti₀ hδ hδ_le_Tδ
          have hrec_le : Rec ≤ δ⁻¹ :=
            hrec_le_Tδ.trans hTδ_inv_le
          have hrec_nonneg : 0 ≤ Rec := by
            unfold Rec
            exact inv_nonneg_of_nonneg (mul_nonneg hT_pos.le (hδ.le.trans hδx))
          have hE_le : E ≤ Real.exp (a * R) := by
            unfold E
            exact
              scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                a ha R x hxR
          have hE_nonneg : 0 ≤ E := by
            unfold E
            exact norm_nonneg _
          have h_pref_rec :
              Pref * Rec ≤ B * δ⁻¹ :=
            mul_le_mul hpref_le hrec_le hrec_nonneg hB_nonneg
          have h_product :
              (Pref * Rec) * E ≤ (B * δ⁻¹) * Real.exp (a * R) :=
            mul_le_mul h_pref_rec hE_le hE_nonneg
              (mul_nonneg hB_nonneg hδ_inv_nonneg)
          calc
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                (Pref * Rec) * E := by
              rfl
            _ ≤ (B * δ⁻¹) * Real.exp (a * R) := h_product
            _ = C := by
              rfl)

theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let B : ℝ := Real.pi + 1
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact add_nonneg Real.pi_nonneg zero_le_one
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
      a ha R δ B hδ hB_nonneg
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
        a)

/-- Positive upper-arc away-from-zero estimate from its Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
    (a : ℝ) (ha : 0 < a) (R δ Cj : ℝ) (hδ : 0 < δ)
    (hCj_nonneg : 0 ≤ Cj)
    (hjordan :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
              ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Cj) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  exact
    ⟨Cj, hCj_nonneg,
      (hjordan.and (eventually_gt_atTop a)).mono
        (fun T hTpair =>
          fun x hδx hxR =>
            have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
              hδ.trans_le hδx
            have harc :
                ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T :=
              (scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
                a ha x hxpos T hTpair.2).trans
                (scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
                  a ha x hxpos T hTpair.2)
            have hexp_nonneg :
                0 ≤ ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
              norm_nonneg _
            calc
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                  Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact norm_mul
                  (scalarFourierLaplacePlemelj_positiveUpperArc a x T)
                  (Complex.exp ((a : ℂ) * (x : ℂ)))
              _ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact mul_le_mul_of_nonneg_right harc hexp_nonneg
              _ ≤ Cj := hTpair.1 x hδx hxR)⟩

theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  match
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
      a ha R δ hδ
  with
  | ⟨Cj, hCj_nonneg, hjordan⟩ =>
      exact
        scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
          a ha R δ Cj hδ hCj_nonneg hjordan

end FixedLineCauchyProjection

end
end Boundary
