import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.UncompensatedDirichlet.Owner

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

theorem scalarFourierLaplacePlemelj_compactInterval_positive_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            0 < x →
            x < δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨C, hC_nonneg, hnear⟩ =>
      exact
        ⟨C, hC_nonneg,
          hnear.mono
            (fun T hT x hxpos hxδ hxR =>
              have hnorm : ‖x‖ = x := by
                exact (Real.norm_eq_abs x).trans (abs_of_pos hxpos)
              have hnorm_lt : ‖x‖ < δ :=
                hnorm.trans_lt hxδ
              hT x (ne_of_gt hxpos) hnorm_lt hxR)⟩

/-- Assembly of the positive compact-interval estimate from its near-zero and
away-from-zero pieces. -/
theorem scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually_of_split
    (a : ℝ) (ha : 0 < a) (R δ Cnear Caway : ℝ) (hδ : 0 < δ)
    (hCnear_nonneg : 0 ≤ Cnear) (hCaway_nonneg : 0 ≤ Caway)
    (hnear :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          0 < x →
          x < δ →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cnear)
    (haway :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Caway) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            0 < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let C : ℝ := max Cnear Caway
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact hCnear_nonneg.trans (le_max_left Cnear Caway)
  have hnear_le : Cnear ≤ C := by
    unfold C
    exact le_max_left Cnear Caway
  have haway_le : Caway ≤ C := by
    unfold C
    exact le_max_right Cnear Caway
  exact
    ⟨C, hC_nonneg,
      hnear.and haway |>.mono
        (fun T hsplit =>
          fun x hxpos hxR =>
            match lt_or_ge x δ with
            | Or.inl hx_lt_delta =>
                (hsplit.1 x hxpos hx_lt_delta hxR).trans hnear_le
            | Or.inr hx_ge_delta =>
                (hsplit.2 x hx_ge_delta hxR).trans haway_le)⟩

theorem scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            0 < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let δ : ℝ := 1
  have hδ : 0 < δ := by
    unfold δ
    exact zero_lt_one
  match scalarFourierLaplacePlemelj_compactInterval_positive_nearZero_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Cnear, hCnear_nonneg, hnear⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually
        a ha R δ hδ with
      | ⟨Caway, hCaway_nonneg, haway⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually_of_split
              a ha R δ Cnear Caway hδ hCnear_nonneg hCaway_nonneg
              hnear haway

/-- Reciprocal factor in the negative away-zero Jordan majorant is bounded by
the away-from-zero threshold. -/
theorem scalarFourierLaplacePlemelj_negative_awayZero_reciprocal_le
    (T x δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hxδ : x ≤ -δ) :
    (T * (-x))⁻¹ ≤ (T * δ)⁻¹ := by
  have hδ_negx : δ ≤ -x := by
    calc
      δ = -(-δ) := by
        exact (neg_neg δ).symm
      _ ≤ -x := by
        exact neg_le_neg hxδ
  have hTδ_pos : 0 < T * δ :=
    mul_pos hT hδ
  have hTδ_le_Tnegx : T * δ ≤ T * (-x) :=
    mul_le_mul_of_nonneg_left hδ_negx hT.le
  exact inv_anti₀ hTδ_pos hTδ_le_Tnegx

/-- Product assembly for the negative lower-arc Jordan majorant away from
zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
    (a : ℝ) (ha : 0 < a) (R δ B : ℝ) (hδ : 0 < δ)
    (hB_nonneg : 0 ≤ B)
    (hpref :
      ∀ᶠ (T : ℝ) in atTop,
        Real.pi * T / (T - a) ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let C : ℝ := B * δ⁻¹ * Real.exp (a * R)
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ :=
    inv_nonneg_of_nonneg hδ.le
  have hexp_nonneg : 0 ≤ Real.exp (a * R) :=
    (Real.exp_pos (a * R)).le
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg hB_nonneg hδ_inv_nonneg) hexp_nonneg
  exact
    ⟨C, hC_nonneg,
      (hpref.and (eventually_gt_atTop (max a 1))).mono
        (fun T hTpair =>
          fun x hxδ hxR =>
            let Pref : ℝ := Real.pi * T / (T - a)
            let Rec : ℝ := (T * (-x))⁻¹
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
                scalarFourierLaplacePlemelj_negative_awayZero_reciprocal_le
                  T x δ hT_pos hδ hxδ
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
            have hδ_negx_nonneg : 0 ≤ -x := by
              have hδ_le_negx : δ ≤ -x := by
                calc
                  δ = -(-δ) := by
                    exact (neg_neg δ).symm
                  _ ≤ -x := by
                    exact neg_le_neg hxδ
              exact hδ.le.trans hδ_le_negx
            have hrec_nonneg : 0 ≤ Rec := by
              unfold Rec
              exact inv_nonneg_of_nonneg
                (mul_nonneg hT_pos.le hδ_negx_nonneg)
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
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                  ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  (Pref * Rec) * E := by
                rfl
              _ ≤ (B * δ⁻¹) * Real.exp (a * R) := h_product
              _ = C := by
                rfl)⟩

theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let B : ℝ := Real.pi + 1
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact add_nonneg Real.pi_nonneg zero_le_one
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
      a ha R δ B hδ hB_nonneg
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
        a)

/-- Negative lower-arc away-from-zero estimate from its Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually_of_jordan
    (a : ℝ) (ha : 0 < a) (R δ Cj : ℝ) (hδ : 0 < δ)
    (hCj_nonneg : 0 ≤ Cj)
    (hjordan :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          x ≤ -δ →
          ‖x‖ ≤ R →
            scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
              ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Cj) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  exact
    ⟨Cj, hCj_nonneg,
      (hjordan.and (eventually_gt_atTop a)).mono
        (fun T hTpair =>
          fun x hxδ hxR =>
            have hxneg : x < 0 := by
              have hnegδ_neg : -δ < 0 := neg_lt_zero.mpr hδ
              exact hxδ.trans_lt hnegδ_neg
            have harc :
                ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
                  scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T :=
              (scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
                a ha x hxneg T hTpair.2).trans
                (scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
                  a ha x hxneg T hTpair.2)
            have hexp_nonneg :
                0 ≤ ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
              norm_nonneg _
            calc
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                  Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact norm_mul
                  (scalarFourierLaplacePlemelj_negativeLowerArc a x T)
                  (Complex.exp ((a : ℂ) * (x : ℂ)))
              _ ≤
                  scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact mul_le_mul_of_nonneg_right harc hexp_nonneg
              _ ≤ Cj := hTpair.1 x hxδ hxR)⟩

theorem scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  match
    scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually
      a ha R δ hδ
  with
  | ⟨Cj, hCj_nonneg, hjordan⟩ =>
      exact
        scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually_of_jordan
          a ha R δ Cj hδ hCj_nonneg hjordan

/-- Radius-qualified finite lower-half-plane pole-free identity for the
negative-time scalar window. -/
theorem scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T =
        0 := by
  have hclosed :
      scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 :=
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
      a ha x hx T hT
  exact
    (scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
      a x T).symm.trans hclosed

/-- Exact radius-qualified negative finite-window formula after moving the
compensating exponential inside the window. -/
theorem scalarFourierLaplacePlemelj_negative_window_with_exp_eq_neg_lowerArc_mul_exp_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))) =
      -(scalarFourierLaplacePlemelj_negativeLowerArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ))) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_negativeLowerArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  have hadd : W + A = 0 :=
    scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero_of_radius
      a ha x hx T hT
  have hmul : W * E + A * E = 0 := by
    calc
      W * E + A * E = (W + A) * E := by
        exact (add_mul W A E).symm
      _ = 0 * E := by
        exact congrArg (fun z : ℂ => z * E) hadd
      _ = 0 := by
        exact zero_mul E
  have hsub : W * E = -(A * E) := by
    calc
      W * E = (W * E + A * E) - A * E := by
        exact (add_sub_cancel_right (W * E) (A * E)).symm
      _ = 0 - A * E := by
        exact congrArg (fun z : ℂ => z - A * E) hmul
      _ = -(A * E) := by
        exact zero_sub (A * E)
  have hwindow :
      W * E =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
      a x T
  exact hwindow.symm.trans hsub

/-- Radius-qualified negative finite-window norm estimate from the compensated
lower-arc norm. -/
theorem scalarFourierLaplacePlemelj_negative_window_with_exp_norm_le_lowerArc_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
  let A : ℂ := scalarFourierLaplacePlemelj_negativeLowerArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let Wexp : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))
  have heq :
      Wexp = -(A * E) :=
    scalarFourierLaplacePlemelj_negative_window_with_exp_eq_neg_lowerArc_mul_exp_of_radius
      a ha x hx T hT
  calc
    ‖Wexp‖ = ‖-(A * E)‖ := by
      exact congrArg norm heq
    _ = ‖A * E‖ := by
      exact norm_neg (A * E)
    _ ≤ ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
        Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
      exact le_refl ‖A * E‖

/-- Negative-time away-from-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_awayZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨Carc, hCarc_nonneg, harc⟩ =>
      have hevent :
          ∀ᶠ (T : ℝ) in atTop,
            ∀ x : ℝ,
              x ≤ -δ →
              ‖x‖ ≤ R →
                ‖(∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ)))‖
                ≤ Carc :=
        (harc.and (eventually_gt_atTop (0 : ℝ))).mono
          (fun T hTpair =>
            fun x hxδ hxR =>
              have hxneg : x < 0 := by
                have hnegδ_neg : -δ < 0 := neg_lt_zero.mpr hδ
                exact hxδ.trans_lt hnegδ_neg
              have hwindow :
                  ‖(∫ t in Set.Icc (-T) T,
                    (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp ((a : ℂ) * (x : ℂ)))‖
                  ≤ ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                      Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
                scalarFourierLaplacePlemelj_negative_window_with_exp_norm_le_lowerArc_of_radius
                  a ha x hxneg T (hTpair.2)
              hwindow.trans (hTpair.1 x hxδ hxR))
      exact ⟨Carc, hCarc_nonneg, hevent⟩

/-- Negative-time near-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x < 0 →
            -δ < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨C, hC_nonneg, hnear⟩ =>
      exact
        ⟨C, hC_nonneg,
          hnear.mono
            (fun T hT x hxneg hδx hxR =>
              have hx_ne : x ≠ 0 := ne_of_lt hxneg
              have h_abs_lt : ‖x‖ < δ := by
                calc
                  ‖x‖ = -x := by
                    exact (Real.norm_eq_abs x).trans (abs_of_neg hxneg)
                  _ < δ := by
                    exact neg_lt.mp hδx
              hT x hx_ne h_abs_lt hxR)⟩

/-- Assembly of the negative compact-interval estimate from its near-zero and
away-from-zero pieces. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually_of_split
    (a : ℝ) (ha : 0 < a) (R δ Cnear Caway : ℝ) (hδ : 0 < δ)
    (hCnear_nonneg : 0 ≤ Cnear) (hCaway_nonneg : 0 ≤ Caway)
    (hnear :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          x < 0 →
          -δ < x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cnear)
    (haway :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          x ≤ -δ →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Caway) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x < 0 →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let C : ℝ := max Cnear Caway
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact hCnear_nonneg.trans (le_max_left Cnear Caway)
  have hnear_le : Cnear ≤ C := by
    unfold C
    exact le_max_left Cnear Caway
  have haway_le : Caway ≤ C := by
    unfold C
    exact le_max_right Cnear Caway
  exact
    ⟨C, hC_nonneg,
      hnear.and haway |>.mono
        (fun T hsplit =>
          fun x hxneg hxR =>
            match lt_or_ge (-δ) x with
            | Or.inl hx_near =>
                (hsplit.1 x hxneg hx_near hxR).trans hnear_le
            | Or.inr hx_not_near =>
                (hsplit.2 x hx_not_near hxR).trans haway_le)⟩

/-- Negative-time compact-interval estimate for the normalized scalar
Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x < 0 →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let δ : ℝ := 1
  have hδ : 0 < δ := by
    unfold δ
    exact zero_lt_one
  match scalarFourierLaplacePlemelj_compactInterval_negative_nearZero_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Cnear, hCnear_nonneg, hnear⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_negative_awayZero_norm_bound_eventually
        a ha R δ hδ with
      | ⟨Caway, hCaway_nonneg, haway⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually_of_split
              a ha R δ Cnear Caway hδ hCnear_nonneg hCaway_nonneg
              hnear haway

/-- Zero-time compact-interval estimate for the normalized scalar
Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_zero_norm_bound
    (a : ℝ) (ha : 0 < a) (R T x : ℝ) (hx_zero : x = 0) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ 2 * (Real.pi + 1) := by
  if hT : 0 ≤ T then
    have hbound :
        ‖(∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ))‖
          ≤ 2 * (Real.pi + 1) :=
      scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_zero
        a ha T x hT hx_zero
    have hwindow :
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ)) =
          ∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ)) :=
      scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
        a x T
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ 2 * (Real.pi + 1))
        hwindow
        hbound
  else
    have hT_lt : T < 0 :=
      lt_of_not_ge hT
    have hT_lt_neg : T < -T := by
      calc
        T < 0 := hT_lt
        _ < -T := neg_pos.mpr hT_lt
    have hinterval_empty : Set.Icc (-T) T = (∅ : Set ℝ) :=
      Set.Icc_eq_empty_of_lt hT_lt_neg
    have hintegral_zero :
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ))) = 0 := by
      exact Eq.subst
        (motive := fun s : Set ℝ =>
          (∫ t in s,
            (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ))) = 0)
        hinterval_empty.symm
        (setIntegral_empty
          (μ := volume)
          (f := fun t : ℝ =>
            (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ))))
    calc
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
          = ‖(0 : ℂ)‖ := by
            exact congrArg norm hintegral_zero
      _ = 0 := norm_zero
      _ ≤ 2 * (Real.pi + 1) :=
            mul_nonneg zero_le_two
              (add_nonneg Real.pi_pos.le zero_le_one)

/-- The maximum of the two one-sided compact-interval constants and the
zero-time constant is a common compact-interval Plemelj constant. -/
theorem scalarFourierLaplacePlemelj_compactInterval_commonConstant_bound
    (a : ℝ) (ha : 0 < a) (R Cpos Cneg : ℝ)
    (hCpos_nonneg : 0 ≤ Cpos) (hCneg_nonneg : 0 ≤ Cneg)
    (hpos :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          0 < x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cpos)
    (hneg :
      ∀ᶠ (T : ℝ) in atTop,
        ∀ x : ℝ,
          x < 0 →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cneg) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let Czero : ℝ := 2 * (Real.pi + 1)
  let C : ℝ := max (max Cpos Cneg) Czero
  have hCzero_nonneg : 0 ≤ Czero := by
    unfold Czero
    exact mul_nonneg zero_le_two
      (add_nonneg Real.pi_nonneg zero_le_one)
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact le_max_of_le_right hCzero_nonneg
  have hCpos_le : Cpos ≤ C := by
    unfold C
    exact (le_max_left Cpos Cneg).trans (le_max_left (max Cpos Cneg) Czero)
  have hCneg_le : Cneg ≤ C := by
    unfold C
    exact (le_max_right Cpos Cneg).trans (le_max_left (max Cpos Cneg) Czero)
  have hCzero_le : Czero ≤ C := by
    unfold C
    exact le_max_right (max Cpos Cneg) Czero
  exact
    ⟨C, hC_nonneg,
      hpos.and hneg |>.mono
        (fun T hboth =>
          fun x hxR =>
            match lt_trichotomy x 0 with
            | Or.inl hxneg =>
                (hboth.2 x hxneg hxR).trans hCneg_le
            | Or.inr hnonneg =>
                match hnonneg with
                | Or.inl hxzero =>
                    (scalarFourierLaplacePlemelj_compactInterval_zero_norm_bound
                      a ha R T x hxzero).trans hCzero_le
                | Or.inr hxpos =>
                    (hboth.1 x hxpos hxR).trans hCpos_le)⟩

/-- Compact-interval estimate for the normalized scalar Fourier-Laplace
Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + (t : ℂ) * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually
    a ha R with
  | ⟨Cpos, hCpos_nonneg, hpos⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually
        a ha R with
      | ⟨Cneg, hCneg_nonneg, hneg⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_commonConstant_bound
              a ha R Cpos Cneg hCpos_nonneg hCneg_nonneg hpos hneg

/-- Compact-interval scalar-window estimate for the fixed-right-line Cauchy
kernel.

This is the analytic core of compact-support domination: on every bounded
time interval, the finite scalar Cauchy windows are eventually uniformly
bounded in the truncation radius. -/
theorem fixedRightLine_scalarCauchyWindow_compactInterval_norm_bound_eventually
    (R c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C := by
  have ha : 0 < c - 1 :=
    sub_pos.mpr hc
  match scalarFourierLaplacePlemelj_compactInterval_norm_bound_eventually
    (c - 1) ha R with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      exact
        ⟨C, hC_nonneg,
          hC_eventual.mono
            (fun T hT =>
              fun x hx =>
                Eq.subst
                  (motive := fun z : ℂ => ‖z‖ ≤ C)
                  (fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow
                    c x T).symm
                  (hT x hx))⟩

/-- Compact-support scalar-window estimate on the time support of the kernel.

This is the local finite-window bound owned by the compact-support Cauchy
projection layer.  The scalar Cauchy windows are only required uniformly on
the compact set where the time kernel can be nonzero. -/
theorem fixedRightLine_scalarCauchyWindow_tsupport_norm_bound_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ x : ℝ,
            x ∈ tsupport K →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C := by
  have hbounded : Bornology.IsBounded (tsupport K) :=
    hK_compact.isBounded
  match hbounded.exists_norm_le with
  | ⟨R, hR⟩ =>
      match fixedRightLine_scalarCauchyWindow_compactInterval_norm_bound_eventually
        R c hc with
      | ⟨C, hC_nonneg, hC_eventual⟩ =>
          exact
            ⟨C, hC_nonneg,
              hC_eventual.mono
                (fun T hT =>
                  fun x hx =>
                    hT x (hR x hx))⟩

/-- Compact-support paired-window estimate for the fixed-right-line scalar
Cauchy kernel.

This is the true domination source: after pairing with the compactly supported
kernel, the finite scalar Cauchy windows are bounded by a constant times
`‖K x‖` eventually in the truncation radius. -/
theorem fixedRightLine_scalarCauchyWindow_compactSupport_paired_norm_bound_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ (T : ℝ) in atTop,
          ∀ᵐ x ∂volume,
            ‖K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C * ‖K x‖ := by
  match
    fixedRightLine_scalarCauchyWindow_tsupport_norm_bound_eventually
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      exact
        ⟨C, hC_nonneg,
          hC_eventual.mono
            (fun T hT =>
              Eventually.of_forall
                (fun x : ℝ =>
                  haveI : Decidable (x ∈ tsupport K) :=
                    Classical.propDecidable (x ∈ tsupport K)
                  if hx_support : x ∈ tsupport K then
                    let W : ℂ :=
                      ∫ t in Set.Icc (-T) T,
                        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))
                    have hW : ‖W‖ ≤ C :=
                      hT x hx_support
                    have hmul : ‖K x‖ * ‖W‖ ≤ ‖K x‖ * C :=
                      mul_le_mul_of_nonneg_left hW (norm_nonneg (K x))
                    calc
                      ‖K x * W‖ = ‖K x‖ * ‖W‖ := by
                        exact norm_mul (K x) W
                      _ ≤ ‖K x‖ * C := hmul
                      _ = C * ‖K x‖ := by
                        exact mul_comm ‖K x‖ C
                  else
                    let W : ℂ :=
                      ∫ t in Set.Icc (-T) T,
                        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))
                    have hK_zero : K x = 0 :=
                      image_eq_zero_of_nmem_tsupport hx_support
                    have hleft : ‖K x * W‖ = 0 := by
                      calc
                        ‖K x * W‖ = ‖(0 : ℂ) * W‖ := by
                          exact congrArg (fun z : ℂ => ‖z * W‖) hK_zero
                        _ = ‖(0 : ℂ)‖ := by
                          exact congrArg norm (zero_mul W)
                        _ = 0 := norm_zero
                    have hright : C * ‖K x‖ = 0 := by
                      calc
                        C * ‖K x‖ = C * ‖(0 : ℂ)‖ := by
                          exact congrArg (fun z : ℂ => C * ‖z‖) hK_zero
                        _ = C * 0 := by
                          exact congrArg (fun r : ℝ => C * r) norm_zero
                        _ = 0 := by
                          exact mul_zero C
                    Eq.subst
                      (motive := fun y : ℝ => ‖K x * W‖ ≤ y)
                      hright.symm
                      (Eq.subst
                        (motive := fun y : ℝ => y ≤ 0)
                        hleft.symm
                        (le_refl 0))))⟩

/-- Uniform compact-support domination for the paired scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_compactSupport_dominated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ G : ℝ → ℝ,
      Integrable G ∧
        0 ≤ᵐ[volume] G ∧
          ∀ᶠ (T : ℝ) in atTop,
            ∀ᵐ x ∂volume,
              ‖K x *
                (∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
                ≤ G x := by
  match
    fixedRightLine_scalarCauchyWindow_compactSupport_paired_norm_bound_eventually
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      let G : ℝ → ℝ := fun x : ℝ => C * ‖K x‖
      have hK_integrable : Integrable K volume :=
        hK_cont.integrable_of_hasCompactSupport hK_compact
      have hG_integrable : Integrable G volume :=
        hK_integrable.norm.const_mul C
      have hG_nonnegative : 0 ≤ᵐ[volume] G :=
        Eventually.of_forall
          (fun x : ℝ =>
            mul_nonneg hC_nonneg (norm_nonneg (K x)))
      exact
        ⟨G, hG_integrable, hG_nonnegative,
          hC_eventual.mono
            (fun T hT =>
              hT.mono
                (fun _ hx => hx))⟩

/-- Joint continuity of the finite scalar fixed-right-line Cauchy-window
integrand in the space and frequency variables. -/
theorem fixedRightLine_scalarCauchyWindow_integrand_joint_continuous
    (c : ℝ) (hc : 1 < c) :
    Continuous
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + (p.2 : ℂ) * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (p.2 : ℂ) * (p.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.1 : ℂ))) := by
  have hden :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c : ℂ) + (p.2 : ℂ) * Complex.I) - 1)) :=
    (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).sub
      continuous_const
  have hden_ne :
      ∀ p : ℝ × ℝ,
        (((c : ℂ) + (p.2 : ℂ) * Complex.I) - 1) ≠ 0 :=
    fun p : ℝ × ℝ =>
      fixedRightLine_cauchyDenominator_ne_zero c p.2 hc
  have hscalar :
      Continuous
        (fun p : ℝ × ℝ =>
          -1 / (((c : ℂ) + (p.2 : ℂ) * Complex.I) - 1)) :=
    continuous_const.div hden hden_ne
  have hphase :
      Continuous
        (fun p : ℝ × ℝ =>
          Complex.I * (p.2 : ℂ) * (p.1 : ℂ)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp continuous_fst)
  have hweight :
      Continuous
        (fun p : ℝ × ℝ =>
          ((c - 1 : ℝ) : ℂ) * (p.1 : ℂ)) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst)
  exact
    (hscalar.mul (Complex.continuous_exp.comp hphase)).mul
      (Complex.continuous_exp.comp hweight)

/-- Continuity of each finite scalar Cauchy window before pairing with the
compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_continuous
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    Continuous
      (fun x : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) :=
  continuous_parametric_integral_of_continuous
    (f := fun x : ℝ => fun t : ℝ =>
      (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    (fixedRightLine_scalarCauchyWindow_integrand_joint_continuous c hc)
    isCompact_Icc

/-- Continuity in the time variable of each finite scalar Cauchy window paired
against the smooth compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_continuous
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    Continuous
      (fun x : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) := by
  exact hK_cont.mul
    (fixedRightLine_scalarCauchyWindow_continuous c hc T)

/-- A.e.-strong measurability of the paired scalar Cauchy window kernels. -/
theorem fixedRightLine_scalarCauchyWindow_paired_aestronglyMeasurable_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∀ᶠ (T : ℝ) in atTop,
      AEStronglyMeasurable
        (fun x : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        volume := by
  exact
    Eventually.of_forall
      (fun T : ℝ =>
        (fixedRightLine_scalarCauchyWindow_paired_continuous
          K hK_cont hK_compact hK_smooth c hc T).aestronglyMeasurable)

/-- Positive-time paired scalar Cauchy window limit after multiplication by
the compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_positive
    (K : ℝ → ℂ) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun T : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝 (-2 * (Real.pi : ℂ))) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_positive
      c hc x hx
  have hmul :
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝 (K x * (-2 * (Real.pi : ℂ)))) :=
    tendsto_const_nhds.mul hscalar
  have hcomm :
      K x * (-2 * (Real.pi : ℂ)) =
        (-2 * (Real.pi : ℂ)) * K x :=
    mul_comm (K x) (-2 * (Real.pi : ℂ))
  have hindicator :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x =
        (-2 * (Real.pi : ℂ)) * K x :=
    indicator_of_mem hx
      (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)
  have htarget :
      K x * (-2 * (Real.pi : ℂ)) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x :=
    hcomm.trans hindicator.symm
  exact htarget ▸ hmul

/-- Negative-time paired scalar Cauchy window limit after multiplication by
the compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_negative
    (K : ℝ → ℂ) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝 0) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_negative
      c hc x hx
  have hmul :
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝 (K x * 0)) :=
    tendsto_const_nhds.mul hscalar
  have hzero :
      K x * (0 : ℂ) = 0 :=
    mul_zero (K x)
  have hnotMem :
      x ∉ Set.Ioi (0 : ℝ) :=
    fun hxpos => not_lt_of_gt hx hxpos
  have hindicator :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x =
        0 :=
    indicator_of_not_mem hnotMem
      (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)
  have htarget :
      K x * (0 : ℂ) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x :=
    hzero.trans hindicator.symm
  exact htarget ▸ hmul

/-- A.e. paired scalar Cauchy window limit against the open positive half-line. -/
theorem fixedRightLine_scalarCauchyWindow_ae_tendsto_openHalfLineKernel
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hnotEndpoint :
      ∀ᵐ x ∂volume, x ∉ ({0} : Set ℝ) :=
    (Set.countable_singleton (0 : ℝ)).ae_not_mem volume
  exact
    hnotEndpoint.mono
      (fun x hxNotEndpoint =>
        match lt_or_gt_of_ne
          (fun hxEq : x = 0 =>
            hxNotEndpoint (Set.mem_singleton_iff.mpr hxEq)) with
        | Or.inl hxneg =>
            fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_negative
              K c hc x hxneg
        | Or.inr hxpos =>
            fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_positive
              K c hc x hxpos)

/-- Paired symmetric-window scalar Cauchy kernel convergence against a smooth
compact support kernel, with the open positive half-line as boundary value. -/
theorem fixedRightLine_scalarCauchyWindow_paired_tendsto_openHalfLineIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x in Set.Ioi (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x)) := by
  match
    fixedRightLine_scalarCauchyWindow_compactSupport_dominated
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨G, hG_int, hG_nonneg, hG_bound⟩ =>
      have hmeas :
          ∀ᶠ (T : ℝ) in atTop,
            AEStronglyMeasurable
              (fun x : ℝ =>
                K x *
                  (∫ t in Set.Icc (-T) T,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
              volume :=
        fixedRightLine_scalarCauchyWindow_paired_aestronglyMeasurable_eventually
          K hK_cont hK_compact hK_smooth c hc
      have hae :
          ∀ᵐ x ∂volume,
            Tendsto
              (fun T : ℝ =>
                K x *
                  (∫ t in Set.Icc (-T) T,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
              atTop
              (𝓝
                (Set.indicator (Set.Ioi (0 : ℝ))
                  (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) :=
        fixedRightLine_scalarCauchyWindow_ae_tendsto_openHalfLineKernel
          K hK_cont hK_compact hK_smooth c hc
      have htarget :
          (∫ x : ℝ,
            Set.indicator (Set.Ioi (0 : ℝ))
              (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x) =
            ∫ x in Set.Ioi (0 : ℝ),
              (-2 * (Real.pi : ℂ)) * K x := by
        exact integral_indicator measurableSet_Ioi
      exact
        htarget ▸
          tendsto_integral_filter_of_dominated_convergence
            G hmeas hG_bound hG_int hae

/-- Paired symmetric-window scalar Cauchy kernel convergence against a smooth
compact support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_tendsto_indicatorIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have hopen :
      Tendsto
        (fun T : ℝ =>
          ∫ x : ℝ,
            K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x in Set.Ioi (0 : ℝ),
            (-2 * (Real.pi : ℂ)) * K x)) :=
    fixedRightLine_scalarCauchyWindow_paired_tendsto_openHalfLineIntegral
      K hK_cont hK_compact hK_smooth c hc
  have hclosed :
      (∫ x in Set.Ioi (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x) =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x :=
    fixedRightLine_scalarProjection_Ioi_integral_eq_Ici_integral K
  have hindicator :
      (∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x) =
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) :=
    (fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
      K).symm
  exact hindicator ▸ hclosed ▸ hopen

/-- Paired symmetric-window Cauchy kernel convergence against a smooth compact
support kernel on the fixed right line. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_scalarKernelIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ x : ℝ,
            K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x : ℝ,
            K x *
              Set.indicator (Set.Ici (0 : ℝ))
                (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_paired_tendsto_indicatorIntegral
      K hK_cont hK_compact hK_smooth c hc
  have hfunctions :
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
    funext
      (fun T : ℝ =>
        fixedRightLine_fourierCauchy_symmetricWindow_eq_scalarWindowIntegral
          K hK_cont hK_compact hK_smooth c hc T)
  exact hfunctions.symm ▸ hscalar

/-- Full-line Fourier-Cauchy inversion before collapsing the scalar Cauchy
kernel to the one-sided projection integral. -/
theorem fixedRightLine_fourierCauchy_fullLine_smooth_scalarKernelIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        K x *
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
  have hfull :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ t : ℝ,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
      K hK_cont hK_compact hK_smooth c hc
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x : ℝ,
            K x *
              Set.indicator (Set.Ici (0 : ℝ))
                (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_scalarKernelIntegral
      K hK_cont hK_compact hK_smooth c hc
  exact tendsto_nhds_unique hfull hscalar

/-- Smooth product-level Cauchy projection on the fixed right line.

This is the ordinary-integral owner statement: smooth compact support supplies
the decay needed to interpret the Cauchy multiplier as a genuine full-line
integral before taking the one-sided boundary projection. -/
theorem fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
          exact
            fixedRightLine_fourierCauchy_fullLine_smooth_scalarKernelIntegral
              K hK_cont hK_compact hK_smooth c hc
    _ =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x := by
          exact
            fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
              K

/-- Symmetric truncations of the smooth fixed-line Fourier-Cauchy multiplier
converge to the positive-time one-sided projection. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x)) := by
  have hfull :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ t : ℝ,
            (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
      K hK_cont hK_compact hK_smooth c hc
  have hvalue :
      (∫ t : ℝ,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x :=
    fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
      K hK_cont hK_compact hK_smooth c hc
  exact hvalue ▸ hfull

/-- Generic one-sided Fourier-Cauchy inversion for a smooth compactly supported
time-side kernel on the fixed right line. -/
theorem fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  exact
    fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
      K hK_cont hK_compact hK_smooth c hc

/-- Full-line Cauchy inversion after the vertical slice has already been
rewritten as the Fourier transform of the right projection kernel. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) *
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x :=
          fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
            (zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_contDiff_admissible f)
            c hc
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
          unfold zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
          unfold zetaLaplaceTransform_rightOnePoleProjectionKernel
          exact
            setIntegral_congr_fun measurableSet_Ici
              (fun x _hx =>
                (mul_assoc
                  (-2 * (Real.pi : ℂ))
                  (f.toZetaTestFunction' x)
                  (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)))).symm)

/-- One-sided Cauchy inversion for the right projection kernel on the fixed
line.

This is the genuine analytic core: the full-line Fourier-Cauchy multiplier
integral recovers the positive-time half-line projection value. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2))
        =
        ∫ t : ℝ,
          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact
            integral_congr_ae
              (Eventually.of_forall
                (fun t : ℝ =>
                  congrArg
                    (fun z : ℂ =>
                      (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) * z)
                    (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                      f.toZetaTestFunction' c t)))
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c :=
          zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
            f c hc

/-- Inverse-quadratic truncation control for the fixed right Cauchy multiplier
after its full-line Cauchy value has been identified. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_truncationTail_inverseQuadratic
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) -
            (∫ t : ℝ,
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2))‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
      (zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_contDiff_admissible f)
      c hc height hcofinal
  with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      exact ⟨MR, hMR_pos,
        hMR_eventual.mono
          (fun u hu =>
            let hfinite :
                (∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) =
                  (∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      (∫ x : ℝ,
                        zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
                setIntegral_congr_fun measurableSet_Icc
                  (fun t _ht =>
                    congrArg
                      (fun z : ℂ =>
                        (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) * z)
                      (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                        f.toZetaTestFunction' c t))
            let hfull :
                (∫ t : ℝ,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) =
                  (∫ t : ℝ,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      (∫ x : ℝ,
                        zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
                integral_congr_ae
                  (Eventually.of_forall
                    (fun t : ℝ =>
                      congrArg
                        (fun z : ℂ =>
                          (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) * z)
                        (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                          f.toZetaTestFunction' c t)))
            Eq.subst
              (motive := fun finiteValue : ℂ =>
                ‖finiteValue -
                  (∫ t : ℝ,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2))‖
                  ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
              hfinite.symm
              (Eq.subst
                (motive := fun fullValue : ℂ =>
                  ‖(∫ t in Set.Icc (-(height u)) (height u),
                      (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                        (∫ x : ℝ,
                          zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                            Complex.exp
                              (Complex.I * (t : ℂ) * (x : ℂ)) *
                            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) -
                    fullValue‖
                    ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
                hfull.symm
                hu))⟩

/-- Kernel-level Fourier-Cauchy multiplier estimate for the right one-pole
projection.

This is the analytic owner sink: after the vertical-line Laplace slice is
rewritten as the Fourier transform of
`zetaLaplaceTransform_rightOnePoleProjectionKernel`, the Cauchy multiplier
`((c - 1) + it)⁻¹` projects onto the positive time half-line with an
inverse-quadratic symmetric truncation tail. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fixedLineCauchyMultiplier_estimate
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) -
            zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    zetaLaplaceTransform_rightOnePoleProjectionKernel_truncationTail_inverseQuadratic
      f c hc height hcofinal
  with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      exact ⟨MR, hMR_pos,
        hMR_eventual.mono
          (fun u hu =>
            let hvalue :
                (∫ t : ℝ,
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) =
                  zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c :=
                zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue
                  f c hc
            Eq.subst
              (motive := fun z : ℂ =>
                ‖(∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) -
                  z‖
                  ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
              hvalue
              hu)⟩

/-- Fixed-line Fourier-Cauchy projection theorem for compactly supported
logarithmic test functions.

This is the transform-calculus owner theorem: the symmetric truncations of the
right half-plane Cauchy multiplier on the fixed line converge to the one-sided
time projection with inverse-quadratic tail. -/
theorem zetaLaplaceTransform_fixedLine_rightOnePoleCauchyProjection_eventual_inverseQuadratic_to_value
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + (t : ℂ) * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)) -
            zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  exact
    zetaLaplaceTransform_rightOnePoleProjectionKernel_fixedLineCauchyMultiplier_estimate
      f c hc height hcofinal

end FixedLineCauchyProjection

end
end Boundary
