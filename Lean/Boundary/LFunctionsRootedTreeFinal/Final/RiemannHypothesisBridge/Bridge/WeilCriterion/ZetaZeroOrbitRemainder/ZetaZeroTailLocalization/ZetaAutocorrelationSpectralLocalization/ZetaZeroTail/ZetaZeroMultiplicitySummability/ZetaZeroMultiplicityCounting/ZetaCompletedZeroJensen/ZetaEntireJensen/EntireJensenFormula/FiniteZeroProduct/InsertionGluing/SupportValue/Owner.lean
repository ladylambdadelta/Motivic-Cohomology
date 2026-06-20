import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.FiniteGluing.Owner

/-!
# Normalized factor insertion and removable gluing

This owner layer was split from `FiniteZeroProduct.InsertionGluing.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Zero-freeness split over the finite support image.

The off-support branch is supplied by the punctured quotient/product
factorization; the support branch is supplied by the local removable value
calculation at the indexed support zero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_zeroFree_from_support_split
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hoff :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        w ∉
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ).image
            (fun z : EntireFunctionZero F => (z : ℂ)) →
        Q w ≠ 0)
    (hon :
      ∀ z : EntireFunctionZero F,
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ →
        Q (z : ℂ) ≠ 0) :
    ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  intro w hwρ
  exact
    if hw :
        w ∈
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ).image
            (fun z : EntireFunctionZero F => (z : ℂ)) then
      match Finset.mem_image.1 hw with
      | Exists.intro z hz_data =>
          match hz_data with
          | And.intro hz hzw =>
              Eq.subst (motive := fun x : ℂ => Q x ≠ 0) hzw (hon z hz)
    else
      hoff w hwρ hw

/-- A nonzero zero in the closed disk belongs to the closed-disk support
divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_of_zero_ne_zero_norm_le
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    {w : ℂ}
    (hFw : F w = 0)
    (hw0 : w ≠ 0)
    (hwρ : ‖w‖ ≤ ρ) :
    (⟨w, hFw⟩ : EntireFunctionZero F) ∈
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ := by
  have hsupport :
      (⟨w, hFw⟩ : EntireFunctionZero F) ∈ Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ z) :=
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_ne_zero_of_ne_zero_norm_le_ownerRoot
      F hF hF0 ρ ⟨w, hFw⟩ hw0 hwρ
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
      F hF hF0 ρ hsupport

/-- Off the closed-disk support image, a point of the closed disk is not a zero
of `F`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_function_nonzero_of_not_mem_closedDiskSupport
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    {w : ℂ}
    (hwρ : ‖w‖ ≤ ρ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ))) :
    F w ≠ 0 := by
  intro hFw
  exact
    if hw0 : w = 0 then
      hF0 (Eq.subst (motive := fun x : ℂ => F x = 0) hw0 hFw)
    else
      have hz_mem :
        (⟨w, hFw⟩ : EntireFunctionZero F) ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_of_zero_ne_zero_norm_le
          F hF hF0 ρ hFw hw0 hwρ
      hw (Finset.mem_image.mpr
        (Exists.intro (⟨w, hFw⟩ : EntireFunctionZero F)
          (And.intro hz_mem rfl)))

/-- Off the closed-disk support, a zero of any exact closed-support quotient
would force a zero of `F`, contradicting support exclusion. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_of_not_mem_support
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    {w : ℂ}
    (hwρ : ‖w‖ ≤ ρ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ))) :
    Q w ≠ 0 := by
  have hFw_ne :
      F w ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_function_nonzero_of_not_mem_closedDiskSupport
      F hF hF0 ρ hwρ hw
  intro hQw
  have hfactor_w :
      F w =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ w :=
    hfactor w hwρ
  have hF_zero : F w = 0 :=
    Eq.trans hfactor_w
      (Eq.trans
        (congrArg
          (fun x : ℂ =>
            x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                F hF hF0 ρ w)
          hQw)
        (zero_mul
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ w)))
  exact hFw_ne hF_zero

/-- Pointwise cancellation of the local multiplicity factor against the finite
normalized product away from the support centers. -/
theorem entireFunction_finiteNormalizedFactorization_puncturedCancellation_pointwise
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (ha0 : (a : ℂ) ≠ 0)
    (g : ℂ → ℂ)
    {w : ℂ}
    (hwρ : ‖w‖ ≤ ρ)
    (hwa : w ≠ (a : ℂ))
    (hw_erase :
      ∀ z : EntireFunctionZero F,
        z ∈ S.erase a →
          w ≠ (z : ℂ))
    (hg_factor_w :
      F w =
        (w - (a : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (a : ℂ) •
          g w) :
    Q w =
      g w /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (w : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  -- Deep algebraic cancellation lemma: split the finite product at `a`, use
  -- `(1 - w/a)^m = (-a⁻¹)^m (w-a)^m`, and cancel the nonzero factors
  -- `(w-a)^m` and the erased support product.
  let m : ℕ := entireFunctionZeroMultiplicity F hF (a : ℂ)
  let P : ℂ := (w - (a : ℂ)) ^ m
  let C : ℂ := (-(a : ℂ)⁻¹) ^ m
  let E : ℂ :=
    ∏ z in S.erase a,
      (1 - (w : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ)
  have hP_ne : P ≠ 0 := by
    have hsub_ne : w - (a : ℂ) ≠ 0 :=
      sub_ne_zero.mpr hwa
    exact pow_ne_zero m hsub_ne
  have hC_ne : C ≠ 0 := by
    have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero ha0
    have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
      neg_ne_zero.mpr hinv_ne
    exact pow_ne_zero m hneg_ne
  have hE_ne : E ≠ 0 := by
    exact
      Finset.prod_ne_zero_iff.mpr
        (fun z hz =>
          pow_ne_zero
              (entireFunctionZeroMultiplicity F hF (z : ℂ))
            (fun hfactor =>
              hw_erase z hz
                ((entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_factor_eq_zero_iff
                  F hF S
                  (fun y hy => hS0 y hy)
                  z (Finset.mem_of_mem_erase hz) w).1 hfactor)))
  have hD_ne : C * E ≠ 0 :=
    mul_ne_zero hC_ne hE_ne
  have hfactor_local :
      (1 - w / (a : ℂ)) ^ m = C * P := by
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
        ha0 m
  have hsplit :
      (1 - w / (a : ℂ)) ^ m * E =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w := by
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_mul_erase
        F hF S a ha w
  have hproduct_local :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w =
        P * (C * E) := by
    calc
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w =
          (1 - w / (a : ℂ)) ^ m * E := by
        exact hsplit.symm
      _ = (C * P) * E := by
        exact congrArg (fun x : ℂ => x * E) hfactor_local
      _ = P * (C * E) := by
        calc
          (C * P) * E = C * (P * E) := mul_assoc C P E
          _ = C * (E * P) := by
            exact congrArg (fun x : ℂ => C * x) (mul_comm P E)
          _ = (C * E) * P := (mul_assoc C E P).symm
          _ = P * (C * E) := mul_comm (C * E) P
  have hg_mul : F w = P * g w := by
    exact Eq.trans hg_factor_w (smul_eq_mul ℂ : P • g w = P * g w)
  have hmain :
      Q w * (P * (C * E)) = P * g w := by
    calc
      Q w * (P * (C * E)) =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w := by
        exact congrArg (fun x : ℂ => Q w * x) hproduct_local.symm
      _ = F w := by
        exact (hfactor w hwρ).symm
      _ = P * g w := by
        exact hg_mul
  have hcancel : Q w * (C * E) = g w := by
    have hleft :
        P * (Q w * (C * E)) = P * g w := by
      calc
        P * (Q w * (C * E)) =
            Q w * (P * (C * E)) := by
          exact mul_left_comm P (Q w) (C * E)
        _ = P * g w := by
          exact hmain
    exact mul_left_cancel₀ hP_ne hleft
  calc
    Q w = (Q w * (C * E)) / (C * E) := by
      exact (mul_div_cancel_right₀ (Q w) hD_ne).symm
    _ = g w / (C * E) := by
      exact congrArg (fun x : ℂ => x / (C * E)) hcancel

/-- Closed-disk punctured cancellation for a finite normalized factorization.

This is the pointwise algebraic cancellation statement on the accumulating
closed-disk side of a support point.  It combines the finite-product erase
formula, the normalized/local factor identity, and cancellation of
`(w-a)^m` away from `a`. -/
theorem entireFunction_finiteNormalizedFactorization_frequentlyEq_localRemovableModel
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    ∃ᶠ w in 𝓝[≠] (a : ℂ),
      Q w =
        g w /
          (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in S.erase a,
              (1 - (w : ℂ) / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  have ha0 : (a : ℂ) ≠ 0 :=
    hS0 a ha
  have hgood :
      ∃ᶠ w in 𝓝[≠] (a : ℂ),
        w ≠ (a : ℂ) ∧
        ‖w‖ ≤ ρ ∧
          ∀ z : EntireFunctionZero F,
            z ∈ S.erase a →
              w ≠ (z : ℂ) :=
    entireFunction_closedDisk_puncturedGoodPoints_frequently
      F S a ha ha0 ρ haρ
  have hlocal_punctured :
      ∀ᶠ w in 𝓝[≠] (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w :=
    hg_factor.filter_mono nhdsWithin_le_nhds
  exact
    (Filter.Eventually.and_frequently hlocal_punctured hgood).mono
      (fun w hw =>
        entireFunction_finiteNormalizedFactorization_puncturedCancellation_pointwise
          F Q hF ρ S hS0 hfactor a ha ha0 g
          hw.2.2.1
          hw.2.1
          hw.2.2.2
          hw.1)

/-- Analyticity of the explicit local removable model at a support point.

The denominator is the normalized leading coefficient of the finite divisor:
the `a` factor contributes `(-a⁻¹)^m`, and all remaining factors are nonzero
at `a`. -/
theorem entireFunction_finiteNormalizedFactorization_localRemovableModel_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ)) :
    AnalyticAt ℂ
      (fun w : ℂ =>
        g w /
          (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in S.erase a,
              (1 - w / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ))))
      (a : ℂ) := by
  have hcoeff_an :
      AnalyticAt ℂ
        (fun _w : ℂ =>
          (-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ))
        (a : ℂ) :=
    analyticAt_const
  have hprod_an :
      AnalyticAt ℂ
        (fun w : ℂ =>
          ∏ z in S.erase a,
            (1 - w / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))
        (a : ℂ) :=
    (S.erase a).analyticAt_prod
      (fun z _hz =>
        (analyticAt_const.sub
          (analyticAt_id.mul analyticAt_const)).pow
            (entireFunctionZeroMultiplicity F hF (z : ℂ)))
  have hden_an :
      AnalyticAt ℂ
        (fun w : ℂ =>
          ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in S.erase a,
              (1 - w / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ)))
        (a : ℂ) :=
    hcoeff_an.mul hprod_an
  have hden_ne :
      ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_localLeadingCoeff_nonzero_at_support
      F hF S hS0 a ha
  exact hg_an.div hden_an hden_ne

/-- Punctured local quotient identity forced by a finite normalized
factorization.

This is the exact cancellation theorem for the finite divisor at a support
point.  On punctured points near `a`, the local Taylor factor
`(w-a)^m`, the normalized factor identity
`(1-w/a)^m = (-(a⁻¹))^m (w-a)^m`, and the nonvanishing of all other finite
factors cancel to identify `Q` with the explicit local removable model. -/
theorem entireFunction_finiteNormalizedFactorization_eventuallyEq_localRemovableModel
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q =ᶠ[𝓝[≠] (a : ℂ)]
      fun w : ℂ =>
        g w /
          (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in S.erase a,
              (1 - (w : ℂ) / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  let localModel : ℂ → ℂ :=
    fun w : ℂ =>
      g w /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - w / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ)))
  have hQ_at : AnalyticAt ℂ Q (a : ℂ) :=
    hQ_an (a : ℂ) haρ
  have hmodel_at : AnalyticAt ℂ localModel (a : ℂ) := by
    exact
      entireFunction_finiteNormalizedFactorization_localRemovableModel_analyticAt
        F hF S hS0 a ha g hg_an
  have hfreq :
      ∃ᶠ w in 𝓝[≠] (a : ℂ), Q w = localModel w :=
    entireFunction_finiteNormalizedFactorization_frequentlyEq_localRemovableModel
      F Q hF ρ S hS0 hfactor a ha haρ g hg_factor
  exact
    analyticAt_eventuallyEq_punctured_of_frequentlyEq_punctured
      hQ_at hmodel_at hfreq

/-- Local removable value forced by a closed-disk factorization.

This is the identity-principle/removable-value cut behind support-point
zero-freeness.  A quotient analytic at `a` that satisfies the exact finite
factorization on the closed disk has, at the support point, the value dictated
by the local Taylor unit and the leading coefficient of the normalized finite
divisor. -/
theorem entireFunction_finiteNormalizedFactorization_forces_localRemovableValue
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q (a : ℂ) =
      g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  let localModel : ℂ → ℂ :=
    fun w : ℂ =>
      g w /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - w / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ)))
  have hQ_at : AnalyticAt ℂ Q (a : ℂ) :=
    hQ_an (a : ℂ) haρ
  have hmodel_at : AnalyticAt ℂ localModel (a : ℂ) := by
    exact
      entireFunction_finiteNormalizedFactorization_localRemovableModel_analyticAt
        F hF S hS0 a ha g hg_an
  have hpunctured :
      Q =ᶠ[𝓝[≠] (a : ℂ)] localModel :=
    entireFunction_finiteNormalizedFactorization_eventuallyEq_localRemovableModel
      F Q hF ρ S hS0 hQ_an hfactor a ha haρ g hg_an hg_factor
  exact
    analyticAt_eq_at_of_eventuallyEq_punctured
      hQ_at hmodel_at hpunctured

/-- Value of a single normalized removable quotient at the removed zero.

The local Taylor unit `g` determines the filled quotient value at `a`: after
substituting
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m`, all remaining factors are nonzero at `a`,
so analytic continuation forces the displayed quotient value. -/
theorem entireFunction_singleZeroNormalizedFactor_removableValue
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q (a : ℂ) =
      g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  exact
    entireFunction_finiteNormalizedFactorization_forces_localRemovableValue
      F Q hF ρ S hS0 hQ_an hfactor a ha haρ g hg_an hg_ne hg_factor

/-- Single-zero removable value after normalized factor extraction.

This is the value form of the normalized-factor removable theorem.  It says
that once a quotient is known to satisfy the finite divisor factorization, its
value at a support zero is forced by the local analytic unit and the leading
coefficient of the normalized extracted divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_singleZeroNormalizedFactor_removableValue_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q (a : ℂ) =
      g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  exact
    entireFunction_singleZeroNormalizedFactor_removableValue
      F Q hF ρ S hS0 hQ_an hfactor a ha haρ g hg_an hg_ne hg_factor

/-- Local removable quotient value after extracting an arbitrary finite
normalized divisor.

At a support point `a`, the local order factorization of `F` gives
`F(w) = (w-a)^m g(w)`.  The normalized divisor has local leading coefficient
`(-(a⁻¹))^m` times all other support factors evaluated at `a`; hence the
removable quotient value is the displayed ratio. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_localRemovableValue_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q (a : ℂ) =
      g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_singleZeroNormalizedFactor_removableValue_ownerRoot
      F Q hF ρ S hS0 hQ_an hfactor a ha haρ g hg_an hg_ne hg_factor

/-- The support-point value of a removable quotient is the local Taylor unit
divided by the leading coefficient of the extracted finite divisor.

This is the single-zero removable quotient value theorem consumed by the
support-point zero-freeness proof.  It is the local consequence of
`AnalyticAt.order_eq_nat_iff`: the factor `(w - a)^m` in `F` cancels the
indexed factor `(1 - w/a)^m`, and all remaining finite-support factors are
nonzero at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_supportPoint_value_eq_localRemovableValue_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    Q (a : ℂ) =
      g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_localRemovableValue_ownerRoot
      F Q hF ρ S hS0 hQ_an hfactor a ha haρ g hg_an hg_ne hg_factor

/-- Support-point nonvanishing for a closed-support quotient after extracting
the exact local multiplicity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_at_support_from_maximalMultiplicity_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    Q (z : ℂ) ≠ 0 := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ
  have hS0 : ∀ a : EntireFunctionZero F, a ∈ S → (a : ℂ) ≠ 0 := by
    intro a ha
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ a ha
  have hzρ : ‖(z : ℂ)‖ ≤ ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_norm_le
      F hF hF0 ρ z hz
  match
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
      F hF hF0 ρ z hz
  with
  | ⟨g, hg_an, hg_ne, hg_factor⟩ =>
    have hfactorS :
        ∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w := by
      intro w hw
      exact hfactor w hw
    have hQ_value :
        Q (z : ℂ) =
          g (z : ℂ) /
            (((-(z : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) *
              (∏ a in S.erase z,
                (1 - (z : ℂ) / (a : ℂ)) ^
                  entireFunctionZeroMultiplicity F hF (a : ℂ))) :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_supportPoint_value_eq_localRemovableValue_ownerRoot
        F Q hF ρ S hS0 hQ_an hfactorS z hz hzρ g hg_an hg_ne hg_factor
    have hvalue_ne :
        g (z : ℂ) /
            (((-(z : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) *
              (∏ a in S.erase z,
                (1 - (z : ℂ) / (a : ℂ)) ^
                  entireFunctionZeroMultiplicity F hF (a : ℂ))) ≠ 0 :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_supportPoint_removableValue_nonzero

end
end LFunctions
end Boundary
