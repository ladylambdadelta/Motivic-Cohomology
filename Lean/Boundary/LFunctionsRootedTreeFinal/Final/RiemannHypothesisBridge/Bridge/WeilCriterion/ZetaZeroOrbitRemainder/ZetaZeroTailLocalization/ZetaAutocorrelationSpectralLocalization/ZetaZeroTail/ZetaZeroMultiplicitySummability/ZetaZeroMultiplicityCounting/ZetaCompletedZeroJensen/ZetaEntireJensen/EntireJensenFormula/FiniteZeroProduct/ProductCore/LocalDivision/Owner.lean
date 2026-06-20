import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.ProductCore.QuotientTransport.Owner

/-!
# Finite zero-product core

This owner layer was split from `FiniteZeroProduct.ProductCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Empty finite divisor extraction: the removable quotient is the original
entire function. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_empty
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF ∅ w) ∧
      Q 0 = F 0 := by
  have hF_an :
      ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ F w :=
    fun w _hw => hF w
  have hF_mul :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          F w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF ∅ w := by
    intro w _hw
    calc
      F w = F w * 1 := by
        exact (mul_one (F w)).symm
      _ =
          F w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF ∅ w := by
        rfl
  have hF_origin : F 0 = F 0 :=
    rfl
  exact Exists.intro F (And.intro hF_an (And.intro hF_mul hF_origin))

/-- The normalized extracted factor has value `1` at the origin. -/
theorem entireFunction_normalizedFactor_pow_at_zero
    {a : ℂ}
    (m : ℕ) :
    (1 - (0 : ℂ) / a) ^ m = 1 := by
  have hzero_div : (0 : ℂ) / a = 0 :=
    zero_div a
  have hbase : 1 - (0 : ℂ) / a = 1 := by
    calc
      1 - (0 : ℂ) / a = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hzero_div
      _ = 1 := sub_zero 1
  calc
    (1 - (0 : ℂ) / a) ^ m = (1 : ℂ) ^ m := by
      exact congrArg (fun x : ℂ => x ^ m) hbase
    _ = 1 := one_pow m

/-- Inserting one normalized nonzero factor preserves the finite product
at the origin. -/
theorem entireFunction_finiteZeroDivisorProduct_insert_at_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha : a ∉ S) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF (insert a S) 0 =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF S 0 := by
  have hinsert :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) 0 =
        (1 - (0 : ℂ) / (a : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (a : ℂ) *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF S 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
      F hF S a ha 0
  have hfactor_one :
      (1 - (0 : ℂ) / (a : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (a : ℂ) = 1 :=
    entireFunction_normalizedFactor_pow_at_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF (insert a S) 0 =
        (1 - (0 : ℂ) / (a : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (a : ℂ) *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF S 0 := hinsert
    _ =
        1 *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF S 0 := by
      exact
        congrArg
          (fun x : ℂ =>
            x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S 0)
          hfactor_one
    _ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S 0 :=
      one_mul
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S 0)

/-- The old finite normalized product is nonzero at a newly inserted support
point. -/
theorem entireFunction_finiteZeroDivisorProduct_nonzero_at_newSupport
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF S (a : ℂ) ≠ 0 := by
  have hprod :
      (∏ z in S,
        (1 - (a : ℂ) / (z : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
    exact
      Finset.prod_ne_zero_iff.mpr
        (fun z hz =>
          pow_ne_zero
            (entireFunctionZeroMultiplicity F hF (z : ℂ))
            (fun hfactor =>
              have ha_eq_z : (a : ℂ) = (z : ℂ) :=
                (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_factor_eq_zero_iff
                  F hF S hS0 z hz (a : ℂ)).1 hfactor
              have haz : a = z :=
                Subtype.ext ha_eq_z
              ha_not_mem (Eq.subst (motive := fun y : EntireFunctionZero F => y ∈ S) haz.symm hz)))
  exact
    Eq.subst
      (motive := fun x : ℂ => x ≠ 0)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_def
        F hF S (a : ℂ)).symm
      hprod

/-- Nonvanishing of the leading coefficient for the inserted normalized
finite product at the inserted point. -/
theorem entireFunction_insertedFiniteZeroDivisorProduct_localLeadingCoeff_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (ha0 : (a : ℂ) ≠ 0)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0) :
    ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S (a : ℂ) ≠ 0 := by
  have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero ha0
  have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr hinv_ne
  have hpow_ne :
      (-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) ≠ 0 :=
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
      hneg_ne
  have hprod_ne :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S (a : ℂ) ≠ 0 :=
    entireFunction_finiteZeroDivisorProduct_nonzero_at_newSupport
      F hF S a ha_not_mem hS0
  exact mul_ne_zero hpow_ne hprod_ne

/-- Algebraic cancellation for the local normalized centered-power quotient. -/
theorem complex_div_normalizedCenteredPower_eq_localModel_of_mul_eq
    {Qold P g a w : ℂ}
    {m : ℕ}
    (ha0 : a ≠ 0)
    (hw_ne : w ≠ a)
    (hP_ne : P ≠ 0)
    (hfactor : Qold * P = (w - a) ^ m * g) :
    Qold / ((1 - w / a) ^ m) =
      g / (((-a⁻¹) ^ m) * P) := by
  have hcenter_ne : w - a ≠ 0 :=
    sub_ne_zero.mpr hw_ne
  have hpow_ne : (w - a) ^ m ≠ 0 :=
    pow_ne_zero m hcenter_ne
  have hcoeff_ne : (-a⁻¹) ^ m ≠ 0 := by
    have hinv_ne : a⁻¹ ≠ 0 :=
      inv_ne_zero ha0
    have hneg_ne : -a⁻¹ ≠ 0 :=
      neg_ne_zero.mpr hinv_ne
    exact pow_ne_zero m hneg_ne
  have hnormFactor :
      (1 - w / a) ^ m = (-a⁻¹) ^ m * (w - a) ^ m :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
      ha0 m
  have hden_ne :
      ((-a⁻¹) ^ m) * (w - a) ^ m ≠ 0 :=
    mul_ne_zero hcoeff_ne hpow_ne
  have hcoeffP_ne :
      ((-a⁻¹) ^ m) * P ≠ 0 :=
    mul_ne_zero hcoeff_ne hP_ne
  have hQold_eq :
      Qold = ((w - a) ^ m * g) / P := by
    calc
      Qold = (Qold * P) / P := by
        exact (mul_div_cancel_right₀ Qold hP_ne).symm
      _ = ((w - a) ^ m * g) / P := by
        exact congrArg (fun x : ℂ => x / P) hfactor
  calc
    Qold / ((1 - w / a) ^ m) =
        Qold / (((-a⁻¹) ^ m) * (w - a) ^ m) := by
      exact congrArg (fun x : ℂ => Qold / x) hnormFactor
    _ = (((w - a) ^ m * g) / P) /
        (((-a⁻¹) ^ m) * (w - a) ^ m) := by
      exact congrArg (fun x : ℂ => x / (((-a⁻¹) ^ m) * (w - a) ^ m)) hQold_eq
    _ = (((w - a) ^ m * g) / (((-a⁻¹) ^ m) * (w - a) ^ m)) / P := by
      calc
        (((w - a) ^ m * g) / P) /
            (((-a⁻¹) ^ m) * (w - a) ^ m) =
          ((w - a) ^ m * g) /
            (P * (((-a⁻¹) ^ m) * (w - a) ^ m)) := by
          exact div_div ((w - a) ^ m * g) P (((-a⁻¹) ^ m) * (w - a) ^ m)
        _ =
          ((w - a) ^ m * g) /
            ((((-a⁻¹) ^ m) * (w - a) ^ m) * P) := by
          exact congrArg
            (fun x : ℂ => ((w - a) ^ m * g) / x)
            (mul_comm P (((-a⁻¹) ^ m) * (w - a) ^ m))
        _ =
          (((w - a) ^ m * g) / (((-a⁻¹) ^ m) * (w - a) ^ m)) / P := by
          exact (div_div ((w - a) ^ m * g) (((-a⁻¹) ^ m) * (w - a) ^ m) P).symm
    _ = (g / ((-a⁻¹) ^ m)) / P := by
      have hcancel :
          ((w - a) ^ m * g) / (((-a⁻¹) ^ m) * (w - a) ^ m) =
            g / ((-a⁻¹) ^ m) := by
        calc
          ((w - a) ^ m * g) / (((-a⁻¹) ^ m) * (w - a) ^ m) =
              ((w - a) ^ m * g) / ((w - a) ^ m * ((-a⁻¹) ^ m)) := by
            exact congrArg
              (fun x : ℂ => ((w - a) ^ m * g) / x)
              (mul_comm ((-a⁻¹) ^ m) ((w - a) ^ m))
          _ = g / ((-a⁻¹) ^ m) := by
            exact mul_div_mul_left g ((-a⁻¹) ^ m) hpow_ne
      exact congrArg (fun x : ℂ => x / P) hcancel
    _ = g / (((-a⁻¹) ^ m) * P) := by
      exact (div_mul_eq_div_div g ((-a⁻¹) ^ m) P).symm

/-- Local removable division by a normalized centered power.

This is the analytic-algebra core of inserting a Jensen normalized factor.  If
`Qold * P` has local centered-power factorization `(w-a)^m g(w)` and `P a ≠ 0`,
then `Qold / (1 - w/a)^m` has a removable singularity at `a`; its removable
value is `g a / ((-a⁻¹)^m * P a)`.  This is the standard removable-singularity
step, using
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m` on the punctured neighborhood. -/
theorem analyticAt_removable_div_normalizedCenteredPower
    (Qold P g : ℂ → ℂ)
    {a : ℂ}
    (m : ℕ)
    (ha0 : a ≠ 0)
    (hQold_an : AnalyticAt ℂ Qold a)
    (hP_an : AnalyticAt ℂ P a)
    (hP_ne : P a ≠ 0)
    (hg_an : AnalyticAt ℂ g a)
    (hfactor :
      ∀ᶠ w in 𝓝 a,
        Qold w * P w = (w - a) ^ m • g w) :
    ∃ Q : ℂ → ℂ,
      AnalyticAt ℂ Q a ∧
      Q =ᶠ[𝓝[≠] a]
        (fun w : ℂ => Qold w / ((1 - w / a) ^ m)) ∧
      Q a =
        g a / (((-a⁻¹) ^ m) * P a) := by
  let Q : ℂ → ℂ :=
    fun w : ℂ => g w / (((-a⁻¹) ^ m) * P w)
  have hcoeff_an :
      AnalyticAt ℂ (fun _w : ℂ => (-a⁻¹) ^ m) a :=
    analyticAt_const
  have hden_an :
      AnalyticAt ℂ (fun w : ℂ => ((-a⁻¹) ^ m) * P w) a :=
    hcoeff_an.mul hP_an
  have hcoeff_ne : (-a⁻¹) ^ m ≠ 0 := by
    have hinv_ne : a⁻¹ ≠ 0 :=
      inv_ne_zero ha0
    have hneg_ne : -a⁻¹ ≠ 0 :=
      neg_ne_zero.mpr hinv_ne
    exact pow_ne_zero m hneg_ne
  have hden_ne : ((-a⁻¹) ^ m) * P a ≠ 0 :=
    mul_ne_zero hcoeff_ne hP_ne
  have hQ_an : AnalyticAt ℂ Q a :=
    hg_an.div hden_an hden_ne
  have hP_eventually_ne :
      ∀ᶠ w in 𝓝 a, P w ≠ 0 :=
    hP_an.continuousAt.eventually_ne hP_ne
  have hpunctured :
      Q =ᶠ[𝓝[≠] a]
        (fun w : ℂ => Qold w / ((1 - w / a) ^ m)) := by
    have hlocal :
        ∀ᶠ w in 𝓝 a,
          Qold w * P w = (w - a) ^ m * g w :=
      hfactor.mono
        (fun w hw =>
          Eq.trans hw
            (show (w - a) ^ m • g w = (w - a) ^ m * g w by
              rfl))
    have hlocal_punctured :
        ∀ᶠ w in 𝓝[≠] a,
          Qold w * P w = (w - a) ^ m * g w :=
      hlocal.filter_mono nhdsWithin_le_nhds
    have hP_punctured :
        ∀ᶠ w in 𝓝[≠] a, P w ≠ 0 :=
      hP_eventually_ne.filter_mono nhdsWithin_le_nhds
    have hne_punctured :
        ∀ᶠ w in 𝓝[≠] a, w ∈ ({a}ᶜ : Set ℂ) :=
      self_mem_nhdsWithin
    exact
      (hne_punctured.and
        (hlocal_punctured.and hP_punctured)).mono
        (fun w hw =>
          have hw_ne : w ≠ a :=
            hw.1
          have hlocal_w : Qold w * P w = (w - a) ^ m * g w :=
            hw.2.1
          have hP_w_ne : P w ≠ 0 :=
            hw.2.2
          have hraw_eq :
              Qold w / ((1 - w / a) ^ m) =
                g w / (((-a⁻¹) ^ m) * P w) :=
            complex_div_normalizedCenteredPower_eq_localModel_of_mul_eq
              ha0 hw_ne hP_w_ne hlocal_w
          hraw_eq.symm)
  have hQ_value :
      Q a = g a / (((-a⁻¹) ^ m) * P a) :=
    rfl
  exact Exists.intro Q (And.intro hQ_an (And.intro hpunctured hQ_value))



end
end LFunctions
end Boundary
