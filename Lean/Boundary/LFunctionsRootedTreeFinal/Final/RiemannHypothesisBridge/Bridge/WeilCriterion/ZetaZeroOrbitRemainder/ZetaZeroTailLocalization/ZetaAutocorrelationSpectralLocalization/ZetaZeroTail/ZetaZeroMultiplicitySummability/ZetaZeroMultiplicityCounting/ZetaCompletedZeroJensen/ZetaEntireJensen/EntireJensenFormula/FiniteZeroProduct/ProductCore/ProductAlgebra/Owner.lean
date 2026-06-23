import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryZeroFactors.Owner

/-!
# Finite zero-product core

This owner layer was split from `FiniteZeroProduct.ProductCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

open scoped Topology

noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (s : Finset (EntireFunctionZero F))
    (w : ℂ) : ℂ :=
  ∏ z in s,
    (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)

/-- The parameterized finite zero-divisor product is definitionally the product
over the supplied support finset. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (s : Finset (EntireFunctionZero F))
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF s w =
      ∏ z in s,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
  rfl

/-- Finite normalized product after inserting a new support point. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
    (F : ℂ → ℂ)
    [DecidableEq (EntireFunctionZero F)]
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha : a ∉ S)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF (insert a S) w =
      (1 - w / (a : ℂ)) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) *
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w := by
  exact Finset.prod_insert ha

/-- Finite normalized product split into the factor at a member and the erased
product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_mul_erase
    (F : ℂ → ℂ)
    [DecidableEq (EntireFunctionZero F)]
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (w : ℂ) :
    (1 - w / (a : ℂ)) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) *
        (∏ z in S.erase a,
          (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF S w := by
  exact Finset.mul_prod_erase S
    (fun z : EntireFunctionZero F =>
      (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
    ha

/-- The closed-disk zero-factor product attached to all nonzero zeros in
`‖z‖ ≤ ρ`.

This is the product that should own removable quotient and zero-freeness on the
closed disk. Boundary zeros are included here; they contribute no radial-gap
term later. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
    F hF
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ)
    w

/-- The closed-disk product is the finite product over the closed-disk support
divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
      ∏ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
  rfl

noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
    F hF
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
      F hF hF0 ρ)
    w

/-- The finite zero-factor product is definitionally the product over the
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
      ∏ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
  rfl

/-- A normalized extracted linear factor vanishes exactly at its indexed zero
coordinate. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (w : ℂ) :
    1 - w / (z : ℂ) = 0 ↔ w = (z : ℂ) := by
  have hz_ne_zero : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz
  constructor
  · intro hfactor
    have hquotient_eq_one : w / (z : ℂ) = 1 :=
      (eq_of_sub_eq_zero hfactor).symm
    calc
      w = (w / (z : ℂ)) * (z : ℂ) := by
        exact (div_mul_cancel₀ w hz_ne_zero).symm
      _ = 1 * (z : ℂ) := by
        exact congrArg (fun x : ℂ => x * (z : ℂ)) hquotient_eq_one
      _ = (z : ℂ) := by
        exact one_mul (z : ℂ)
  · intro hw
    have hquotient_eq_one : w / (z : ℂ) = 1 := by
      calc
        w / (z : ℂ) = (z : ℂ) / (z : ℂ) := by
          exact congrArg (fun x : ℂ => x / (z : ℂ)) hw
        _ = 1 := by
          exact div_self hz_ne_zero
    calc
      1 - w / (z : ℂ) = 1 - 1 := by
        exact congrArg (fun x : ℂ => 1 - x) hquotient_eq_one
      _ = 0 := by
        exact sub_self (1 : ℂ)

/-- If one extracted support factor vanishes at `w`, then `w` is a zero of
the original entire function. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_zero_imp_function_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (w : ℂ)
    (hfactor : 1 - w / (z : ℂ) = 0) :
    F w = 0 := by
  have hw_eq_z : w = (z : ℂ) :=
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
      F hF hF0 ρ z hz w).1 hfactor
  exact Eq.subst
    (motive := fun x : ℂ => F x = 0)
    hw_eq_z.symm
    z.property

/-- A zero of the extracted finite product on the Jensen disk is a zero of
`F`. This is the product-zero half of the zero-set matching needed before the
removable quotient can be constructed. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_zero_imp_function_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ)
    (hproduct :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w = 0) :
    F w = 0 := by
  have hproduct_expanded :
      (∏ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) = 0 := by
    exact Eq.trans
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
        F hF hF0 ρ w).symm
      hproduct
  exact
    match Finset.prod_eq_zero_iff.mp hproduct_expanded with
    | Exists.intro z hz_tail =>
        match hz_tail with
        | And.intro hz hfactor_power =>
            have hfactor : 1 - w / (z : ℂ) = 0 :=
              pow_eq_zero hfactor_power
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_zero_imp_function_zero
              F hF hF0 ρ z hz w hfactor

/-- Off-support nonvanishing for the extracted finite zero-factor product.

Away from the support divisor, the finite product has no zero factors, so the
support product itself is nonzero. This is the easy analytic half of the
quotient zero-free argument. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_nonzero_of_not_mem_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ))) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w ≠ 0 := by
  intro hproduct
  have hproduct_expanded :
      (∏ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) = 0 := by
    exact Eq.trans
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
        F hF hF0 ρ w).symm
      hproduct
  exact
    match Finset.prod_eq_zero_iff.mp hproduct_expanded with
    | Exists.intro z hz_tail =>
        match hz_tail with
        | And.intro hz hfactor_power =>
            have hfactor : 1 - w / (z : ℂ) = 0 :=
              pow_eq_zero hfactor_power
            have hw_eq_z : w = (z : ℂ) :=
              (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
                F hF hF0 ρ z hz w).1 hfactor
            hw (Finset.mem_image.mpr (Exists.intro z (And.intro hz hw_eq_z.symm)))

/-- At a support point, every other extracted support factor is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_other_factor_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (a z : EntireFunctionZero F)
    (_ha :
      a ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (hz :
      z ∈
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).erase a) :
    (1 - (a : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ) ≠ 0 := by
  have hz_support :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    (Finset.mem_erase.1 hz).2
  have hza : z ≠ a :=
    (Finset.mem_erase.1 hz).1
  have hbase_ne : 1 - (a : ℂ) / (z : ℂ) ≠ 0 := by
    intro hbase
    have ha_eq_z : (a : ℂ) = (z : ℂ) :=
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
        F hF hF0 ρ z hz_support (a : ℂ)).1 hbase
    exact hza (Subtype.ext ha_eq_z.symm)
  exact
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (z : ℂ))
      hbase_ne

/-- At a support point, the product of all extracted factors except the indexed
one is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_otherFactors_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (a : EntireFunctionZero F)
    (ha :
      a ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    (∏ z in
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ).erase a,
      (1 - (a : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
  exact
    Finset.prod_ne_zero_iff.mpr
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_other_factor_nonzero_at_support
          F hF hF0 ρ a z ha hz)

/-- The leading constant of the extracted support divisor at a support point is
nonzero.

Locally at `a`, the indexed factor is
`1 - w / a = (-(a⁻¹)) * (w - a)`, and all other support factors are nonzero at
`a`.  This is the denominator used by the removable value of the quotient at
`a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_localLeadingCoeff_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (a : EntireFunctionZero F)
    (ha :
      a ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
        (∏ z in
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ).erase a,
          (1 - (a : ℂ) / (z : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
  have ha0 : (a : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ a ha
  have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero ha0
  have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr hinv_ne
  have hpow_ne :
      (-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) ≠ 0 :=
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
      hneg_ne
  have hother_ne :
      (∏ z in
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).erase a,
        (1 - (a : ℂ) / (z : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_otherFactors_nonzero_at_support
      F hF hF0 ρ a ha
  exact mul_ne_zero hpow_ne hother_ne

/-- The removable quotient value prescribed by the local support factorization
is nonzero at a support point.

The numerator is the local analytic unit `g a` from the multiplicity
factorization of `F`; the denominator is the nonzero leading coefficient of the
finite divisor product at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_supportPoint_removableValue_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (a : EntireFunctionZero F)
    (ha :
      a ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (g : ℂ → ℂ)
    (hg_ne : g (a : ℂ) ≠ 0) :
    g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ).erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) ≠ 0 := by
  have hden_ne :
      ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ).erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_localLeadingCoeff_nonzero_at_support
      F hF hF0 ρ a ha
  exact div_ne_zero hg_ne hden_ne

/-- A quotient whose support-point value is the local removable value is
nonzero at that support point. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_nonzero_at_support_of_removableValue
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (a : EntireFunctionZero F)
    (ha :
      a ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (g : ℂ → ℂ)
    (hg_ne : g (a : ℂ) ≠ 0)
    (hQ_value :
      Q (a : ℂ) =
        g (a : ℂ) /
          (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in
              (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
                F hF hF0 ρ).erase a,
              (1 - (a : ℂ) / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ)))) :
    Q (a : ℂ) ≠ 0 := by
  have hvalue_ne :
      g (a : ℂ) /
          (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            (∏ z in
              (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
                F hF hF0 ρ).erase a,
              (1 - (a : ℂ) / (z : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (z : ℂ))) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_supportPoint_removableValue_nonzero
      F hF hF0 ρ a ha g hg_ne
  exact fun hQ_zero => hvalue_ne (Eq.trans hQ_value.symm hQ_zero)

/-- A normalized extracted linear factor over an arbitrary nonzero finite
support vanishes exactly at its indexed zero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_factor_eq_zero_iff
    (F : ℂ → ℂ)
    (_hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (z : EntireFunctionZero F)
    (hz : z ∈ S)
    (w : ℂ) :
    1 - w / (z : ℂ) = 0 ↔ w = (z : ℂ) := by
  have hz_ne_zero : (z : ℂ) ≠ 0 :=
    hS0 z hz
  constructor
  · intro hfactor
    have hquotient_eq_one : w / (z : ℂ) = 1 :=
      (eq_of_sub_eq_zero hfactor).symm
    calc
      w = (w / (z : ℂ)) * (z : ℂ) := by
        exact (div_mul_cancel₀ w hz_ne_zero).symm
      _ = 1 * (z : ℂ) := by
        exact congrArg (fun x : ℂ => x * (z : ℂ)) hquotient_eq_one
      _ = (z : ℂ) := by
        exact one_mul (z : ℂ)
  · intro hw
    have hquotient_eq_one : w / (z : ℂ) = 1 := by
      calc
        w / (z : ℂ) = (z : ℂ) / (z : ℂ) := by
          exact congrArg (fun x : ℂ => x / (z : ℂ)) hw
        _ = 1 := by
          exact div_self hz_ne_zero
    calc
      1 - w / (z : ℂ) = 1 - 1 := by
        exact congrArg (fun x : ℂ => 1 - x) hquotient_eq_one
      _ = 0 := by
        exact sub_self (1 : ℂ)

/-- For an arbitrary nonzero finite support, every other extracted support
factor is nonzero at the indexed support point. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_other_factor_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (a z : EntireFunctionZero F)
    (_ha : a ∈ S)
    (hz : z ∈ S.erase a) :
    (1 - (a : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ) ≠ 0 := by
  have hz_support : z ∈ S :=
    (Finset.mem_erase.1 hz).2
  have hza : z ≠ a :=
    (Finset.mem_erase.1 hz).1
  have hbase_ne : 1 - (a : ℂ) / (z : ℂ) ≠ 0 := by
    intro hbase
    have ha_eq_z : (a : ℂ) = (z : ℂ) :=
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_factor_eq_zero_iff
        F hF S hS0 z hz_support (a : ℂ)).1 hbase
    exact hza (Subtype.ext ha_eq_z.symm)
  exact
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (z : ℂ))
      hbase_ne

/-- The product of all finite-support factors except the indexed one is
nonzero at that indexed support point. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_otherFactors_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (a : EntireFunctionZero F)
    (ha : a ∈ S) :
    (∏ z in S.erase a,
      (1 - (a : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
  exact
    Finset.prod_ne_zero_iff.mpr
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_other_factor_nonzero_at_support
          F hF S hS0 a z ha hz)

/-- The leading coefficient of an arbitrary extracted finite divisor at a
support point is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_localLeadingCoeff_nonzero_at_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (a : EntireFunctionZero F)
    (ha : a ∈ S) :
    ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
        (∏ z in S.erase a,
          (1 - (a : ℂ) / (z : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
  have ha0 : (a : ℂ) ≠ 0 :=
    hS0 a ha
  have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero ha0
  have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr hinv_ne
  have hpow_ne :
      (-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) ≠ 0 :=
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
      hneg_ne
  have hother_ne :
      (∏ z in S.erase a,
        (1 - (a : ℂ) / (z : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_otherFactors_nonzero_at_support
      F hF S hS0 a ha
  exact mul_ne_zero hpow_ne hother_ne

/-- The removable quotient value prescribed by a local factorization over an
arbitrary finite support is nonzero at a support point. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_supportPoint_removableValue_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (g : ℂ → ℂ)
    (hg_ne : g (a : ℂ) ≠ 0) :
    g (a : ℂ) /
        (((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))) ≠ 0 := by
  have hden_ne :
      ((-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)) *
          (∏ z in S.erase a,
            (1 - (a : ℂ) / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_localLeadingCoeff_nonzero_at_support
      F hF S hS0 a ha
  exact div_ne_zero hg_ne hden_ne


end
end LFunctions
end Boundary
