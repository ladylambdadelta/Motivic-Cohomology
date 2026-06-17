import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.Owner

/-!
# Finite zero-product core

This file is a sequential owner sublayer split from the finite zero-product
Jensen package.  It owns the finite-product algebra and local removable
division lemmas before global insertion gluing.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
    (ha :
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
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
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
    (ha : a ∈ S)
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

/-- Normalized finite-factor identity at a nonzero center.

The extracted Jensen factor `1 - w / a` is the local linear factor `w - a`
multiplied by the nonzero constant `-(a⁻¹)`.  This is the algebraic bridge
between the normalized product used globally and the local analytic order
factorization used at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
    {a w : ℂ}
    (ha0 : a ≠ 0)
    (m : ℕ) :
    (1 - w / a) ^ m = (-(a⁻¹)) ^ m * (w - a) ^ m := by
  have hbase : 1 - w / a = -(a⁻¹) * (w - a) := by
    calc
      1 - w / a = 1 - w * a⁻¹ := by
        exact congrArg (fun x : ℂ => 1 - x) (div_eq_mul_inv w a)
      _ = a * a⁻¹ - w * a⁻¹ := by
        exact congrArg (fun x : ℂ => x - w * a⁻¹) (mul_inv_cancel₀ ha0).symm
      _ = (a - w) * a⁻¹ := by
        exact (sub_mul a w a⁻¹).symm
      _ = (-(w - a)) * a⁻¹ := by
        exact congrArg (fun x : ℂ => x * a⁻¹) (neg_sub w a).symm
      _ = a⁻¹ * (-(w - a)) := by
        exact mul_comm (-(w - a)) a⁻¹
      _ = -(a⁻¹ * (w - a)) := by
        exact mul_neg a⁻¹ (w - a)
      _ = -(a⁻¹) * (w - a) := by
        exact (neg_mul a⁻¹ (w - a)).symm
  calc
    (1 - w / a) ^ m = (-(a⁻¹) * (w - a)) ^ m := by
      exact congrArg (fun x : ℂ => x ^ m) hbase
    _ = (-(a⁻¹)) ^ m * (w - a) ^ m := by
      exact mul_pow (-(a⁻¹)) (w - a) m

/-- Leading coefficient of the inserted finite product at the inserted zero,
after removing the local factor `(w-a)^m`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_insertedProduct_localLeadingCoeff
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha0 : (a : ℂ) ≠ 0)
    (w : ℂ) :
    (1 - w / (a : ℂ)) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) =
      (-(a : ℂ)⁻¹) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) *
        (w - (a : ℂ)) ^ entireFunctionZeroMultiplicity F hF (a : ℂ) :=
  entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
    ha0 (entireFunctionZeroMultiplicity F hF (a : ℂ))

/-- The punctured quotient after extracting the support divisor.

This is only the raw divided expression away from the support zeros; the
removable zero-free quotient is supplied later by the removable-extension
theorem. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  F w /
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
      F hF hF0 ρ w

/-- The closed-disk finite quotient is `F` divided by the closed-disk finite
zero-factor product.  This is the quotient surface that owns zero-freeness on
`‖w‖ ≤ ρ`. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  F w /
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
      F hF hF0 ρ w

/-- The finite quotient is definitionally `F` divided by the extracted finite
zero-factor product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w =
      F w /
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w := by
  rfl

/-- The closed-disk finite quotient is definitionally `F` divided by the
closed-disk product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorQuotient_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorQuotient
        F hF hF0 ρ w =
      F w /
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
          F hF hF0 ρ w := by
  rfl

/-- Each extracted nonzero zero factor is normalized to `1` at the origin. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin_factor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F) :
    (1 - (0 : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ) = 1 := by
  have hzero_div : (0 : ℂ) / (z : ℂ) = 0 :=
    zero_div (z : ℂ)
  have hbase :
      1 - (0 : ℂ) / (z : ℂ) = 1 := by
    calc
      1 - (0 : ℂ) / (z : ℂ) = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hzero_div
      _ = 1 := by
        exact sub_zero (1 : ℂ)
  exact
    Eq.trans
      (congrArg
        (fun x : ℂ => x ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
        hbase)
      (one_pow (entireFunctionZeroMultiplicity F hF (z : ℂ)))

/-- The finite zero-divisor product is normalized to `1` at the origin. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ 0 = 1 := by
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ 0 =
        ∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (1 - (0 : ℂ) / (z : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (z : ℂ) := by
      exact
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
          F hF hF0 ρ 0
    _ =
        ∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          1 := by
      exact
        Finset.prod_congr rfl
          (fun z _ =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin_factor
              F hF hF0 ρ z)
    _ = 1 := by
      exact Finset.prod_const_one

/-- With the current quotient definition `F / Product`, the quotient value at
the origin is exactly `F 0`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ 0 = F 0 := by
  have hproduct_origin :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ 0 = 1 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
      F hF hF0 ρ
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ 0 =
        F 0 /
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ 0 := by
      exact
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_def
          F hF hF0 ρ 0
    _ = F 0 / 1 := by
      exact congrArg (fun x : ℂ => F 0 / x) hproduct_origin
    _ = F 0 := by
      exact div_one (F 0)

/-- The current finite quotient origin normalization has positive sign:
`log ‖Q(0)‖ = log ‖F(0)‖`.  This is the canonical peeled origin calculation
from the product definition. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm_from_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖ := by
  exact
    congrArg Real.log
      (congrArg norm
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin
          F hF hF0 ρ))

/-- Away from zeros of the extracted finite product, the quotient definition
reconstructs `F` by direct cancellation. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ)
    (hproduct :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w ≠ 0) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w *
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
      F w := by
  let P : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
      F hF hF0 ρ w
  have hquotient :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
          F hF hF0 ρ w =
        F w / P :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_def
      F hF hF0 ρ w
  have hP_ne : P ≠ 0 :=
    hproduct
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w *
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
        (F w / P) * P := by
      exact congrArg (fun x : ℂ => x * P) hquotient
    _ = F w := by
      exact div_mul_cancel₀ (F w) hP_ne

/-- Off the support divisor, product nonvanishing and function nonvanishing
make the raw finite quotient nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_nonzero_of_not_mem_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ)))
    (hFw : F w ≠ 0) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w ≠ 0 := by
  have hproduct_ne :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_nonzero_of_not_mem_support
      F hF hF0 ρ w hw
  have hreconstruct :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
          F hF hF0 ρ w *
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w =
        F w :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_ne_zero
      F hF hF0 ρ w hproduct_ne
  exact fun hQ_zero =>
    hFw
      (Eq.trans hreconstruct.symm
        (Eq.trans
          (congrArg
            (fun x : ℂ =>
              x *
                entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                  F hF hF0 ρ w)
            hQ_zero)
          (zero_mul
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w))))

/-- If a closed-disk point is off the support and `F` is nonzero there, then
any quotient satisfying the exact finite-product factorization is nonzero
there. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_nonzero_of_not_mem_support
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (w : ℂ)
    (hwρ : ‖w‖ ≤ ρ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ)))
    (hFw : F w ≠ 0) :
    Q w ≠ 0 := by
  have hfactor_w :
      F w =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w :=
    hfactor w hwρ
  exact fun hQ_zero =>
    hFw
      (Eq.trans hfactor_w
        (Eq.trans
          (congrArg
            (fun x : ℂ =>
              x *
                entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                  F hF hF0 ρ w)
            hQ_zero)
          (zero_mul
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w))))

/-- Off the support divisor, a zero of a factored removable quotient forces a
zero of the original function. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_zero_imp_function_zero_of_not_mem_support
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (w : ℂ)
    (hwρ : ‖w‖ ≤ ρ)
    (hw :
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ)))
    (hQw : Q w = 0) :
    F w = 0 := by
  have hfactor_w :
      F w =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w :=
    hfactor w hwρ
  exact
    Eq.trans hfactor_w
      (Eq.trans
        (congrArg
          (fun x : ℂ =>
            x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
                F hF hF0 ρ w)
          hQw)
        (zero_mul
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w)))

/-- At a zero of the extracted finite product, quotient-product reconstruction
reduces to the matching zero of `F`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ)
    (hproduct :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w = 0)
    (hF_zero : F w = 0) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w *
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
      F w := by
  let Q : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
      F hF hF0 ρ w
  let P : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
      F hF hF0 ρ w
  have hP_zero : P = 0 :=
    hproduct
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w *
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
        Q * P := by
      rfl
    _ = Q * 0 := by
      exact congrArg (fun x : ℂ => Q * x) hP_zero
    _ = 0 := by
      exact mul_zero Q
    _ = F w := by
      exact hF_zero.symm

/-- Quotient-product reconstruction on Jensen's disk after the finite divisor
zero set has been matched with the zero set of `F`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_zero_imp_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hproduct_zero_imp_zero :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w = 0 →
        F w = 0) :
    ∀ w : ℂ,
      ‖w‖ ≤ ρ →
      F w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w := by
  intro w hw
  exact
    if hproduct :
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w = 0 then
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_zero
        F hF hF0 ρ w hproduct
        (hproduct_zero_imp_zero w hw hproduct)).symm
    else
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_ne_zero
        F hF hF0 ρ w hproduct).symm

/-- Local multiplicity factorization at a support zero of the finite Jensen
divisor.

This is the point where the analytic order of `F` at a support zero is
identified with the exponent used in the finite product.  The local
factorization is
`F w = (w - z)^m • g w`, with `g z ≠ 0`, and is the canonical local input for
removing the quotient singularity at `z`.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (z : ℂ) ∧
      g (z : ℂ) ≠ 0 ∧
      ∀ᶠ w in 𝓝 (z : ℂ),
        F w =
          (w - (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ) •
            g w := by
  have horder :
      (hF (z : ℂ)).order =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ENat) := by
    exact
      entireFunction_order_eq_multiplicity_of_nontrivial
        F hF ⟨0, hF0⟩ (z : ℂ)
  exact
    entireFunction_localMultiplicityFactorization
      F hF (z : ℂ) horder

/-- Local multiplicity factorization at a closed-disk support zero.

This is the local input for the closed-disk removable quotient. Boundary zeros
are included in this support because zero-freeness is asserted on the closed
disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (z : ℂ) ∧
      g (z : ℂ) ≠ 0 ∧
      ∀ᶠ w in 𝓝 (z : ℂ),
        F w =
          (w - (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ) •
            g w := by
  have horder :
      (hF (z : ℂ)).order =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ENat) := by
    exact
      entireFunction_order_eq_multiplicity_of_nontrivial
        F hF ⟨0, hF0⟩ (z : ℂ)
  exact
    entireFunction_localMultiplicityFactorization
      F hF (z : ℂ) horder

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
