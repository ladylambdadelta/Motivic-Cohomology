import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.Owner

/-!
# Finite zero-product quotient and removable factorization

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The finite zero-factor product attached to the radial-gap support divisor.

This is the product side of Jensen's finite divisor assembly: each zero inside
the Jensen circle contributes the linear factor
`1 - w / z`, repeated with analytic multiplicity. -/
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
  rcases Finset.prod_eq_zero_iff.mp hproduct_expanded with
    ⟨z, hz, hfactor_power⟩
  have hfactor : 1 - w / (z : ℂ) = 0 :=
    pow_eq_zero hfactor_power
  exact
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
  rcases Finset.prod_eq_zero_iff.mp hproduct_expanded with ⟨z, hz, hfactor_power⟩
  have hfactor : 1 - w / (z : ℂ) = 0 :=
    pow_eq_zero hfactor_power
  have hw_eq_z : w = (z : ℂ) :=
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
      F hF hF0 ρ z hz w).1 hfactor
  exact hw ⟨z, hz, hw_eq_z⟩

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
    exact hza (Subtype.ext ha_eq_z)
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
    exact hza (Subtype.ext ha_eq_z)
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
      exact
        Finset.prod_const_one
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ)

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
  by_cases hproduct :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w = 0
  · exact
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_zero
        F hF hF0 ρ w hproduct
        (hproduct_zero_imp_zero w hw hproduct)).symm
  · exact
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
  refine ⟨F, ?_, ?_, rfl⟩
  · intro w _hw
    exact hF w
  · intro w _hw
    calc
      F w = F w * 1 := by
        exact (mul_one (F w)).symm
      _ =
          F w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF ∅ w := by
        rfl

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

/-- Inserting one normalized nonzero factor does not change the finite product
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
        exact (mul_div_cancel₀ Qold hP_ne).symm
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
      exact div_div_eq_div_div_swap ((w - a) ^ m * g) P (((-a⁻¹) ^ m) * (w - a) ^ m)
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
          Eq.trans hw (smul_eq_mul ((w - a) ^ m) (g w)))
    have hlocal_punctured :
        ∀ᶠ w in 𝓝[≠] a,
          Qold w * P w = (w - a) ^ m * g w :=
      hlocal.filter_mono nhdsWithin_le_nhds
    have hP_punctured :
        ∀ᶠ w in 𝓝[≠] a, P w ≠ 0 :=
      hP_eventually_ne.filter_mono nhdsWithin_le_nhds
    exact
      (self_mem_nhdsWithin.and_eventually
        (hlocal_punctured.and_eventually hP_punctured)).mono
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
  refine ⟨Q, hQ_an, hpunctured, ?_⟩
  rfl

/-- Global gluing after local removable division at the inserted support point.

The local theorem supplies an analytic filled quotient near `a`, eventually
equal on the punctured neighborhood to `Qold / (1 - w/a)^m`.  This theorem
glues that local model with the ordinary quotient away from `a`, proves
analyticity on the closed disk, and transports the finite-product identity via
`Product(insert a S) = (1 - w/a)^m * Product(S)`. -/
theorem entireFunction_insertNormalizedFactor_glue_localDivision
    (F Qold g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w)
    (hQold_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Qold w)
    (hQold_factor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Qold w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (hQold_zero : Qold 0 = F 0)
    (hlocal_div :
      ∃ Qloc : ℂ → ℂ,
        AnalyticAt ℂ Qloc (a : ℂ) ∧
        Qloc =ᶠ[𝓝[≠] (a : ℂ)]
          (fun w : ℂ =>
            Qold w /
              ((1 - w / (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ))) ∧
        Qloc (a : ℂ) =
          g (a : ℂ) /
            (((-(a : ℂ)⁻¹) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ)) *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S (a : ℂ))) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  -- Exact global gluing theorem: define `Q` by the local filled quotient at
  -- `a` and by `Qold / (1-w/a)^m` elsewhere; use `hlocal_div` for analyticity
  -- at `a`, ordinary analytic division away from `a`, and product insertion
  -- for the closed-disk factor identity and origin normalization.
  sorry

/-- Explicit old-quotient/local-unit form of one-step normalized removable
division.

This is the true analytic construction behind the finite insertion step.  The
old quotient `Qold` is divided by the inserted normalized factor away from
`a`; the local Taylor unit `g` supplies the filled value at `a` after the
identity
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m`.  The resulting quotient is analytic on the
closed disk and preserves the origin normalization because the inserted factor
has value `1` at `0`. -/
theorem entireFunction_insertNormalizedFactor_removableQuotient_from_oldQuotient_and_localUnit
    (F Qold g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hg_an : AnalyticAt ℂ g (a : ℂ))
    (hg_ne : g (a : ℂ) ≠ 0)
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w)
    (hQold_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Qold w)
    (hQold_factor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Qold w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (hQold_zero : Qold 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  -- Broad closed-disk insertion splits into two cases:
  -- if `a` lies in the disk, instantiate
  -- `analyticAt_removable_div_normalizedCenteredPower` at `a` and glue the
  -- local filled quotient; if not, ordinary division by the nonvanishing
  -- normalized factor is analytic at every disk point.  The current theorem
  -- intentionally has no `‖a‖ ≤ ρ` hypothesis, so this global localization
  -- step is the exact remaining gluing theorem.
  sorry

/-- Insert one normalized zero factor into an analytic finite factorization.

This is the canonical local analytic-division construction used by the
single-insert step.  Given a quotient for the finite product over `S`, and a
Taylor-order factorization of `F` at the new nonzero support point `a`, it
constructs the quotient for `insert a S`.  The removable value at `a` is forced
by the local unit and the normalized-factor identity
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m`; away from `a`, the quotient is the old
quotient divided by the inserted normalized factor. -/
theorem entireFunction_insertNormalizedFactor_removableQuotient_of_localTaylorFactorization
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  rcases hlocal_a with
  | intro g hg =>
      rcases hS with
      | intro Qold hQold =>
          exact
            entireFunction_insertNormalizedFactor_removableQuotient_from_oldQuotient_and_localUnit
              F Qold g hF ρ hρ S a ha_not_mem hS0 ha0
              hg.1
              hg.2.1
              hg.2.2
              hQold.1
              hQold.2.1
              hQold.2.2

/-- Single-insert analytic division by a normalized finite zero factor.

This is the canonical removable-quotient theorem for one new nonzero support
point.  The proof is local analytic algebra: use the Taylor-order factorization
at `a`, rewrite `(1 - w/a)^m` as `(-a⁻¹)^m (w-a)^m`, divide the old quotient
by the normalized inserted factor away from `a`, and fill the removable value
at `a` with the local Taylor unit divided by the nonzero leading coefficient. -/
theorem entireFunction_insertNormalizedFactor_removableQuotient_localAnalyticDivision
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_insertNormalizedFactor_removableQuotient_of_localTaylorFactorization
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Canonical removable quotient after inserting one normalized zero factor.

This is the true single-insert removable construction.  Starting from a
quotient for `S`, it divides by the normalized factor `(1 - w/a)^m`; near `a`
the local Taylor factorization of `F` and the algebraic identity
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m` provide the removable value. -/
theorem entireFunction_insertNormalizedFactor_removableQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_insertNormalizedFactor_removableQuotient_localAnalyticDivision
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Single-zero normalized-factor removable quotient.

This is the local removable-singularity construction for inserting one
nonzero zero into a finite normalized divisor.  It is the analytic step:
combine the Taylor-order factorization at `a` with
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m`, divide by the old finite divisor, and fill
the removable value at `a`. -/
theorem entireFunction_singleZeroNormalizedFactor_removableQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_insertNormalizedFactor_removableQuotient
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Single-zero removable quotient after normalized factor extraction.

This is the local analytic theorem behind one insertion in the finite divisor.
The proof combines the order factorization
`F(w) = (w-a)^m g(w)` with
`(1 - w/a)^m = (-(a⁻¹))^m (w-a)^m`, then fills the removable value at `a`.
All remaining already-extracted factors are analytic and nonzero at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_singleZeroNormalizedFactor_removableQuotient_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_singleZeroNormalizedFactor_removableQuotient
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Single insertion removable quotient theorem for a finite normalized
divisor.

This is the canonical local-to-global step in finite divisor extraction.  The
local input is the exact order factorization at the inserted zero `a`; the
already extracted quotient for `S` is patched through the removable singularity
created by dividing by `(1 - w / a)^m`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_single_insert_removable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_singleZeroNormalizedFactor_removableQuotient_ownerRoot
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- One-step finite divisor extraction.

Assuming a removable quotient has already been constructed for `S`, this
theorem extracts one further nonzero zero `a ∉ S`.  The proof is the local
single-zero removable quotient theorem applied to the current quotient times
the remaining product, using the local multiplicity factor of `F` at `a`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_insert_step_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hlocal_a :
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g (a : ℂ) ∧
        g (a : ℂ) ≠ 0 ∧
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w =
            (w - (a : ℂ)) ^
                entireFunctionZeroMultiplicity F hF (a : ℂ) •
              g w)
    (hS :
      ∃ Q : ℂ → ℂ,
        (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
        (∀ w : ℂ,
          ‖w‖ ≤ ρ →
          F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF S w) ∧
        Q 0 = F 0) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_single_insert_removable_ownerRoot
      F hF ρ hρ S a ha_not_mem hS0 ha0 hlocal_a hS

/-- Finset-induction construction of the finite removable quotient.

The induction step removes one indexed nonzero zero using the local factor
supplied by `AnalyticAt.order_eq_nat_iff`; the remaining finite product is
analytic and nonzero at that center, so the single-zero removable value is the
local Taylor unit divided by the remaining leading coefficient. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_induction_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w) ∧
      Q 0 = F 0 := by
  revert hS0 hlocal
  refine Finset.induction_on S ?base ?step
  · intro _hS0 _hlocal
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_empty
        F hF ρ hρ
  · intro a S ha_not_mem ih hS0 hlocal
    have hS0_tail :
        ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
      intro z hz
      exact hS0 z (Finset.mem_insert.2 (Or.inr hz))
    have ha0 : (a : ℂ) ≠ 0 :=
      hS0 a (Finset.mem_insert.2 (Or.inl rfl))
    have hlocal_a :
        ∃ g : ℂ → ℂ,
          AnalyticAt ℂ g (a : ℂ) ∧
          g (a : ℂ) ≠ 0 ∧
          ∀ᶠ w in 𝓝 (a : ℂ),
            F w =
              (w - (a : ℂ)) ^
                  entireFunctionZeroMultiplicity F hF (a : ℂ) •
                g w :=
      hlocal a (Finset.mem_insert.2 (Or.inl rfl))
    have hlocal_tail :
        ∀ z : EntireFunctionZero F,
          z ∈ S →
            ∃ g : ℂ → ℂ,
              AnalyticAt ℂ g (z : ℂ) ∧
              g (z : ℂ) ≠ 0 ∧
              ∀ᶠ w in 𝓝 (z : ℂ),
                F w =
                  (w - (z : ℂ)) ^
                      entireFunctionZeroMultiplicity F hF (z : ℂ) •
                    g w := by
      intro z hz
      exact hlocal z (Finset.mem_insert.2 (Or.inr hz))
    have hS :
        ∃ Q : ℂ → ℂ,
          (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
          (∀ w : ℂ,
            ‖w‖ ≤ ρ →
            F w =
              Q w *
                entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                  F hF S w) ∧
          Q 0 = F 0 :=
      ih hS0_tail hlocal_tail
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_insert_step_ownerRoot
        F hF ρ hρ S a ha_not_mem hS0_tail ha0 hlocal_a hS

/-- Parameterized finite removable quotient gluing across a finite set of
nonzero zeros.

This is the single owner-level removable-singularity construction used by both
the closed-disk support product and the radial-gap product.  The supplied
finite set determines the extracted divisor; any zeros not in `S` remain zeros
of the quotient rather than singularities. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_induction_ownerRoot
      F hF ρ hρ S hS0 hlocal

/-- Finset-level removable quotient gluing across the closed-disk support.

This is the closed-disk analogue of the radial support gluing root. It is the
correct owner for a quotient that is zero-free on `‖w‖ ≤ ρ`, because it removes
boundary zeros as well as strictly interior zeros. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  have hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
    intro z hz
    have hz_closed :
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ :=
      Eq.subst (motive := fun T : Finset (EntireFunctionZero F) => z ∈ T)
        hS hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ z hz_closed
  obtain ⟨Q, hQ_an, hfactor, hQ0⟩ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF ρ hρ S hS0 hlocal
  refine ⟨Q, hQ_an, ?_, hQ0⟩
  intro w hwρ
  have hprod :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
          F hF hF0 ρ w := by
    unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
    exact
      congrArg
        (fun T : Finset (EntireFunctionZero F) =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF T w)
        hS
  calc
    F w =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF S w :=
      hfactor w hwρ
    _ =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ w := by
      exact congrArg (fun x : ℂ => Q w * x) hprod

/-- Closed-disk removable quotient after extracting all nonzero zeros in
`‖w‖ ≤ ρ`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_extension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ
  have hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    rfl
  have hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w := by
    intro z hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
        F hF hF0 ρ z hz
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF hF0 ρ hρ S hS hlocal

/-- Finset-level removable quotient gluing across the extracted Jensen support.

This is the owner lemma for the finite gluing step: every support point carries
the local multiplicity factor of `F`, and the support product carries the same
power there.  The resulting local quotients patch with the raw quotient on the
complement of the support and give one analytic quotient on the closed disk.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (S : Finset (EntireFunctionZero F))
    (hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)
    (hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  have hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0 := by
    intro z hz
    have hz_radial :
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ :=
      Eq.subst (motive := fun T : Finset (EntireFunctionZero F) => z ∈ T)
        hS hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ z hz_radial
  obtain ⟨Q, hQ_an, hfactor, hQ0⟩ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteSupportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF ρ hρ S hS0 hlocal
  refine ⟨Q, hQ_an, ?_, hQ0⟩
  intro w hwρ
  have hprod :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w := by
    unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
    exact
      congrArg
        (fun T : Finset (EntireFunctionZero F) =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF T w)
        hS
  calc
    F w =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF S w :=
      hfactor w hwρ
    _ =
        Q w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w := by
      exact congrArg (fun x : ℂ => Q w * x) hprod

/-- Canonical finite removable quotient after extracting exactly the Jensen
support divisor, stated as a thin wrapper over the Finset gluing owner lemma. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_from_glue_finset_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
      F hF hF0 ρ
  have hS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    rfl
  have hlocal :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          ∃ g : ℂ → ℂ,
            AnalyticAt ℂ g (z : ℂ) ∧
            g (z : ℂ) ≠ 0 ∧
            ∀ᶠ w in 𝓝 (z : ℂ),
              F w =
                (w - (z : ℂ)) ^
                    entireFunctionZeroMultiplicity F hF (z : ℂ) •
                  g w := by
    intro z hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
        F hF hF0 ρ z hz
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_glue_finset_ownerRoot
      F hF hF0 ρ hρ S hS hlocal

/-- Canonical finite removable quotient after extracting the Jensen support
divisor.

The construction removes the finite set of quotient singularities by the local
Taylor factors at the support zeros and agrees with the raw quotient away from
that finite support. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_from_glue_finset_ownerRoot
      F hF hF0 ρ hρ

/-- Away from the finite support, the raw quotient is the required local
quotient and reconstructs `F` after multiplication by the finite divisor
product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_puncturedAgreement_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    ∀ w : ℂ,
      w ∉
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ)) →
      F w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w := by
  intro w hw
  have hproduct_ne :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w ≠ 0 := by
    have hproduct_expanded :
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w =
          ∏ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
        F hF hF0 ρ w
    have hfinite_product_ne :
        (∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) ≠ 0 := by
      exact
        Finset.prod_ne_zero_iff.mpr
          (fun z hz =>
            pow_ne_zero
              (entireFunctionZeroMultiplicity F hF (z : ℂ))
              (fun hfactor =>
                hw
                  ⟨z, hz,
                    ((entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_factor_eq_zero_iff
                      F hF hF0 ρ z hz w).1 hfactor).symm⟩))
    exact
      Eq.subst
        (motive := fun x : ℂ => x ≠ 0)
        hproduct_expanded.symm
        hfinite_product_ne
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_mul_product_of_product_ne_zero
      F hF hF0 ρ w hproduct_ne).symm

/-- Removable extension across the finite Jensen support.

The local Taylor factors at the support zeros cancel the corresponding powers
in the finite product, while the raw quotient gives the construction away from
the support.  The output is an entire quotient on the closed disk together with
the exact product factorization there. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_extension_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w) ∧
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      Q 0 = F 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_finiteExtension_ownerRoot
      F hF hF0 ρ hρ

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
  by_cases hw :
      w ∈
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ))
  · rcases Finset.mem_image.1 hw with ⟨z, hz, hzw⟩
    exact Eq.subst (motive := fun x : ℂ => Q x ≠ 0) hzw.symm (hon z hz)
  · exact hoff w hwρ hw

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
  by_cases hw0 : w = 0
  · exact hF0 (Eq.subst (motive := fun x : ℂ => F x = 0) hw0 hFw)
  · have hz_mem :
        (⟨w, hFw⟩ : EntireFunctionZero F) ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_of_zero_ne_zero_norm_le
        F hF hF0 ρ hFw hw0 hwρ
    exact hw ⟨⟨w, hFw⟩, hz_mem, rfl⟩

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
      exact hFw_ne
    (Eq.trans hfactor_w
      (Eq.trans
        (congrArg
          (fun x : ℂ =>
            x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                F hF hF0 ρ w)
          hQw)
        (zero_mul
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ w))))

/-- Analytic germs that agree on a punctured neighborhood have the same value
at the puncture.

This is the reusable removable-value endpoint: after the factor-cancellation
argument has produced equality away from the center, continuity of the two
analytic germs identifies their filled-in values. -/
theorem analyticAt_eq_at_of_eventuallyEq_punctured
    {f g : ℂ → ℂ}
    {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a)
    (hfg : f =ᶠ[𝓝[≠] a] g) :
    f a = g a := by
  have hf_tendsto_nhds :
      Filter.Tendsto f (𝓝 a) (𝓝 (f a)) :=
    hf.continuousAt.tendsto
  have hg_tendsto_nhds :
      Filter.Tendsto g (𝓝 a) (𝓝 (g a)) :=
    hg.continuousAt.tendsto
  have hf_tendsto_punctured :
      Filter.Tendsto f (𝓝[≠] a) (𝓝 (f a)) :=
    hf_tendsto_nhds.mono_left nhdsWithin_le_nhds
  have hg_tendsto_punctured :
      Filter.Tendsto g (𝓝[≠] a) (𝓝 (g a)) :=
    hg_tendsto_nhds.mono_left nhdsWithin_le_nhds
  have hf_tendsto_g_value :
      Filter.Tendsto f (𝓝[≠] a) (𝓝 (g a)) :=
    Filter.Tendsto.congr' hfg hg_tendsto_punctured
  exact
    tendsto_nhds_unique hf_tendsto_punctured hf_tendsto_g_value

/-- Analytic identity theorem in local punctured-germ form.

If two analytic germs agree frequently in the punctured neighborhood of the
center, then they agree eventually in the punctured neighborhood. -/
theorem analyticAt_eventuallyEq_punctured_of_frequentlyEq_punctured
    {f g : ℂ → ℂ}
    {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a)
    (hfg : ∃ᶠ w in 𝓝[≠] a, f w = g w) :
    f =ᶠ[𝓝[≠] a] g := by
  have hfg_nhds :
      ∀ᶠ w in 𝓝 a, f w = g w :=
    (AnalyticAt.frequently_eq_iff_eventually_eq hf hg).1 hfg
  exact hfg_nhds.filter_mono nhdsWithin_le_nhds

/-- Every nonempty real open interval contains a point outside a prescribed
finite set. -/
theorem real_Ioo_avoidFinite_nonempty
    (T : Finset ℝ)
    {u v : ℝ}
    (huv : u < v) :
    ∃ t : ℝ,
      t ∈ Set.Ioo u v ∧
        ∀ r : ℝ, r ∈ T → t ≠ r := by
  have hcount :
      Set.Countable ((T : Set ℝ)) :=
    T.finite_toSet.countable
  have hdense :
      Dense (((T : Set ℝ))ᶜ) :=
    hcount.dense_compl
  have hnonempty :
      (Set.Ioo u v).Nonempty :=
    Set.nonempty_Ioo.2 huv
  rcases hdense.inter_open_nonempty (Set.Ioo u v) isOpen_Ioo hnonempty with
  | intro t ht =>
      exact
        ⟨t, ht.2,
          fun r hr htr =>
            ht.1
              (Eq.subst
                (motive := fun x : ℝ => x ∈ (T : Set ℝ))
                htr
                hr)⟩

/-- One-sided real finite avoidance near `1`.

This is the real topology core used by radial finite avoidance: numbers
`t < 1`, arbitrarily close to `1`, can be chosen outside a prescribed finite
set. -/
theorem real_leftNhds_one_avoidFinite_frequently
    (T : Finset ℝ) :
    ∃ᶠ t in 𝓝[<] (1 : ℝ),
      0 ≤ t ∧
      t < 1 ∧
        ∀ r : ℝ, r ∈ T → t ≠ r := by
  refine Filter.frequently_iff.2 ?_
  intro U hU
  rcases
    (mem_nhdsWithin_Iio_iff_exists_Ioo_subset (a := (1 : ℝ)) (s := U)).1 hU with
  | intro l hl =>
      have hl_lt_one : l < 1 :=
        hl.1
      have hmax_lt_one : max l 0 < 1 :=
        max_lt hl_lt_one zero_lt_one
      rcases real_Ioo_avoidFinite_nonempty T hmax_lt_one with
      | intro t ht =>
          have ht_mem_U : t ∈ U :=
            hl.2 t
              ⟨lt_of_le_of_lt (le_max_left l 0) ht.1.1, ht.1.2⟩
          have ht_nonneg : 0 ≤ t :=
            (le_max_right l 0).trans ht.1.1.le
          exact
            ⟨t, ht_mem_U, ht_nonneg, ht.1.2, ht.2⟩


/-- Radial finite-avoidance inside a closed disk.

For a nonzero point `a` in `closedBall 0 ρ`, the inward radial points
`t • a`, with `t < 1` and `t → 1`, stay in the closed disk, are punctured at
`a`, and avoid any prescribed finite set frequently. -/
theorem complex_closedBall_radial_punctured_avoidFinite_frequently
    (a : ℂ)
    (ρ : ℝ)
    (T : Finset ℂ)
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ ≤ ρ) :
    ∃ᶠ w in 𝓝[≠] a,
      w ≠ a ∧
      ‖w‖ ≤ ρ ∧
        ∀ z : ℂ, z ∈ T → w ≠ z := by
  let badScalars : Finset ℝ :=
    T.image (fun z : ℂ => (z / a).re)
  have hreal :
      ∃ᶠ t in 𝓝[<] (1 : ℝ),
        0 ≤ t ∧
        t < 1 ∧
          ∀ r : ℝ, r ∈ badScalars → t ≠ r :=
    real_leftNhds_one_avoidFinite_frequently badScalars
  have htendsto_nhds :
      Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] (1 : ℝ)) (𝓝 a) := by
    have hcont :
        ContinuousAt (fun t : ℝ => (t : ℂ) * a) (1 : ℝ) :=
      (Complex.continuous_ofReal.continuousAt).mul continuousAt_const
    have hvalue :
        (fun t : ℝ => (t : ℂ) * a) 1 = a := by
      exact one_mul a
    exact hvalue ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds
  have heventually_punctured :
      ∀ᶠ t in 𝓝[<] (1 : ℝ), (t : ℂ) * a ∈ ({a}ᶜ : Set ℂ) := by
    exact
      (eventually_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Iio (1 : ℝ)).mono
        (fun t ht h_eq =>
          have h_eq_one_mul : (t : ℂ) * a = 1 * a :=
            h_eq.trans (one_mul a).symm
          have hscalar_complex : (t : ℂ) = 1 :=
            mul_right_cancel₀ ha0 h_eq_one_mul
          have ht_eq_one : t = 1 :=
            Complex.ofReal_injective hscalar_complex
          have hnot : ¬ t = 1 :=
            ne_of_lt ht
          hnot ht_eq_one)
  have htendsto :
      Tendsto (fun t : ℝ => (t : ℂ) * a) (𝓝[<] (1 : ℝ)) (𝓝[≠] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun t : ℝ => (t : ℂ) * a)
      htendsto_nhds
      heventually_punctured
  exact
    htendsto.frequently
      (hreal.mono
        (fun t ht =>
          have ht_nonneg : 0 ≤ t :=
            ht.1
          have ht_lt_one : t < 1 :=
            ht.2.1
          have ht_abs_le_one : |t| ≤ 1 :=
            abs_le.2 ⟨ht_nonneg, ht_lt_one.le⟩
          have hnorm_scalar : ‖(t : ℂ)‖ = |t| := by
            exact
              (complex_norm_ofReal_of_nonnegative ht_nonneg).trans
                (abs_of_nonneg ht_nonneg).symm
          have hnorm_le_a : ‖(t : ℂ) * a‖ ≤ ‖a‖ := by
            calc
              ‖(t : ℂ) * a‖ = ‖(t : ℂ)‖ * ‖a‖ := by
                exact norm_mul (t : ℂ) a
              _ = |t| * ‖a‖ := by
                exact congrArg (fun r : ℝ => r * ‖a‖) hnorm_scalar
              _ ≤ 1 * ‖a‖ :=
                mul_le_mul_of_nonneg_right ht_abs_le_one (norm_nonneg a)
              _ = ‖a‖ := one_mul ‖a‖
          have hnorm_le_ρ : ‖(t : ℂ) * a‖ ≤ ρ :=
            hnorm_le_a.trans haρ
          ⟨fun h_eq =>
              have h_eq_one_mul : (t : ℂ) * a = 1 * a :=
                h_eq.trans (one_mul a).symm
              have hscalar_complex : (t : ℂ) = 1 :=
                mul_right_cancel₀ ha0 h_eq_one_mul
              have ht_eq_one : t = 1 :=
                Complex.ofReal_injective hscalar_complex
              have hnot : ¬ t = 1 :=
                ne_of_lt ht_lt_one
              hnot ht_eq_one,
            hnorm_le_ρ,
            fun z hz h_eq =>
              have hz_bad :
                  (z / a).re ∈ badScalars :=
                Finset.mem_image.2 ⟨z, hz, rfl⟩
              have hz_div_eq : z / a = (t : ℂ) := by
                calc
                  z / a = ((t : ℂ) * a) / a := by
                    exact congrArg (fun q : ℂ => q / a) h_eq.symm
                  _ = (t : ℂ) := mul_div_cancel_right₀ (t : ℂ) ha0
              have ht_re_eq : t = (z / a).re := by
                exact (congrArg Complex.re hz_div_eq).symm
              ht.2.2 (z / a).re hz_bad ht_re_eq⟩))

/-- Good punctured closed-disk points near a nonzero support point.

This is the topology input for finite normalized-factor cancellation: near a
nonzero point `a` with `‖a‖ ≤ ρ`, points of the closed disk that avoid `a` and
the finitely many other support centers occur frequently in the punctured
neighborhood of `a`. -/
theorem entireFunction_closedDisk_puncturedGoodPoints_frequently
    (F : ℂ → ℂ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha : a ∈ S)
    (ha0 : (a : ℂ) ≠ 0)
    (ρ : ℝ)
    (haρ : ‖(a : ℂ)‖ ≤ ρ) :
    ∃ᶠ w in 𝓝[≠] (a : ℂ),
      w ≠ (a : ℂ) ∧
      ‖w‖ ≤ ρ ∧
        ∀ z : EntireFunctionZero F,
          z ∈ S.erase a →
            w ≠ (z : ℂ) := by
  have hradial :
      ∃ᶠ w in 𝓝[≠] (a : ℂ),
        w ≠ (a : ℂ) ∧
        ‖w‖ ≤ ρ ∧
          ∀ z : ℂ,
            z ∈ (S.erase a).image (fun z : EntireFunctionZero F => (z : ℂ)) →
              w ≠ z :=
    complex_closedBall_radial_punctured_avoidFinite_frequently
      (a : ℂ)
      ρ
      ((S.erase a).image (fun z : EntireFunctionZero F => (z : ℂ)))
      ha0
      haρ
  exact
    hradial.mono
      (fun w hw =>
        ⟨hw.1, hw.2.1,
          fun z hz =>
            hw.2.2
              (z : ℂ)
              (Finset.mem_image.2 ⟨z, hz, rfl⟩)⟩)


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
                  z (Finset.mem_of_mem_erase hz) w).1 hfactor).symm))
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
        exact Eq.trans (mul_assoc C P E).symm (mul_left_comm C P E)
  have hg_mul : F w = P * g w := by
    exact Eq.trans hg_factor_w (smul_eq_mul P (g w))
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
      exact (mul_div_cancel₀ (Q w) hD_ne).symm
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
    (hgood.and_eventually hlocal_punctured).mono
      (fun w hw =>
        entireFunction_finiteNormalizedFactorization_puncturedCancellation_pointwise
          F Q hF ρ S hS0 hfactor a ha ha0 g
          hw.1.2.1
          hw.1.1
          hw.1.2.2
          hw.2)

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
  obtain ⟨g, hg_an, hg_ne, hg_factor⟩ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_localMultiplicityFactor_ownerRoot
      F hF hF0 ρ z hz
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
      F hF S hS0 z hz g hg_ne
  exact fun hQ_zero => hvalue_ne (Eq.trans hQ_value.symm hQ_zero)

/-- Maximal-multiplicity zero-freeness for the quotient after finite removable
gluing.

This owner lemma is the local multiplicity sink: after the support product has
removed exactly the analytic order of `F` at every support zero, the glued
quotient has order zero throughout the closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_from_maximalMultiplicity_ownerRoot
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
              F hF hF0 ρ w) :
    ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  intro w hwρ
  by_cases hw :
      w ∈
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ).image
          (fun z : EntireFunctionZero F => (z : ℂ))
  · rcases Finset.mem_image.1 hw with ⟨z, hz, hzw⟩
    exact
      Eq.subst (motive := fun x : ℂ => Q x ≠ 0) hzw.symm
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_at_support_from_maximalMultiplicity_ownerRoot
          F Q hF hF0 ρ hQ_an hfactor z hz)
  · exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_of_not_mem_support
        F Q hF hF0 ρ hfactor hwρ hw

/-- Maximal-multiplicity zero-freeness for the removable quotient.

If the quotient vanished at a point of the closed disk, then the product
factorization would force `F` to vanish there to order strictly larger than the
exponent extracted in the finite product.  At a support point this contradicts
the local maximality of the multiplicity factor; away from the support it
contradicts the matched zero set. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_ownerRoot
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
              F hF hF0 ρ w) :
    ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_from_maximalMultiplicity_ownerRoot
      F Q hF hF0 ρ hQ_an hfactor

/-- Zero-free analytic Jensen mean theorem for a removable quotient on a closed
disk.

This is the exact zero-free input needed by the boundary-log decomposition:
if `Q` is analytic and nonvanishing on the Jensen disk, then the normalized
boundary mean of `log ‖Q‖` is the central value `log ‖Q 0‖`. -/

end
end LFunctions
end Boundary
