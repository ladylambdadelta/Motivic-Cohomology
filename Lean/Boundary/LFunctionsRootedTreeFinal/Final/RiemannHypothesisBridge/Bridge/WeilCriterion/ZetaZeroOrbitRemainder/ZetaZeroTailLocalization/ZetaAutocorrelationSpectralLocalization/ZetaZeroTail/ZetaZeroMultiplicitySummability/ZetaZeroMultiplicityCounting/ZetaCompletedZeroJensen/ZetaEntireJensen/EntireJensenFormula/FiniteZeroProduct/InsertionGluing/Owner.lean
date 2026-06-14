import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.ProductCore.Owner

/-!
# Normalized factor insertion and removable gluing

This file is a sequential owner sublayer split from the finite zero-product
Jensen package.  It owns the global gluing and insertion quotient transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Raw quotient obtained after inserting the normalized factor away from the
inserted support point. -/
noncomputable def entireFunction_insertNormalizedFactor_rawQuotient
    (F Qold : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (w : ℂ) : ℂ :=
  Qold w /
    ((1 - w / (a : ℂ)) ^
      entireFunctionZeroMultiplicity F hF (a : ℂ))

/-- The globally glued quotient: local removable fill at `a`, raw quotient
away from `a`. -/
noncomputable def entireFunction_insertNormalizedFactor_gluedQuotient
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (w : ℂ) : ℂ :=
  if w = (a : ℂ) then
    Qloc w
  else
    entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a w

/-- The normalized inserted factor is nonzero away from its center. -/
theorem entireFunction_insertNormalizedFactor_normalizedFactor_pow_ne_of_ne
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (ha0 : (a : ℂ) ≠ 0)
    {w : ℂ}
    (hw_ne : w ≠ (a : ℂ)) :
    (1 - w / (a : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (a : ℂ) ≠ 0 := by
  have hbase_ne : 1 - w / (a : ℂ) ≠ 0 := by
    intro hbase_zero
    have hdiv_eq_one : w / (a : ℂ) = 1 :=
      (eq_of_sub_eq_zero hbase_zero).symm
    have hw_eq : w = (a : ℂ) := by
      calc
        w = (w / (a : ℂ)) * (a : ℂ) := by
          exact (div_mul_cancel₀ w ha0).symm
        _ = 1 * (a : ℂ) := by
          exact congrArg (fun x : ℂ => x * (a : ℂ)) hdiv_eq_one
        _ = (a : ℂ) := one_mul (a : ℂ)
    exact hw_ne hw_eq
  exact
    pow_ne_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
      hbase_ne

/-- Analyticity of one normalized finite-product factor. -/
theorem entireFunction_finiteZeroDivisorProduct_factor_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : EntireFunctionZero F)
    (w : ℂ) :
    AnalyticAt ℂ
      (fun x : ℂ =>
        (1 - x / (z : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (z : ℂ))
      w := by
  by_cases hz0 : (z : ℂ) = 0
  · have hconst :
        (fun x : ℂ =>
          (1 - x / (z : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (z : ℂ))
          =
        (fun _x : ℂ =>
          (1 - 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) := by
      funext x
      calc
        (1 - x / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) =
            (1 - x / 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
          exact congrArg
            (fun y : ℂ => (1 - x / y) ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
            hz0
        _ = (1 - 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
          exact congrArg
            (fun y : ℂ => (1 - y) ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
            (div_zero x)
    exact Eq.subst (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w) hconst.symm analyticAt_const
  · exact
      ((analyticAt_const.sub
        (analyticAt_id.div analyticAt_const hz0)).pow
          (entireFunctionZeroMultiplicity F hF (z : ℂ)))

/-- Analyticity of a finite normalized zero-divisor product. -/
theorem entireFunction_finiteZeroDivisorProduct_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (S : Finset (EntireFunctionZero F))
    (w : ℂ) :
    AnalyticAt ℂ
      (fun x : ℂ =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF S x)
      w := by
  classical
  refine Finset.induction_on S ?empty ?insert
  · have hconst :
        (fun x : ℂ =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF ∅ x)
          =
        (fun _x : ℂ => 1) := by
      funext x
      rfl
    exact Eq.subst (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w) hconst.symm analyticAt_const
  · intro z T hz_not_mem hT
    have hfactor :
        AnalyticAt ℂ
          (fun x : ℂ =>
            (1 - x / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))
          w :=
      entireFunction_finiteZeroDivisorProduct_factor_analyticAt F hF z w
    have hprod_eq :
        (fun x : ℂ =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF (insert z T) x)
          =
        (fun x : ℂ =>
          (1 - x / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ) *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF T x) := by
      funext x
      exact
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
          F hF T z hz_not_mem x
    exact
      Eq.subst
        (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w)
        hprod_eq.symm
        (hfactor.mul hT)

/-- The glued quotient agrees with the local removable quotient near the
inserted point. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_local
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (hQloc_eq :
      Qloc =ᶠ[𝓝[≠] (a : ℂ)]
        entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a) :
    entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a
      =ᶠ[𝓝 (a : ℂ)] Qloc := by
  rw [eventuallyEq_nhdsWithin_iff] at hQloc_eq
  exact
    hQloc_eq.mono
      (fun w hw =>
        by
          by_cases hw_eq : w = (a : ℂ)
          · calc
              entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w =
                  Qloc w := if_pos hw_eq
          · calc
              entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w =
                  entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a w := if_neg hw_eq
              _ = Qloc w := (hw hw_eq).symm)

/-- Analyticity of the glued quotient at the inserted point. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_analyticAt_insertedPoint
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (hQloc_an : AnalyticAt ℂ Qloc (a : ℂ))
    (hQloc_eq :
      Qloc =ᶠ[𝓝[≠] (a : ℂ)]
        entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a) :
    AnalyticAt ℂ
      (entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a)
      (a : ℂ) :=
  hQloc_an.congr
    (entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_local
      F Qold Qloc hF a hQloc_eq).symm

/-- Away from the inserted point, the glued quotient agrees locally with the
raw quotient. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_raw_of_ne
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    {w : ℂ}
    (hw_ne : w ≠ (a : ℂ)) :
    entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a
      =ᶠ[𝓝 w]
        entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a := by
  exact
    (eventually_ne_nhds hw_ne).mono
      (fun x hx_ne =>
        if_neg hx_ne)

/-- The raw quotient is analytic away from the inserted point whenever the old
quotient is analytic there. -/
theorem entireFunction_insertNormalizedFactor_rawQuotient_analyticAt_of_ne
    (F Qold : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (ha0 : (a : ℂ) ≠ 0)
    {w : ℂ}
    (hw_ne : w ≠ (a : ℂ))
    (hQold_an : AnalyticAt ℂ Qold w) :
    AnalyticAt ℂ
      (entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a)
      w := by
  have hden_ne :
      (fun x : ℂ =>
        (1 - x / (a : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (a : ℂ)) w ≠ 0 :=
    entireFunction_insertNormalizedFactor_normalizedFactor_pow_ne_of_ne
      F hF a ha0 hw_ne
  have hden_an :
      AnalyticAt ℂ
        (fun x : ℂ =>
          (1 - x / (a : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (a : ℂ))
        w := by
    exact
      ((analyticAt_const.sub
        (analyticAt_id.div analyticAt_const ha0)).pow
          (entireFunctionZeroMultiplicity F hF (a : ℂ)))
  exact hQold_an.div hden_an hden_ne

/-- Closed-disk analyticity of the glued quotient, by the inserted-point /
off-point case split. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_analyticOn_closedDisk
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (a : EntireFunctionZero F)
    (ha0 : (a : ℂ) ≠ 0)
    (hQloc_an : AnalyticAt ℂ Qloc (a : ℂ))
    (hQloc_eq :
      Qloc =ᶠ[𝓝[≠] (a : ℂ)]
        entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a)
    (hQold_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Qold w) :
    ∀ w : ℂ,
      ‖w‖ ≤ ρ →
        AnalyticAt ℂ
          (entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a)
          w := by
  intro w hwρ
  by_cases hw_eq : w = (a : ℂ)
  · exact
      Eq.subst
        (motive := fun x : ℂ =>
          AnalyticAt ℂ
            (entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a)
            x)
        hw_eq.symm
        (entireFunction_insertNormalizedFactor_gluedQuotient_analyticAt_insertedPoint
          F Qold Qloc hF a hQloc_an hQloc_eq)
  · exact
      (entireFunction_insertNormalizedFactor_rawQuotient_analyticAt_of_ne
        F Qold hF a ha0 hw_eq (hQold_an w hwρ)).congr
        (entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_raw_of_ne
          F Qold Qloc hF a hw_eq).symm

/-- Off the inserted point, the glued quotient satisfies the inserted product
identity by ordinary division and the finite-product insertion identity. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_of_ne
    (F Qold Qloc g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hQold_factor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Qold w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    {w : ℂ}
    (hw_ne : w ≠ (a : ℂ))
    (hwρ : ‖w‖ ≤ ρ) :
    F w =
      entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w *
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) w := by
  let A : ℂ :=
    (1 - w / (a : ℂ)) ^ entireFunctionZeroMultiplicity F hF (a : ℂ)
  let P : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
      F hF S w
  have hA_ne : A ≠ 0 :=
    entireFunction_insertNormalizedFactor_normalizedFactor_pow_ne_of_ne
      F hF a ha0 hw_ne
  have hglue :
      entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w =
        Qold w / A := by
    calc
      entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w =
          entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a w := by
        exact if_neg hw_ne
      _ = Qold w / A := by
        rfl
  have hinsert :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) w =
        A * P := by
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
        F hF S a ha_not_mem w
  calc
    F w = Qold w * P := hQold_factor w hwρ
    _ = (Qold w / A) * (A * P) := by
      calc
        Qold w * P = ((Qold w / A) * A) * P := by
          exact congrArg (fun x : ℂ => x * P) (div_mul_cancel₀ (Qold w) hA_ne).symm
        _ = (Qold w / A) * (A * P) := mul_assoc (Qold w / A) A P
    _ =
        entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF (insert a S) w := by
      exact
        congrArg₂
          (fun x y : ℂ => x * y)
          hglue.symm
          hinsert.symm

/-- At the inserted point, the glued quotient satisfies the inserted product
identity with the removable value prescribed by the local Taylor unit. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_at_insertedPoint
    (F Qold Qloc g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (ha0 : (a : ℂ) ≠ 0)
    (hQloc_value :
      Qloc (a : ℂ) =
        g (a : ℂ) /
          (((-(a : ℂ)⁻¹) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S (a : ℂ)))
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    F (a : ℂ) =
      entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a (a : ℂ) *
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) (a : ℂ) := by
  let m : ℕ := entireFunctionZeroMultiplicity F hF (a : ℂ)
  let C : ℂ := (-(a : ℂ)⁻¹) ^ m
  let Z : ℂ := ((a : ℂ) - (a : ℂ)) ^ m
  let P : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
      F hF S (a : ℂ)
  have hP_ne : P ≠ 0 :=
    entireFunction_finiteZeroDivisorProduct_nonzero_at_newSupport
      F hF S a ha_not_mem hS0
  have hC_ne : C ≠ 0 := by
    have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero ha0
    have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
      neg_ne_zero.mpr hinv_ne
    exact pow_ne_zero m hneg_ne
  have hD_ne : C * P ≠ 0 :=
    mul_ne_zero hC_ne hP_ne
  have hF_local :
      F (a : ℂ) = Z * g (a : ℂ) := by
    calc
      F (a : ℂ) =
          ((a : ℂ) - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g (a : ℂ) :=
        hg_factor.self_of_nhds
      _ = Z * g (a : ℂ) := by
        exact smul_eq_mul Z (g (a : ℂ))
  have hglue :
      entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a (a : ℂ) =
        Qloc (a : ℂ) :=
    if_pos rfl
  have hinsert :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) (a : ℂ) =
        (C * Z) * P := by
    have hraw_insert :
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF (insert a S) (a : ℂ) =
          (1 - (a : ℂ) / (a : ℂ)) ^ m * P :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
        F hF S a ha_not_mem (a : ℂ)
    have hnorm :
        (1 - (a : ℂ) / (a : ℂ)) ^ m = C * Z :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
        ha0 m
    calc
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
          F hF (insert a S) (a : ℂ) =
          (1 - (a : ℂ) / (a : ℂ)) ^ m * P := hraw_insert
      _ = (C * Z) * P := by
        exact congrArg (fun x : ℂ => x * P) hnorm
  calc
    F (a : ℂ) = Z * g (a : ℂ) := hF_local
    _ = (g (a : ℂ) / (C * P)) * ((C * Z) * P) := by
      calc
        Z * g (a : ℂ) = g (a : ℂ) * Z := mul_comm Z (g (a : ℂ))
        _ = ((g (a : ℂ) / (C * P)) * (C * P)) * Z := by
          exact congrArg (fun x : ℂ => x * Z) (div_mul_cancel₀ (g (a : ℂ)) hD_ne).symm
        _ = (g (a : ℂ) / (C * P)) * ((C * P) * Z) := by
          exact mul_assoc (g (a : ℂ) / (C * P)) (C * P) Z
        _ = (g (a : ℂ) / (C * P)) * ((C * Z) * P) := by
          have hCPZ : (C * P) * Z = (C * Z) * P := by
            calc
              (C * P) * Z = C * (P * Z) := mul_assoc C P Z
              _ = C * (Z * P) := by
                exact congrArg (fun x : ℂ => C * x) (mul_comm P Z)
              _ = (C * Z) * P := (mul_assoc C Z P).symm
          exact congrArg (fun x : ℂ => (g (a : ℂ) / (C * P)) * x) hCPZ
    _ =
        entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a (a : ℂ) *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF (insert a S) (a : ℂ) := by
      exact
        congrArg₂
          (fun x y : ℂ => x * y)
          (Eq.trans hglue hQloc_value)
          hinsert.symm

/-- Product identity for the glued quotient after inserting one normalized
factor. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_product_identity
    (F Qold Qloc g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (hQold_factor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Qold w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S w)
    (hQloc_value :
      Qloc (a : ℂ) =
        g (a : ℂ) /
          (((-(a : ℂ)⁻¹) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ)) *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S (a : ℂ)))
    (hg_factor :
      ∀ᶠ w in 𝓝 (a : ℂ),
        F w =
          (w - (a : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (a : ℂ) •
            g w) :
    ∀ w : ℂ,
      ‖w‖ ≤ ρ →
      F w =
        entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF (insert a S) w := by
  intro w hwρ
  by_cases hw_eq : w = (a : ℂ)
  · exact
      Eq.subst
        (motive := fun x : ℂ =>
          F x =
            entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF (insert a S) x)
        hw_eq.symm
        (entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_at_insertedPoint
          F Qold Qloc g hF ρ S a ha_not_mem hS0 ha0 hQloc_value hg_factor)
  · exact
      entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_of_ne
        F Qold Qloc g hF ρ S a ha_not_mem ha0 hQold_factor hw_eq hwρ

/-- Origin normalization of the glued quotient. -/
theorem entireFunction_insertNormalizedFactor_gluedQuotient_zero
    (F Qold Qloc : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (a : EntireFunctionZero F)
    (ha0 : (a : ℂ) ≠ 0)
    (hQold_zero : Qold 0 = F 0) :
    entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a 0 = F 0 := by
  have hzero_ne : (0 : ℂ) ≠ (a : ℂ) :=
    fun h => ha0 h.symm
  have hfactor_zero :
      (1 - (0 : ℂ) / (a : ℂ)) ^
          entireFunctionZeroMultiplicity F hF (a : ℂ) = 1 :=
    entireFunction_normalizedFactor_pow_at_zero
      (entireFunctionZeroMultiplicity F hF (a : ℂ))
  calc
    entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a 0 =
        entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a 0 := by
      exact if_neg hzero_ne
    _ =
        Qold 0 /
          ((1 - (0 : ℂ) / (a : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (a : ℂ)) := by
      rfl
    _ = Qold 0 / 1 := by
      exact congrArg (fun x : ℂ => Qold 0 / x) hfactor_zero
    _ = Qold 0 := div_one (Qold 0)
    _ = F 0 := hQold_zero

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
  rcases hlocal_div with ⟨Qloc, hQloc_an, hQloc_eq, hQloc_value⟩
  refine
    ⟨entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a,
      ?_, ?_, ?_⟩
  · exact
      entireFunction_insertNormalizedFactor_gluedQuotient_analyticOn_closedDisk
        F Qold Qloc hF ρ a ha0 hQloc_an hQloc_eq hQold_an
  · exact
      entireFunction_insertNormalizedFactor_gluedQuotient_product_identity
        F Qold Qloc g hF ρ S a ha_not_mem hS0 ha0 hQold_factor
        hQloc_value hg_factor
  · exact
      entireFunction_insertNormalizedFactor_gluedQuotient_zero
        F Qold Qloc hF a ha0 hQold_zero

/-- Cancellation identity for the inserted local quotient model.

This is the algebra behind replacing the old local quotient
`(q * g) / p` divided by the inserted normalized factor `c * q` with the
filled inserted local model `g / (c * p)`. -/
theorem complex_insertedLocalModel_division_cancellation
    (g q c p : ℂ)
    (hq : q ≠ 0)
    (hc : c ≠ 0)
    (hp : p ≠ 0) :
    g / (c * p) = ((q * g) / p) / (c * q) := by
  have hcp : c * p ≠ 0 :=
    mul_ne_zero hc hp
  have hcq : c * q ≠ 0 :=
    mul_ne_zero hc hq
  have hright_mul :
      (((q * g) / p) / (c * q)) * (c * q) =
        (q * g) / p := by
    exact div_mul_cancel₀ ((q * g) / p) hcq
  have hleft_mul :
      (g / (c * p)) * (c * q) =
        (q * g) / p := by
    calc
      (g / (c * p)) * (c * q)
          = (g * (c * p)⁻¹) * (c * q) := by
            exact congrArg (fun x : ℂ => x * (c * q)) (div_eq_mul_inv g (c * p))
      _ = (g * (p⁻¹ * c⁻¹)) * (c * q) := by
            exact congrArg (fun x : ℂ => (g * x) * (c * q)) (mul_inv_rev c p)
      _ = ((g * p⁻¹) * c⁻¹) * (c * q) := by
            exact congrArg (fun x : ℂ => x * (c * q)) (mul_assoc g p⁻¹ c⁻¹)
      _ = (g * p⁻¹) * (c⁻¹ * (c * q)) := by
            exact mul_assoc (g * p⁻¹) c⁻¹ (c * q)
      _ = (g * p⁻¹) * ((c⁻¹ * c) * q) := by
            exact congrArg (fun x : ℂ => (g * p⁻¹) * x) (mul_assoc c⁻¹ c q).symm
      _ = (g * p⁻¹) * (1 * q) := by
            exact congrArg (fun x : ℂ => (g * p⁻¹) * (x * q)) (inv_mul_cancel₀ hc)
      _ = (g * p⁻¹) * q := by
            exact congrArg (fun x : ℂ => (g * p⁻¹) * x) (one_mul q)
      _ = q * (g * p⁻¹) := by
            exact mul_comm (g * p⁻¹) q
      _ = (q * g) * p⁻¹ := by
            exact (mul_assoc q g p⁻¹).symm
      _ = (q * g) / p := by
            exact (div_eq_mul_inv (q * g) p).symm
  exact
    mul_left_cancel₀ hcq
      (Eq.trans hleft_mul hright_mul.symm)

/-- Local removable division package for the inserted normalized factor,
constructed from the old quotient and the local Taylor unit. -/
theorem entireFunction_insertNormalizedFactor_localDivision_from_oldQuotient_and_localUnit
    (F Qold g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (haρ : ‖(a : ℂ)‖ ≤ ρ)
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
              F hF S w) :
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
              F hF S (a : ℂ)) := by
  let m : ℕ := entireFunctionZeroMultiplicity F hF (a : ℂ)
  let oldProduct : ℂ → ℂ :=
    fun w : ℂ =>
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
        F hF S w
  let oldLocalModel : ℂ → ℂ :=
    fun w : ℂ => ((w - (a : ℂ)) ^ m * g w) / oldProduct w
  let insertedLocalModel : ℂ → ℂ :=
    fun w : ℂ =>
      g w /
        (((-(a : ℂ)⁻¹) ^ m) * oldProduct w)
  have hS_insert0 :
      ∀ z : EntireFunctionZero F, z ∈ insert a S → (z : ℂ) ≠ 0 := by
    intro z hz
    have hz_cases : z = a ∨ z ∈ S :=
      Finset.mem_insert.mp hz
    cases hz_cases with
    | inl hza =>
        exact Eq.subst (motive := fun x : EntireFunctionZero F => (x : ℂ) ≠ 0) hza.symm ha0
    | inr hzS =>
        exact hS0 z hzS
  have hgood :
      ∃ᶠ w in 𝓝[≠] (a : ℂ),
        w ≠ (a : ℂ) ∧
        ‖w‖ ≤ ρ ∧
          ∀ z : EntireFunctionZero F,
            z ∈ S →
              w ≠ (z : ℂ) := by
    have hgood_insert :
        ∃ᶠ w in 𝓝[≠] (a : ℂ),
          w ≠ (a : ℂ) ∧
          ‖w‖ ≤ ρ ∧
            ∀ z : EntireFunctionZero F,
              z ∈ (insert a S).erase a →
                w ≠ (z : ℂ) :=
      entireFunction_closedDisk_puncturedGoodPoints_frequently
        F (insert a S) a (Finset.mem_insert_self a S) ha0 ρ haρ
    exact
      hgood_insert.mono
        (fun w hw =>
          ⟨hw.1, hw.2.1,
            fun z hzS =>
              hw.2.2 z
                (Finset.mem_erase.mpr ⟨ha_not_mem.ne_of_mem hzS, Finset.mem_insert_of_mem hzS⟩)⟩)
  have hlocal_punctured :
      ∀ᶠ w in 𝓝[≠] (a : ℂ),
        F w = (w - (a : ℂ)) ^ m * g w := by
    have hlocal :
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w = (w - (a : ℂ)) ^ m * g w :=
      hg_factor.mono
        (fun w hw =>
          Eq.trans hw (smul_eq_mul ((w - (a : ℂ)) ^ m) (g w)))
    exact hlocal.filter_mono nhdsWithin_le_nhds
  have holdProduct_an :
      AnalyticAt ℂ oldProduct (a : ℂ) := by
    exact
      entireFunction_finiteZeroDivisorProduct_analyticAt
        F hF S (a : ℂ)
  have holdProduct_ne :
      oldProduct (a : ℂ) ≠ 0 := by
    exact
      entireFunction_finiteZeroDivisorProduct_nonzero_at_newSupport
        F hF S a ha_not_mem hS0
  have holdLocalModel_an :
      AnalyticAt ℂ oldLocalModel (a : ℂ) := by
    have hpow_an :
        AnalyticAt ℂ (fun w : ℂ => (w - (a : ℂ)) ^ m) (a : ℂ) :=
      (analyticAt_id.sub analyticAt_const).pow m
    have hnum_an :
        AnalyticAt ℂ (fun w : ℂ => (w - (a : ℂ)) ^ m * g w) (a : ℂ) :=
      hpow_an.mul hg_an
    exact hnum_an.div holdProduct_an holdProduct_ne
  have hQold_model_frequently :
      ∃ᶠ w in 𝓝[≠] (a : ℂ), Qold w = oldLocalModel w := by
    exact
      (hgood.and_eventually hlocal_punctured).mono
        (fun w hw =>
          let hwgood := hw.1
          let hF_local := hw.2
          have hproduct_ne : oldProduct w ≠ 0 :=
            Finset.prod_ne_zero_iff.mpr
              (fun z hz =>
                pow_ne_zero
                  (entireFunctionZeroMultiplicity F hF (z : ℂ))
                  (fun hfactor =>
                    hwgood.2.2 z hz
                      ((entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_factor_eq_zero_iff
                        F hF S
                        (fun y hy => hS0 y hy)
                        z hz w).1 hfactor).symm))
          have hfactor_w :
              F w = Qold w * oldProduct w :=
            hQold_factor w hwgood.2.1
          have hQold_mul :
              Qold w * oldProduct w = (w - (a : ℂ)) ^ m * g w :=
            Eq.trans hfactor_w.symm hF_local
          calc
            Qold w = (Qold w * oldProduct w) / oldProduct w := by
              exact (mul_div_cancel₀ (Qold w) hproduct_ne).symm
            _ = ((w - (a : ℂ)) ^ m * g w) / oldProduct w := by
              exact congrArg (fun x : ℂ => x / oldProduct w) hQold_mul
            _ = oldLocalModel w := rfl)
  have hQold_model :
      Qold =ᶠ[𝓝[≠] (a : ℂ)] oldLocalModel :=
    analyticAt_eventuallyEq_punctured_of_frequentlyEq_punctured
      (hQold_an (a : ℂ) haρ)
      holdLocalModel_an
      hQold_model_frequently
  have hinserted_an :
      AnalyticAt ℂ insertedLocalModel (a : ℂ) := by
    have hcoeff_an :
        AnalyticAt ℂ
          (fun _w : ℂ => (-(a : ℂ)⁻¹) ^ m)
          (a : ℂ) :=
      analyticAt_const
    have hden_an :
        AnalyticAt ℂ
          (fun w : ℂ => ((-(a : ℂ)⁻¹) ^ m) * oldProduct w)
          (a : ℂ) :=
      hcoeff_an.mul holdProduct_an
    have hcoeff_ne : (-(a : ℂ)⁻¹) ^ m ≠ 0 := by
      have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
        inv_ne_zero ha0
      have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
        neg_ne_zero.mpr hinv_ne
      exact pow_ne_zero m hneg_ne
    have hden_ne : ((-(a : ℂ)⁻¹) ^ m) * oldProduct (a : ℂ) ≠ 0 :=
      mul_ne_zero hcoeff_ne holdProduct_ne
    exact hg_an.div hden_an hden_ne
  have hraw_eq_inserted :
      insertedLocalModel =ᶠ[𝓝[≠] (a : ℂ)]
        (fun w : ℂ =>
          Qold w /
            ((1 - w / (a : ℂ)) ^ m)) := by
    have hpunctured :
        ∀ᶠ w in 𝓝[≠] (a : ℂ), w ≠ (a : ℂ) :=
      (eventually_mem_nhdsWithin :
        ∀ᶠ w in 𝓝[≠] (a : ℂ), w ∈ ({(a : ℂ)}ᶜ : Set ℂ))
    have hproduct_ne_eventual :
        ∀ᶠ w in 𝓝[≠] (a : ℂ), oldProduct w ≠ 0 :=
      (holdProduct_an.continuousAt.eventually_ne holdProduct_ne).filter_mono
        nhdsWithin_le_nhds
    exact
      ((hQold_model.and_eventually hpunctured).and_eventually hproduct_ne_eventual).mono
        (fun w hw =>
          have hQw : Qold w = oldLocalModel w := hw.1.1
          have hwa : w ≠ (a : ℂ) := hw.1.2
          have hpow_ne : (w - (a : ℂ)) ^ m ≠ 0 :=
            pow_ne_zero m (sub_ne_zero.mpr hwa)
          have hcoeff_ne : (-(a : ℂ)⁻¹) ^ m ≠ 0 := by
            have hinv_ne : (a : ℂ)⁻¹ ≠ 0 :=
              inv_ne_zero ha0
            have hneg_ne : -(a : ℂ)⁻¹ ≠ 0 :=
              neg_ne_zero.mpr hinv_ne
            exact pow_ne_zero m hneg_ne
          have hprod_ne : oldProduct w ≠ 0 := hw.2
          have hnorm :
              (1 - w / (a : ℂ)) ^ m =
                ((-(a : ℂ)⁻¹) ^ m) * (w - (a : ℂ)) ^ m :=
            entireFunction_standardJensenFormula_nonzeroAtOrigin_normalizedFactor_pow_eq_localFactor
              ha0 m
          calc
            insertedLocalModel w =
                g w / (((-(a : ℂ)⁻¹) ^ m) * oldProduct w) := rfl
            _ = (((w - (a : ℂ)) ^ m * g w) / oldProduct w) /
                (((-(a : ℂ)⁻¹) ^ m) * (w - (a : ℂ)) ^ m) := by
              exact
                complex_insertedLocalModel_division_cancellation
                  (g w)
                  ((w - (a : ℂ)) ^ m)
                  ((-(a : ℂ)⁻¹) ^ m)
                  (oldProduct w)
                  hpow_ne
                  hcoeff_ne
                  hprod_ne
            _ = Qold w /
                (((-(a : ℂ)⁻¹) ^ m) * (w - (a : ℂ)) ^ m) := by
              exact
                congrArg
                  (fun x : ℂ => x /
                    (((-(a : ℂ)⁻¹) ^ m) * (w - (a : ℂ)) ^ m))
                  hQw.symm
            _ = Qold w / ((1 - w / (a : ℂ)) ^ m) := by
              exact congrArg (fun x : ℂ => Qold w / x) hnorm.symm)
  refine ⟨insertedLocalModel, hinserted_an, hraw_eq_inserted, ?_⟩
  rfl

/-- If the inserted zero lies outside the closed disk, insertion is ordinary
division by a nonvanishing analytic normalized factor throughout the disk. -/
theorem entireFunction_insertNormalizedFactor_removableQuotient_off_insertedDisk
    (F Qold g : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (S : Finset (EntireFunctionZero F))
    (a : EntireFunctionZero F)
    (ha_not_mem : a ∉ S)
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
    (ha0 : (a : ℂ) ≠ 0)
    (haρ_not : ¬ ‖(a : ℂ)‖ ≤ ρ)
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
  refine
    ⟨entireFunction_insertNormalizedFactor_gluedQuotient F Qold g hF a,
      ?_, ?_, ?_⟩
  · intro w hwρ
    have hw_ne : w ≠ (a : ℂ) := by
      intro hw_eq
      exact haρ_not (hw_eq ▸ hwρ)
    exact
      (entireFunction_insertNormalizedFactor_rawQuotient_analyticAt_of_ne
        F Qold hF a ha0 hw_ne (hQold_an w hwρ)).congr
        (entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_raw_of_ne
          F Qold g hF a hw_ne).symm
  · intro w hwρ
    have hw_ne : w ≠ (a : ℂ) := by
      intro hw_eq
      exact haρ_not (hw_eq ▸ hwρ)
    exact
      entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_of_ne
        F Qold g g hF ρ S a ha_not_mem ha0 hQold_factor hw_ne hwρ
  · exact
      entireFunction_insertNormalizedFactor_gluedQuotient_zero
        F Qold g hF a ha0 hQold_zero

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
  by_cases haρ : ‖(a : ℂ)‖ ≤ ρ
  · have hlocal_div :
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
                  F hF S (a : ℂ)) :=
      entireFunction_insertNormalizedFactor_localDivision_from_oldQuotient_and_localUnit
        F Qold g hF ρ S a ha_not_mem hS0 ha0 haρ
        hg_an hg_ne hg_factor hQold_an hQold_factor
    exact
      entireFunction_insertNormalizedFactor_glue_localDivision
        F Qold g hF ρ hρ S a ha_not_mem hS0 ha0 hg_an hg_ne hg_factor
        hQold_an hQold_factor hQold_zero hlocal_div
  · exact
      entireFunction_insertNormalizedFactor_removableQuotient_off_insertedDisk
        F Qold g hF ρ S a ha_not_mem hS0 ha0 haρ
        hQold_an hQold_factor hQold_zero

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
