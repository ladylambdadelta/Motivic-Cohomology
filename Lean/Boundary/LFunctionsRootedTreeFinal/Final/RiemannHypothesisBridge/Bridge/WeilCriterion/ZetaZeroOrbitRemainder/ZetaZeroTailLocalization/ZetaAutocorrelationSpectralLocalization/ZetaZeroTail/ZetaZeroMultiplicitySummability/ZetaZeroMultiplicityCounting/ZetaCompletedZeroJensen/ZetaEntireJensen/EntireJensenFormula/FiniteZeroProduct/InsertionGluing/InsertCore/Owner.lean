import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.Avoidance

/-!
# Normalized factor insertion and removable gluing

This owner layer was split from `FiniteZeroProduct.InsertionGluing.Owner` without changing public declaration names.
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
  exact
    if hz0 : (z : ℂ) = 0 then
      have hconst :
          (fun x : ℂ =>
            (1 - x / (z : ℂ)) ^
              entireFunctionZeroMultiplicity F hF (z : ℂ))
            =
          (fun _x : ℂ =>
            (1 - 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)) := by
        exact funext_iff.mpr
          (fun x =>
            calc
              (1 - x / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) =
                  (1 - x / 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
                exact congrArg
                  (fun y : ℂ => (1 - x / y) ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
                  hz0
              _ = (1 - 0) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
                exact congrArg
                  (fun y : ℂ => (1 - y) ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
                  (div_zero x))
      Eq.subst (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w) hconst.symm analyticAt_const
    else
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
  have hempty :
      AnalyticAt ℂ
        (fun x : ℂ =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF ∅ x)
        w := by
    have hconst :
        (fun x : ℂ =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
            F hF ∅ x)
          =
        (fun _x : ℂ => 1) := by
      exact funext_iff.mpr (fun _x => rfl)
    exact Eq.subst (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w) hconst.symm analyticAt_const
  have hinsert :
      ∀ z T,
        z ∉ T →
        AnalyticAt ℂ
          (fun x : ℂ =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF T x)
          w →
        AnalyticAt ℂ
          (fun x : ℂ =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert z T) x)
          w := by
    intro z T hz_not_mem hT
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
      exact funext_iff.mpr
        (fun x =>
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct_insert
            F hF T z hz_not_mem x)
    exact
      Eq.subst
        (motive := fun f : ℂ → ℂ => AnalyticAt ℂ f w)
        hprod_eq.symm
        (hfactor.mul hT)
  exact Finset.induction_on S hempty hinsert

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
  have hQloc_eq' :
      ∀ᶠ w in 𝓝 (a : ℂ),
        w ≠ (a : ℂ) →
          Qloc w = entireFunction_insertNormalizedFactor_rawQuotient F Qold hF a w :=
    eventuallyEq_nhdsWithin_iff.mp hQloc_eq
  exact
    hQloc_eq'.mono
      (fun w hw =>
        if hw_eq : w = (a : ℂ) then
          calc
            entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a w =
                Qloc w := if_pos hw_eq
        else
          calc
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
  exact
    if hw_eq : w = (a : ℂ) then
      Eq.subst
        (motive := fun x : ℂ =>
          AnalyticAt ℂ
            (entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a)
            x)
        hw_eq.symm
        (entireFunction_insertNormalizedFactor_gluedQuotient_analyticAt_insertedPoint
          F Qold Qloc hF a hQloc_an hQloc_eq)
    else
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
    (hS0 : ∀ z : EntireFunctionZero F, z ∈ S → (z : ℂ) ≠ 0)
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
        exact (smul_eq_mul ℂ : Z • g (a : ℂ) = Z * g (a : ℂ))
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
          (Eq.trans hglue hQloc_value).symm
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
  exact
    if hw_eq : w = (a : ℂ) then
      Eq.subst
        (motive := fun x : ℂ =>
          F x =
            entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a x *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                F hF (insert a S) x)
        hw_eq.symm
        (entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_at_insertedPoint
          F Qold Qloc g hF ρ S a ha_not_mem hS0 ha0 hQloc_value hg_factor)
    else
      entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_of_ne
        F Qold Qloc g hF ρ S a ha_not_mem hS0 ha0 hQold_factor hw_eq hwρ

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


end
end LFunctions
end Boundary
