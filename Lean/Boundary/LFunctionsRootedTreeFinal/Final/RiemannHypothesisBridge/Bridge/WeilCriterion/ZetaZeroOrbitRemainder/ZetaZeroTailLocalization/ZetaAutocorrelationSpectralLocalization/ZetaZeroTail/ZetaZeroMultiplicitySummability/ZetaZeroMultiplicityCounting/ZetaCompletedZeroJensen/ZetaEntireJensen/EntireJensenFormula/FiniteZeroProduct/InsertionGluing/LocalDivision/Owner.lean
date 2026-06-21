import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.InsertCore.Owner

/-!
# Normalized factor insertion and removable gluing

This owner layer was split from `FiniteZeroProduct.InsertionGluing.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

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
  exact
    match hlocal_div with
    | Exists.intro Qloc hQloc_data =>
        match hQloc_data with
        | And.intro hQloc_an hQloc_tail =>
            match hQloc_tail with
            | And.intro hQloc_eq hQloc_value =>
                let Q : ℂ → ℂ :=
                  entireFunction_insertNormalizedFactor_gluedQuotient F Qold Qloc hF a
                have hQ_an :
                    ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w :=
                  entireFunction_insertNormalizedFactor_gluedQuotient_analyticOn_closedDisk
                    F Qold Qloc hF ρ a ha0 hQloc_an hQloc_eq hQold_an
                have hQ_product :
                    ∀ w : ℂ,
                      ‖w‖ ≤ ρ →
                      F w =
                        Q w *
                          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
                            F hF (insert a S) w :=
                  entireFunction_insertNormalizedFactor_gluedQuotient_product_identity
                    F Qold Qloc g hF ρ S a ha_not_mem hS0 ha0 hQold_factor
                    hQloc_value hg_factor
                have hQ_zero : Q 0 = F 0 :=
                  entireFunction_insertNormalizedFactor_gluedQuotient_zero
                    F Qold Qloc hF a ha0 hQold_zero
                Exists.intro Q (And.intro hQ_an (And.intro hQ_product hQ_zero))

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
            exact congrArg (fun x : ℂ => x * (c * q)) (mul_assoc g p⁻¹ c⁻¹).symm
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
    mul_right_cancel₀ hcq
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
                (Finset.mem_erase.mpr
                  ⟨fun hza =>
                    ha_not_mem (Eq.subst (motive := fun x : EntireFunctionZero F => x ∈ S) hza hzS),
                    Finset.mem_insert_of_mem hzS⟩)⟩)
  have hlocal_punctured :
      ∀ᶠ w in 𝓝[≠] (a : ℂ),
        F w = (w - (a : ℂ)) ^ m * g w := by
    have hlocal :
        ∀ᶠ w in 𝓝 (a : ℂ),
          F w = (w - (a : ℂ)) ^ m * g w :=
      hg_factor.mono
        (fun w hw =>
          Eq.trans hw (smul_eq_mul ℂ : ((w - (a : ℂ)) ^ m) • g w = ((w - (a : ℂ)) ^ m) * g w))
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
      (Filter.Eventually.and_frequently hlocal_punctured hgood).mono
        (fun w hw =>
          let hF_local := hw.1
          let hwgood := hw.2
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
                        z hz w).1 hfactor)))
          have hfactor_w :
              F w = Qold w * oldProduct w :=
            hQold_factor w hwgood.2.1
          have hQold_mul :
              Qold w * oldProduct w = (w - (a : ℂ)) ^ m * g w :=
            Eq.trans hfactor_w.symm hF_local
          calc
            Qold w = (Qold w * oldProduct w) / oldProduct w := by
              exact (mul_div_cancel_right₀ (Qold w) hproduct_ne).symm
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
      ((hQold_model.and hpunctured).and hproduct_ne_eventual).mono
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
  have hinserted_value :
      insertedLocalModel (a : ℂ) =
        g (a : ℂ) /
          (((-(a : ℂ)⁻¹) ^ m) *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF S (a : ℂ)) :=
    rfl
  exact Exists.intro insertedLocalModel
    (And.intro hinserted_an
      (And.intro hraw_eq_inserted hinserted_value))

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
  let Q : ℂ → ℂ :=
    entireFunction_insertNormalizedFactor_gluedQuotient F Qold g hF a
  have hQ_an :
      ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w := by
    intro w hwρ
    have hw_ne : w ≠ (a : ℂ) := by
      intro hw_eq
      exact haρ_not (hw_eq ▸ hwρ)
    exact
      (entireFunction_insertNormalizedFactor_rawQuotient_analyticAt_of_ne
        F Qold hF a ha0 hw_ne (hQold_an w hwρ)).congr
        (entireFunction_insertNormalizedFactor_gluedQuotient_eventuallyEq_raw_of_ne
          F Qold g hF a hw_ne).symm
  have hQ_product :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisorProduct
              F hF (insert a S) w := by
    intro w hwρ
    have hw_ne : w ≠ (a : ℂ) := by
      intro hw_eq
      exact haρ_not (hw_eq ▸ hwρ)
    exact
      entireFunction_insertNormalizedFactor_gluedQuotient_product_identity_of_ne
        F Qold g g hF ρ S a ha_not_mem hS0 ha0 hQold_factor hw_ne hwρ
  have hQ_zero : Q 0 = F 0 :=
    entireFunction_insertNormalizedFactor_gluedQuotient_zero
      F Qold g hF a ha0 hQold_zero
  exact Exists.intro Q (And.intro hQ_an (And.intro hQ_product hQ_zero))

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
  exact
    if haρ : ‖(a : ℂ)‖ ≤ ρ then
      have hlocal_div :
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
      entireFunction_insertNormalizedFactor_glue_localDivision
        F Qold g hF ρ hρ S a ha_not_mem hS0 ha0 hg_an hg_ne hg_factor
        hQold_an hQold_factor hQold_zero hlocal_div
    else
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
  exact
    match hlocal_a with
    | Exists.intro g hg =>
        match hS with
        | Exists.intro Qold hQold =>
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

end
end LFunctions
end Boundary
