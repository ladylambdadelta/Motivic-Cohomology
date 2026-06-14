import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.Owner

/-!
# Boundary-log assembly for Jensen formula

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem entireFunction_zeroFreeOnClosedDisk_boundaryLogAverage_eq_origin_log_norm_ownerRoot
    (Q : ℂ → ℂ)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
      Real.log ‖Q 0‖ := by
  rcases
      entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
        Q hρ hQ_an hzero
      with ⟨L, hL_an, hL_log⟩
  have hboundary :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) := by
    exact congrArg
      (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
      (by
        apply intervalIntegral.integral_congr
        intro θ hθ
        have hcircle_norm :
            ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ ≤ ρ := by
          have hρ_nonneg : 0 ≤ ρ :=
            le_trans zero_le_one hρ
          have hnorm_eq : ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ρ := by
            calc
              ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
                  ‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
                exact norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I))
              _ = ρ * ‖Complex.exp (θ * Complex.I)‖ := by
                exact congrArg
                  (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
                  (Complex.norm_ofReal_of_nonneg hρ_nonneg)
              _ = ρ * 1 := by
                exact congrArg (fun x : ℝ => ρ * x)
                  (Complex.norm_exp_ofReal_mul_I θ)
              _ = ρ := by
                exact mul_one ρ
          exact le_of_eq hnorm_eq
        exact
          (entireFunction_analyticLogBranch_re_eq_log_norm
            Q L hcircle_norm hL_log).symm)
  have hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
        (L 0).re :=
    entireFunction_analyticLog_re_holomorphicMeanValue_circle
      L hρ hL_an
  have hcenter :
      (L 0).re = Real.log ‖Q 0‖ :=
    entireFunction_analyticLogBranch_center_re_eq_log_norm
      Q L hρ hL_log
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) :=
      hboundary
    _ = (L 0).re := hmean
    _ = Real.log ‖Q 0‖ := hcenter

/-- Origin normalization for any removable quotient whose closed-disk
factorization is normalized by the finite product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_origin_log_norm_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) :
    Real.log ‖Q 0‖ = Real.log ‖F 0‖ := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hρ_origin : ‖(0 : ℂ)‖ ≤ ρ := by
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ ρ)
        (norm_zero : ‖(0 : ℂ)‖ = 0).symm
        hρ_nonneg
  have hfactor_origin :
      F 0 =
        Q 0 *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ 0 :=
    hfactor 0 hρ_origin
  have hproduct_origin :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ 0 = 1 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
      F hF hF0 ρ
  have hQ_origin : Q 0 = F 0 := by
    calc
      Q 0 = Q 0 * 1 :=
        (mul_one (Q 0)).symm
      _ =
          Q 0 *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ 0 :=
        congrArg (fun x : ℂ => Q 0 * x) hproduct_origin.symm
      _ = F 0 :=
        hfactor_origin.symm
  exact congrArg (fun x : ℝ => Real.log x) (congrArg norm hQ_origin)

/-- Radial-support boundary logarithm comparison for an already zero-free
quotient.

This theorem does not construct a radial-support quotient that is zero-free on
the closed disk.  It only records the radial-factor boundary formula under the
explicit hypotheses `hfactor` and `hzero`; the owner construction of a
zero-free closed-disk quotient now lives in the closed-support package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
      F hF hF0 ρ hρ
  have horigin :
      Real.log ‖Q 0‖ = Real.log ‖F 0‖ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_origin_log_norm_ownerRoot
      F Q hF hF0 ρ hρ hfactor
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact hboundary
    _ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact
        congrArg
          (fun x : ℝ =>
            x +
              (∑ z in
                entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
                  F hF hF0 ρ,
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                  ((2 * Real.pi)⁻¹ *
                    (∫ θ in (0 : ℝ)..(2 * Real.pi),
                      Real.log
                        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))))
          horigin.symm

/-- Pointwise logarithm of a finite product of nonzero complex factors.

This is the algebraic product-log identity used after the finite boundary
exception set has removed every vanishing boundary factor. -/
theorem finiteComplexProduct_log_norm_eq_sum_log_norm_of_nonzero
    {ι : Type*}
    (S : Finset ι)
    (f : ι → ℂ)
    (hf : ∀ i : ι, i ∈ S → f i ≠ 0) :
    Real.log ‖∏ i in S, f i‖ =
      ∑ i in S, Real.log ‖f i‖ := by
  refine Finset.induction_on S ?base ?step
  · calc
      Real.log ‖∏ i in (∅ : Finset ι), f i‖ = Real.log ‖(1 : ℂ)‖ := by
        rfl
      _ = 0 := by
        exact Real.log_one
      _ = ∑ i in (∅ : Finset ι), Real.log ‖f i‖ := by
        rfl
  · intro a S ha_not_mem ih
    have ha_ne : f a ≠ 0 :=
      hf a (Finset.mem_insert.2 (Or.inl rfl))
    have hS_ne : ∀ i : ι, i ∈ S → f i ≠ 0 := by
      intro i hi
      exact hf i (Finset.mem_insert.2 (Or.inr hi))
    have hprod_ne : (∏ i in S, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hS_ne
    have hnorm_a_ne : ‖f a‖ ≠ 0 :=
      norm_ne_zero_iff.mpr ha_ne
    have hnorm_prod_ne : ‖∏ i in S, f i‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hprod_ne
    calc
      Real.log ‖∏ i in insert a S, f i‖ =
          Real.log ‖f a * ∏ i in S, f i‖ := by
        exact congrArg (fun x : ℂ => Real.log ‖x‖)
          (Finset.prod_insert ha_not_mem)
      _ = Real.log (‖f a‖ * ‖∏ i in S, f i‖) := by
        exact congrArg Real.log (norm_mul (f a) (∏ i in S, f i))
      _ = Real.log ‖f a‖ + Real.log ‖∏ i in S, f i‖ := by
        exact Real.log_mul hnorm_a_ne hnorm_prod_ne
      _ = Real.log ‖f a‖ + ∑ i in S, Real.log ‖f i‖ := by
        exact congrArg (fun x : ℝ => Real.log ‖f a‖ + x) (ih hS_ne)
      _ = ∑ i in insert a S, Real.log ‖f i‖ := by
        exact (Finset.sum_insert ha_not_mem).symm

/-- Pointwise closed-support factor product-log identity away from boundary
exceptions.

At a parameter where every extracted closed-support boundary factor is
nonzero, the logarithm of the closed-support finite product is the finite sum
of the logarithms of its normalized factors, with multiplicity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorProduct_pointwise_of_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (θ : ℝ)
    (hfactor_ne :
      ∀ z : EntireFunctionZero F,
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ →
        1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ)) ≠ 0) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ
  let sample : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I)
  let factor : EntireFunctionZero F → ℂ :=
    fun z => (1 - sample / (z : ℂ)) ^
      entireFunctionZeroMultiplicity F hF (z : ℂ)
  have hfactor_nonzero : ∀ z : EntireFunctionZero F, z ∈ S → factor z ≠ 0 := by
    intro z hz
    exact
      pow_ne_zero
        (entireFunctionZeroMultiplicity F hF (z : ℂ))
        (hfactor_ne z hz)
  have hproduct_log :
      Real.log ‖∏ z in S, factor z‖ =
        ∑ z in S, Real.log ‖factor z‖ :=
    finiteComplexProduct_log_norm_eq_sum_log_norm_of_nonzero
      S factor hfactor_nonzero
  have hsummand :
      ∀ z : EntireFunctionZero F,
        z ∈ S →
          Real.log ‖factor z‖ =
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ‖1 - sample / (z : ℂ)‖ := by
    intro z _hz
    calc
      Real.log ‖factor z‖ =
          Real.log (‖1 - sample / (z : ℂ)‖ ^
            entireFunctionZeroMultiplicity F hF (z : ℂ)) := by
        exact congrArg Real.log
          (norm_pow
            (1 - sample / (z : ℂ))
            (entireFunctionZeroMultiplicity F hF (z : ℂ)))
      _ =
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log ‖1 - sample / (z : ℂ)‖ := by
        exact Real.log_pow
          ‖1 - sample / (z : ℂ)‖
          (entireFunctionZeroMultiplicity F hF (z : ℂ))
  calc
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
            F hF hF0 ρ ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log ‖∏ z in S, factor z‖ := by
      rfl
    _ = ∑ z in S, Real.log ‖factor z‖ :=
      hproduct_log
    _ =
        ∑ z in S,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log ‖1 - sample / (z : ℂ)‖ := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      exact hsummand z hz
    _ =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖ := by
      rfl

/-- Finiteness of boundary exception parameters for one normalized factor. -/
theorem entireFunction_normalizedSingleFactor_boundaryExceptionParameters_finite
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ : 0 < ρ) :
    Set.Finite
      {θ : ℝ |
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) ∧
          1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) = 0} := by
  let G : ℂ → ℂ := fun w => 1 - w / a
  have hG : ∀ w : ℂ, AnalyticAt ℂ G w := by
    intro w
    dsimp [G]
    exact analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hnontrivial : ∃ w : ℂ, G w ≠ 0 := by
    refine ⟨0, ?_⟩
    dsimp [G]
    exact sub_ne_zero.mpr one_ne_zero
  have hzeros : Set.Finite {w : ℂ | ‖w‖ = ρ ∧ G w = 0} :=
    entireFunction_finite_circle_zeros G hG hnontrivial ρ
  have hρ_nonneg : 0 ≤ ρ :=
    hρ.le
  have hfiniteQuotient :
      (entireFunctionJensenQuotientBoundaryZeroParameters G ρ).Finite :=
    entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
      G ρ hρ_nonneg
      (entireFunction_boundaryCircleParam_injectiveOn_Ioc hρ)
      hzeros
  refine hfiniteQuotient.subset ?_
  intro θ hθ
  have hθ_uIcc : θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) :=
    Set.uIoc_subset_uIcc hθ.1
  have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have hle : (0 : ℝ) ≤ 2 * Real.pi :=
      mul_nonneg zero_le_two Real.pi_pos.le
    exact Eq.subst
      (motive := fun s : Set ℝ => θ ∈ s)
      (Set.uIcc_of_le hle)
      hθ_uIcc
  exact ⟨hθ_Icc, hθ.2⟩

/-- Finiteness of the exact interval-scoped exception parameters for the
closed-support product.

The set is the honest parameter set where at least one extracted closed-disk
factor vanishes on the boundary circle.  The proof is the standard finite
preimage argument: for each support point the boundary parametrization is
injective on the fundamental arc, with the endpoint handled by adjoining `0`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryExceptionParameters_finite_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    Set.Finite
      {θ : ℝ |
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) ∧
          ∃ z : EntireFunctionZero F,
            z ∈
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ ∧
              1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ)) = 0} := by
  let S : Finset (EntireFunctionZero F) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
      F hF hF0 ρ
  let E : EntireFunctionZero F → Set ℝ :=
    fun z =>
      {θ : ℝ |
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) ∧
          1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ)) = 0}
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hEfinite : ∀ z : EntireFunctionZero F, z ∈ (S : Set (EntireFunctionZero F)) →
      (E z).Finite := by
    intro z hz
    have hzS : z ∈ S := hz
    have hz0 : (z : ℂ) ≠ 0 :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
        F hF hF0 ρ z hzS
    exact
      entireFunction_normalizedSingleFactor_boundaryExceptionParameters_finite
        hz0 hρ_pos
  have hfiniteUnion : (⋃ z ∈ (S : Set (EntireFunctionZero F)), E z).Finite :=
    S.finite_toSet.biUnion hEfinite
  refine hfiniteUnion.subset ?_
  intro θ hθ
  rcases hθ.2 with ⟨z, hz, hzvanish⟩
  exact Set.mem_biUnion hz ⟨hθ.1, hzvanish⟩

/-- Interval-scoped boundary exception set for closed-support factors.

This constructs the finite set of parameters in the fundamental interval where
some extracted closed-support factor vanishes.  Away from this set, every
factor in the closed-support product is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryExceptionSet_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ E : Finset ℝ,
      ∀ θ : ℝ,
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
        θ ∉ E →
          ∀ z : EntireFunctionZero F,
            z ∈
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ →
            1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ)) ≠ 0 := by
  let Eset : Set ℝ :=
    {θ : ℝ |
      θ ∈ Ι (0 : ℝ) (2 * Real.pi) ∧
        ∃ z : EntireFunctionZero F,
          z ∈
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ ∧
            1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ)) = 0}
  have hfinite : Eset.Finite :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryExceptionParameters_finite_ownerRoot
      F hF hF0 ρ hρ
  refine ⟨hfinite.toFinset, ?_⟩
  intro θ hθI hθnot z hz hvanish
  have hθEset : θ ∈ Eset :=
    ⟨hθI, ⟨z, hz, hvanish⟩⟩
  have hθE : θ ∈ hfinite.toFinset :=
    hfinite.mem_toFinset.2 hθEset
  exact hθnot hθE

/-- Pointwise product-log identity after removing the interval-scoped boundary
exception set. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_pointwise_from_exceptionSet_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    ∃ E : Finset ℝ,
      ∀ θ : ℝ,
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
        θ ∉ E →
          entireFunctionJensenBoundaryLogIntegrand F ρ θ =
            Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
              (∑ z in
                entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                  F hF hF0 ρ,
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryExceptionSet_ownerRoot
        F hF hF0 ρ hρ with
    ⟨E, hE⟩
  refine ⟨E, ?_⟩
  intro θ hθI hθnot
  let sample : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I)
  let P : ℂ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
      F hF hF0 ρ sample
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hsample_norm : ‖sample‖ = ρ :=
    entireFunctionJensenBoundaryCircle_norm hρ_nonneg
  have hsample_mem : ‖sample‖ ≤ ρ :=
    le_of_eq hsample_norm
  have hQ_ne : Q sample ≠ 0 :=
    hzero sample hsample_mem
  have hfactor_ne :
      ∀ z : EntireFunctionZero F,
        z ∈
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ →
        1 - (sample / (z : ℂ)) ≠ 0 := by
    intro z hz
    exact hE θ hθI hθnot z hz
  have hP_log :
      Real.log ‖P‖ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log ‖1 - (sample / (z : ℂ))‖) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorProduct_pointwise_of_nonzero
      F hF hF0 ρ θ hfactor_ne
  have hP_ne : P ≠ 0 := by
    unfold P
    unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
    exact
      Finset.prod_ne_zero_iff.mpr
        (fun z hz =>
          pow_ne_zero
            (entireFunctionZeroMultiplicity F hF (z : ℂ))
            (hfactor_ne z hz))
  have hnorm_Q_ne : ‖Q sample‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hQ_ne
  have hnorm_P_ne : ‖P‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hP_ne
  have hfactor_sample :
      F sample = Q sample * P :=
    hfactor sample hsample_mem
  calc
    entireFunctionJensenBoundaryLogIntegrand F ρ θ =
        Real.log ‖F sample‖ := by
      rfl
    _ = Real.log ‖Q sample * P‖ := by
      exact congrArg (fun x : ℂ => Real.log ‖x‖) hfactor_sample
    _ = Real.log (‖Q sample‖ * ‖P‖) := by
      exact congrArg Real.log (norm_mul (Q sample) P)
    _ = Real.log ‖Q sample‖ + Real.log ‖P‖ := by
      exact Real.log_mul hnorm_Q_ne hnorm_P_ne
    _ =
        Real.log ‖Q sample‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ‖1 - (sample / (z : ℂ))‖) := by
      exact congrArg (fun x : ℝ => Real.log ‖Q sample‖ + x) hP_log
    _ =
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
      rfl

/-- Pointwise product-log identity away from the finite boundary-exception set.

Off the parameters where a boundary factor vanishes, the closed-support
factorization gives a nonzero product and the logarithm of the norm splits as
the quotient logarithm plus the finite sum of single-factor logarithms. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_pointwise_offException_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    ∃ E : Finset ℝ,
      ∀ θ : ℝ,
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
        θ ∉ E →
          entireFunctionJensenBoundaryLogIntegrand F ρ θ =
            Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
              (∑ z in
                entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                  F hF hF0 ρ,
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_pointwise_from_exceptionSet_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- A.e. boundary product-log congruence from the finite exception set. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_aeEq_from_pointwise_offException_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogIntegrand F ρ =ᵐ[
        MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
  obtain ⟨E, hE⟩ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hnot_mem_volume :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∉ (E : Set ℝ) :=
    E.finite_toSet.countable.ae_not_mem MeasureTheory.volume
  have hnot_mem :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ∉ (E : Set ℝ) :=
    MeasureTheory.ae_restrict_of_ae hnot_mem_volume
  have hmem_interval :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) :=
    MeasureTheory.ae_restrict_mem measurableSet_uIoc
  filter_upwards [hnot_mem, hmem_interval] with θ hθ_not hθ_interval
  exact hE θ hθ_interval hθ_not

/-- Interval-integrability of the closed-support product-log summands with
finite boundary exceptions. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_finiteException_intervalIntegrable_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hF_nontrivial : ∃ z : ℂ, F z ≠ 0 :=
    ⟨0, hF0⟩
  have hzeros : Set.Finite {z : ℂ | ‖z‖ = ρ ∧ F z = 0} :=
    entireFunction_circleZeros_finite F hF hF_nontrivial ρ
  have hF_int :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F ρ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      F hF hF_nontrivial hρ_pos hzeros
  have hae :
      entireFunctionJensenBoundaryLogIntegrand F ρ =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        (fun θ : ℝ =>
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ,
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_aeEq_from_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  exact hF_int.congr hae

/-- Interval-integrability of a single normalized boundary factor.

This is the analytic single-factor sink consumed by the finite product-log
exchange.  It is the finite-log-singularity theorem applied to the entire
function `w ↦ 1 - w / a`; its circle zeros are finite, and the displayed
integrand is definitionally the Jensen boundary logarithmic integrand for that
factor. -/
theorem entireFunction_normalizedSingleFactor_boundaryLog_intervalIntegrable_ownerRoot
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ : 0 < ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log
          ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  let G : ℂ → ℂ := fun w => 1 - w / a
  have hG : ∀ w : ℂ, AnalyticAt ℂ G w := by
    intro w
    dsimp [G]
    exact analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hnontrivial : ∃ w : ℂ, G w ≠ 0 := by
    refine ⟨0, ?_⟩
    dsimp [G]
    exact sub_ne_zero.mpr one_ne_zero
  have hzeros : Set.Finite {w : ℂ | ‖w‖ = ρ ∧ G w = 0} :=
    entireFunction_finite_circle_zeros G hG hnontrivial ρ
  have hInt :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand G ρ)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      G hG hnontrivial hρ hzeros
  exact hInt

/-- Interval-integrability of one closed-support boundary logarithmic factor.

This is the single-factor input for exchanging the finite closed-support sum
with the interval integral.  Interior factors are continuous; boundary factors
have one logarithmic singularity on the fundamental interval and are handled by
the finite logarithmic-singularity API. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  have hz0 : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz
  have hz_norm_le : ‖(z : ℂ)‖ ≤ ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_norm_le
      F hF hF0 ρ z hz
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz0) hz_norm_le
  have hfactor_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_normalizedSingleFactor_boundaryLog_intervalIntegrable_ownerRoot
      hz0 hρ_pos
  exact hfactor_int.const_mul
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)

/-- Finite sum/integral exchange for the closed-support boundary factor sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_sum_integral_exchange_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖ := by
      exact
        intervalIntegral.integral_finset_sum
          (fun z hz =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
              F hF hF0 ρ z hz)
    _ =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
      refine Finset.sum_congr rfl ?_
      intro z _hz
      exact
        intervalIntegral.integral_const_mul
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
          (fun θ : ℝ =>
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)

/-- Finite interval-integrability gluing for a closed-support boundary factor
sum.

This is purely measure-theoretic: a finite sum of interval-integrable
single-factor logarithmic terms is interval-integrable on the same interval. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum_intervalIntegrable_from_singleFactors
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  exact
    IntervalIntegrable.sum
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ)
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
          F hF hF0 ρ z hz)

/-- Interval-integrability of the finite closed-support factor-sum boundary
term. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum_intervalIntegrable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum_intervalIntegrable_from_singleFactors
      F hF hF0 ρ

/-- Quotient boundary logarithm integrability from the product-log a.e. split.

The a.e. identity writes the boundary logarithm of `F` as the quotient
logarithm plus the finite factor-sum logarithm.  Since the left side and the
finite factor sum are interval-integrable, the quotient term is
interval-integrable. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_from_productSplit
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  let q : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖
  let fs : ℝ → ℝ :=
    fun θ : ℝ =>
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖
  have hcombined :
      IntervalIntegrable
        (fun θ : ℝ => q θ + fs θ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_finiteException_intervalIntegrable_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hfs :
      IntervalIntegrable fs MeasureTheory.volume 0 (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum_intervalIntegrable_ownerRoot
      F hF hF0 ρ
  have hdiff :
      IntervalIntegrable
        (fun θ : ℝ => (q θ + fs θ) - fs θ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    hcombined.sub hfs
  have hpoint :
      (fun θ : ℝ => (q θ + fs θ) - fs θ) =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        q :=
    Filter.Eventually.of_forall
      (fun θ : ℝ => add_sub_cancel_right (q θ) (fs θ))
  exact hdiff.congr hpoint

/-- Interval-integrability of the quotient boundary logarithm after the
closed-support product-log split.

The quotient term is obtained from the interval-integrable combined product-log
integrand by subtracting the finite factor-sum term. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_from_productSplit
      F Q hF hF0 ρ hρ hfactor hzero

/-- Pull a fixed scalar into the second factor of a finite real weighted sum. -/
theorem finiteReal_sum_scalar_mul_weighted_integrals
    {ι : Type*}
    (S : Finset ι)
    (c : ℝ)
    (m I : ι → ℝ) :
    c * (∑ i in S, m i * I i) =
      ∑ i in S, m i * (c * I i) := by
  refine Finset.induction_on S ?base ?step
  · calc
      c * (∑ i in (∅ : Finset ι), m i * I i) = c * 0 := by
        exact congrArg (fun x : ℝ => c * x) Finset.sum_empty
      _ = 0 := mul_zero c
      _ = ∑ i in (∅ : Finset ι), m i * (c * I i) := by
        exact Finset.sum_empty.symm
  · intro a S ha_not_mem ih
    have hterm :
        c * (m a * I a) = m a * (c * I a) := by
      calc
        c * (m a * I a) = (c * m a) * I a :=
          (mul_assoc c (m a) (I a)).symm
        _ = (m a * c) * I a := by
          exact congrArg (fun x : ℝ => x * I a) (mul_comm c (m a))
        _ = m a * (c * I a) :=
          mul_assoc (m a) c (I a)
    calc
      c * (∑ i in insert a S, m i * I i) =
          c * (m a * I a + ∑ i in S, m i * I i) := by
        exact congrArg (fun x : ℝ => c * x) (Finset.sum_insert ha_not_mem)
      _ = c * (m a * I a) + c * (∑ i in S, m i * I i) :=
        mul_add c (m a * I a) (∑ i in S, m i * I i)
      _ = m a * (c * I a) + ∑ i in S, m i * (c * I i) := by
        exact congrArg₂ HAdd.hAdd hterm ih
      _ = ∑ i in insert a S, m i * (c * I i) := by
        exact (Finset.sum_insert ha_not_mem).symm

/-- Integral assembly for the closed-support product-log decomposition.

This is the final measure-theoretic step: restricted-a.e. equality replaces the
boundary log of `F` by the quotient term plus the finite factor sum, the
integral of the sum is split, and the finite factor sum is exchanged with the
interval integral. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_integralAssembly_from_aeEq_and_exchange
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let q : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖
  let fs : ℝ → ℝ :=
    fun θ : ℝ =>
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖
  let c : ℝ := (2 * Real.pi)⁻¹
  have hae :
      entireFunctionJensenBoundaryLogIntegrand F ρ =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        (fun θ : ℝ => q θ + fs θ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_aeEq_from_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hq_int :
      IntervalIntegrable q MeasureTheory.volume 0 (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hfs_int :
      IntervalIntegrable fs MeasureTheory.volume 0 (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum_intervalIntegrable_ownerRoot
      F hF hF0 ρ
  have hcongr :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ := by
    exact intervalIntegral.integral_congr_ae hae
  have hadd :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) := by
    exact intervalIntegral.integral_add hq_int hfs_int
  have hexchange :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_sum_integral_exchange_ownerRoot
      F hF hF0 ρ
  have hscale :
      c *
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (c *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) :=
    finiteReal_sum_scalar_mul_weighted_integrals
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ)
      c
      (fun z : EntireFunctionZero F =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ))
      (fun z : EntireFunctionZero F =>
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        c *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F ρ θ) := by
      rfl
    _ = c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ) := by
      exact congrArg (fun x : ℝ => c * x) hcongr
    _ =
        c *
          ((∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
            (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ)) := by
      exact congrArg (fun x : ℝ => c * x) hadd
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          c * (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) := by
      exact mul_add c
        (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ)
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          c *
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ,
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
      exact congrArg
        (fun x : ℝ => c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) + c * x)
        hexchange
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              (c *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact congrArg
        (fun x : ℝ => c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) + x)
        hscale
    _ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Assembly of the closed-support finite-exception product-log integral from
the a.e. pointwise split and the finite sum/integral exchange. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_integralAssembly_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_integralAssembly_from_aeEq_and_exchange
      F Q hF hF0 ρ hρ hfactor hzero

/-- Finite-exception product-log splitting for a closed-support divisor.

This is the analytic integration sink behind the closed-support boundary-log
decomposition.  The proof is pointwise product-log splitting away from the
finite set of boundary parameters where extracted boundary factors vanish,
followed by finite logarithmic-singularity interval-integrability and a.e.
congruence of interval integrals. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_finiteException_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_integralAssembly_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- Closed-support finite-product boundary-log decomposition with finite
boundary exceptions made explicit.

This is the exact product-log sink: restrict the factorization
`F = Q * P_closed` to the boundary circle, split `log ‖Q * P_closed‖` into the
quotient boundary term and the finite sum of extracted single-zero factor
terms, and interchange the finite sum with the interval integral.  Boundary
zeros are allowed: the finitely many singular parameters are handled by
finite-exception interval-integrability and a.e. congruence. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_finiteException_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_finiteException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- Closed-support finite-product boundary-log decomposition before applying
the zero-free quotient mean theorem. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_from_factorization_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_finiteException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- Boundary logarithm decomposition for the closed-disk removable quotient.

This is the correct product form for closed-disk zero-freeness: all nonzero
zeros with `‖z‖ ≤ ρ`, including boundary zeros, have been extracted. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let quotientBoundary : ℝ :=
    (2 * Real.pi)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
  let factorBoundary : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hsplit :
      entireFunctionJensenBoundaryLogAverage F ρ =
        quotientBoundary + factorBoundary :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_from_factorization_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hquotient_mean :
      quotientBoundary = Real.log ‖Q 0‖ :=
    entireFunction_zeroFreeOnClosedDisk_boundaryLogAverage_eq_origin_log_norm_ownerRoot
      Q ρ hρ hQ_an hzero
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        quotientBoundary + factorBoundary := hsplit
    _ = Real.log ‖Q 0‖ + factorBoundary := by
      exact congrArg (fun x : ℝ => x + factorBoundary) hquotient_mean
    _ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Closed-disk product boundary factors split into the radial-gap factors plus
the boundary-zero factors.

Boundary-zero factors are present in the closed-disk quotient but have zero
radial-gap contribution; the final radial assembly must account for them by
this comparison rather than by asserting that they are absent. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_plus_boundaryZeroFactors_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let φ : EntireFunctionZero F → ℝ :=
    fun z =>
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hsplit_set :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ ∪
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_eq_interior_union_boundary
      F hF hF0 ρ
  have hclosed_sum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
              F hF hF0 ρ ∪
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
          φ z) :=
    congrArg (fun s : Finset (EntireFunctionZero F) => ∑ z in s, φ z)
      hsplit_set
  have hdisjoint :
      Disjoint
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
          F hF hF0 ρ)
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ) :=
    Finset.disjoint_left.2
      (fun z hz_int hz_bd =>
        (Finset.mem_filter.1 hz_bd).2 (Finset.mem_filter.1 hz_int).2)
  have hunion_sum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ ∪
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) :=
    Finset.sum_union hdisjoint
  have hinterior_radial :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
          F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) :=
    congrArg (fun s : Finset (EntireFunctionZero F) => ∑ z in s, φ z)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_eq_radialGapSupportFiniteZeroDivisor_ownerRoot
        F hF hF0 ρ)
  calc
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) := by
      rfl
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
              F hF hF0 ρ ∪
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
          φ z) := hclosed_sum
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) := hunion_sum
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) := by
      exact congrArg
        (fun x : ℝ =>
          x +
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
                F hF hF0 ρ,
              φ z))
        hinterior_radial
    _ =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Closed-support boundary-factor sum reduces to the radial-gap factor sum
because the boundary-zero factor sum is zero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  have hsplit :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_plus_boundaryZeroFactors_ownerRoot
      F hF hF0 ρ
  have hboundary_zero :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_boundaryFactorSum_eq_zero
      F hF hF0 ρ
  calc
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact hsplit
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          0 := by
      exact congrArg
        (fun x : ℝ =>
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
            x)
        hboundary_zero
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
      exact add_zero
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))

/-- Removable quotient after extracting the closed-disk Jensen support divisor.

This is the owner-level removable-singularity factor theorem needed by the
closed-disk finite-product Jensen proof.  The quotient is supplied existentially, not by
globally choosing the raw expression `F / P`; at the support zeros the raw
division expression has the wrong value because division sends `0 / 0` to `0`.
The construction removes those singularities with the matched local
multiplicities for all nonzero zeros with `‖z‖ ≤ ρ`, including boundary zeros,
and returns the closed-support boundary decomposition used downstream.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_exists_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      (∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) ∧
      (entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))) ∧
      (Real.log ‖Q 0‖ = Real.log ‖F 0‖) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_extension_ownerRoot
        F hF hF0 ρ hρ
    with ⟨Q, hQ_an, hfactor, horigin_value⟩
  have hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_ownerRoot
      F Q hF hF0 ρ hQ_an hfactor
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
      F Q hF hF0 ρ hρ hQ_an hfactor hzero
  have horigin :
      Real.log ‖Q 0‖ = Real.log ‖F 0‖ :=
    congrArg (fun x : ℝ => Real.log x) (congrArg norm horigin_value)
  exact ⟨Q, hfactor, hzero, hboundary, horigin⟩

/-- Canonical closed-support finite product factorization on Jensen's closed disk.

The quotient is obtained by locally destructing the closed-disk removable
quotient package; no global choice of a raw quotient is made. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      (∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) ∧
      (entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))) ∧
      (Real.log ‖Q 0‖ = Real.log ‖F 0‖) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_exists_ownerRoot
        F hF hF0 ρ hρ with
    ⟨Q, hfactor, hzero, hboundary, horigin⟩
  exact ⟨Q, hfactor, hzero, hboundary, horigin⟩

/-- There is a closed-support removable finite divisor quotient which is
zero-free on Jensen's closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFreeOnClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
        F hF hF0 ρ hρ with
    ⟨Q, _hfactor, hzero, _hboundary, _horigin⟩
  exact ⟨Q, hzero⟩

/-- Radial-gap boundary logarithm decomposition after the closed-support
quotient has been constructed.

This is no longer the zero-free quotient construction itself.  The zero-free
quotient is owned by the closed-disk support package above; this theorem is the
downstream comparison from the closed-support boundary factor sum to the
strictly interior radial-gap support, with boundary-zero factors handled
separately. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖F 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let closedFactors : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  let radialFactors : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  obtain ⟨Q, _hfactor, _hzero, hboundary, horigin⟩ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
      F hF hF0 ρ hρ
  have hclosed_to_radial :
      closedFactors = radialFactors :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_ownerRoot
      F hF hF0 ρ
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ + closedFactors := by
      exact hboundary
    _ = Real.log ‖F 0‖ + closedFactors := by
      exact congrArg (fun x : ℝ => x + closedFactors) horigin
    _ = Real.log ‖F 0‖ + radialFactors := by
      exact congrArg (fun x : ℝ => Real.log ‖F 0‖ + x) hclosed_to_radial
    _ =
      Real.log ‖F 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Origin normalization for the finite quotient in Jensen's product
factorization. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm_from_def
      F hF hF0 ρ

/-- The finite support divisor sum of single-factor boundary averages is the
support finite radial-gap product sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProductRadialGapSum_eq_singleFactorBoundaryAverageSum
      F hF hF0 ρ).symm

/-- Finite-product boundary-average identity over the support divisor.

This is the quotient/product construction in the assembly chain.  Its proof is
the classical finite divisor factorization on the Jensen disk, construction of
the zero-free quotient, analytic-log mean value for the quotient term, boundary
log decomposition into the quotient and the extracted linear factors, and the
finite single-factor average theorem above.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryAverage_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖F 0‖ +
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
      F hF hF0 ρ hρ
  have hsum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
      F hF hF0 ρ
  let S : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hboundaryS :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ + S :=
    hboundary
  have hsumS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    hsum
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ + S := by
      exact hboundaryS
    _ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact congrArg (fun x : ℝ => Real.log ‖F 0‖ + x) hsum

/-- Support-controlled finite-product boundary identity implies the standard
Jensen boundary mean-log identity by replacing the finite support divisor sum
with the infinite radial-gap sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_supportFiniteProduct_boundaryAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ)) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  have hsupport :
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
      F hF hF0 ρ
  calc
    entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact hsupport
    _ =
        (Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ)) -
          Real.log ‖F 0‖ := by
      exact
        (add_sub_cancel_left
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ))
          (Real.log ‖F 0‖)).symm
    _ = entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
      exact congrArg (fun x : ℝ => x - Real.log ‖F 0‖) hboundary.symm

/-- Analytic-log, harmonic mean-value, and single-zero-factor form of the
classical Jensen product theorem.

Proof chain:
finite divisor factorization on the disk -> zero-free quotient admits an
analytic logarithm -> the real part of that logarithm is harmonic -> harmonic
mean value on the boundary circle -> the single zero-factor boundary average
`log (ρ / ‖a‖)` -> finite product sum -> support-controlled `tsum` transport.

This statement keeps the classical analytic heart separate from the already
proved finite support and summability transports in this owner file.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_finiteProductAssembly_from_constituents
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  intro ρ hρ
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_supportFiniteProduct_boundaryAverage
      F hF hF0 ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryAverage_identity_ownerRoot
        F hF hF0 ρ hρ)

/-- Analytic-log, harmonic mean-value, and single-zero-factor form of the
classical Jensen product theorem.

This public theorem is intentionally a thin wrapper over the finite-product
assembly root, after the three analytic constituents have been isolated above. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_analyticLogHarmonicMeanValue_and_zeroFactorCircleAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_finiteProductAssembly_from_constituents
      F hF hF0

/-- Analytic-log/harmonic mean-value form of the classical Jensen product
theorem. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_analyticLogHarmonicMeanValue
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_analyticLogHarmonicMeanValue_and_zeroFactorCircleAverage
      F hF hF0

/-- Classical analytic product/Jensen identity after finite zero-divisor
factorization.

Proof chain represented by this owner root:
finite zero divisor factorization -> zero-free quotient boundary mean-log
identity -> zero factor radial contribution identity -> finite product sum
identity -> Jensen's formula with explicit constant.

This is the genuine classical complex-analytic input: the zero-free quotient
has boundary mean log equal to its value at the origin, while each extracted
linear zero factor contributes `log (ρ / ‖a‖)` to the normalized boundary mean;
cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_analyticLogHarmonicMeanValue
      F hF hF0

/-- Classical Jensen product/radial-gap identity for a nonzero value at the
origin, including the explicit constant.

This is the product formula form of Jensen's theorem: after multiplying the
linear zero factors inside the circle and taking logarithmic boundary averages,
the radial-gap sum differs from the boundary average by exactly
`Real.log ‖F 0‖`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_productRadialGap_identity_explicitConstant_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_ownerRoot
      F hF hF0

/-- Boundary logarithmic integral identity with explicit origin constant,
projected from the classical Jensen product/radial-gap identity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogIntegral_identity_explicitConstant_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_productRadialGap_identity_explicitConstant_ownerRoot
      F hF hF0

/-- Classical Jensen boundary-log-average identity for a nonzero value at the
origin.

This is the exact classical Jensen package in the normalization of this file:
the nonzero closed-disk multiplicity summands are summable, the radial-gap
summands are summable, and the multiplicity-weighted radial gap sum equals the
normalized boundary logarithmic average up to the origin constant
`log ‖F 0‖`; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_explicitConstant_package_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    (∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
    (∀ ρ : ℝ,
      1 ≤ ρ →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) ∧
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖) := by
  refine ⟨?_, ?_⟩
  · exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisor_closedDiskMultiplicitySummable_ownerRoot
        F hF hF0
  · intro ρ hρ
    exact
      ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_from_finiteZeroDivisor_ownerRoot
          F hF hF0 ρ hρ,
        entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogIntegral_identity_explicitConstant_ownerRoot
          F hF hF0 ρ hρ⟩

/-- Classical Jensen package with the origin constant existentially bundled.

The owner theorem above records the constant explicitly as `log ‖F 0‖`; this
wrapper exists only for downstream code that wants a named constant. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_explicitConstant_package_ownerRoot
        F hF hF0 with
    ⟨hclosed, hradial⟩
  refine ⟨Real.log ‖F 0‖, hclosed, ?_⟩
  intro ρ hρ
  rcases hradial ρ hρ with ⟨hsum, hidentity⟩
  refine ⟨hsum, ?_⟩
  calc
    entireFunctionJensenRadialGapSum F hF ρ + Real.log ‖F 0‖ =
        (entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖) +
          Real.log ‖F 0‖ := by
      exact congrArg (fun x : ℝ => x + Real.log ‖F 0‖) hidentity
    _ = entireFunctionJensenBoundaryLogAverage F ρ := by
      exact sub_add_cancel (entireFunctionJensenBoundaryLogAverage F ρ) (Real.log ‖F 0‖)

/-- Boundary-log-average identity projected from the standard Jensen package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogAverage_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ ρ : ℝ,
          1 ≤ ρ →
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨C, _hclosed, hradial⟩
  exact ⟨C, fun ρ hρ => (hradial ρ hρ).2⟩

/-- Closed-disk summability of the nonzero zero-multiplicity summand in the
standard Jensen setting. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummability_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨_C, hclosed, _hradial⟩
  exact hclosed

/-- Radial-gap summability of the Jensen summand in the standard nonzero-origin
setting. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨_C, _hclosed, hradial⟩
  exact fun ρ hρ => (hradial ρ hρ).1

/-- Standard Jensen formula for a nontrivial entire function whose value at the
origin is nonzero.

This package theorem is a thin assembly over the three owner roots: boundary
log-average identity, closed-disk summability, and radial-gap summability. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  match
    entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogAverage_identity_ownerRoot
      F hF hF0 with
  | ⟨C, hboundary⟩ =>
      refine ⟨C, ?_, ?_⟩
      · exact
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummability_ownerRoot
            F hF hF0
      · intro ρ hρ
        exact
          ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_ownerRoot
              F hF hF0 ρ hρ,
            hboundary ρ hρ⟩

/-- Closed-disk multiplicity summability extracted from the standard
nonzero-origin Jensen package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (R : ℝ)
    (hR : 1 ≤ R) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) :=
  hJ.1 R hR

/-- Radial-gap summability extracted from the standard nonzero-origin Jensen
package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z) :=
  (hJ.2 ρ hρ).1

/-- Radial-gap identity extracted from the standard nonzero-origin Jensen
package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenRadialGapSum F hF ρ + C =
      entireFunctionJensenBoundaryLogAverage F ρ :=
  (hJ.2 ρ hρ).2

/-- Classical Jensen formula for a nontrivial entire function whose value at
the origin is nonzero.

This is now a thin assembly theorem over the exact standard Jensen owner root:
the analytic content is isolated in
`entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot`, while this
name preserves the downstream classical-Jensen API. -/
theorem entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  match entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot F hF hF0 with
  | ⟨C, hJ⟩ =>
      refine ⟨C, ?_, ?_⟩
      · intro R hR
        exact
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummable
            F hF hF0 C hJ R hR
      · intro ρ hρ
        exact
          ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummable
              F hF hF0 C hJ ρ hρ,
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
              F hF hF0 C hJ ρ hρ⟩

/-- Classical Jensen formula for a nontrivial entire function whose value at
the origin is nonzero.

This compatibility theorem is intentionally a thin wrapper over
`entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot`; downstream
zero-counting code should depend on this stable public name, while the analytic
proof remains owned by the root theorem above. -/
theorem entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot F hF hF0

/-- The origin-factor transport theorem is mechanical when the origin is not a
zero: the explicit origin Taylor contribution is zero. -/

end
end LFunctions
end Boundary
