import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.BoundaryLogRegularity

/-!
# Boundary product-log assembly for Jensen formula

This owner layer was split from `BoundaryLogAssembly.ProductLogAssembly.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

open scoped Topology

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
      exact Finset.sum_congr rfl (fun z hz => hsummand z hz)
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
    exact analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hnontrivial : ∃ w : ℂ, G w ≠ 0 := by
    have hG0_eq_one : G 0 = 1 := by
      calc
        G 0 = 1 - 0 / a := rfl
        _ = 1 - 0 := congrArg (fun x : ℂ => 1 - x) (zero_div a)
        _ = 1 := sub_zero 1
    exact
      ⟨0,
        fun hG0 =>
          one_ne_zero (Eq.trans hG0_eq_one.symm hG0)⟩
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
  exact
    hfiniteQuotient.subset
      (fun θ hθ =>
        let hθ_uIcc : θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) :=
          Set.uIoc_subset_uIcc hθ.1
        let hle : (0 : ℝ) ≤ 2 * Real.pi :=
          mul_nonneg zero_le_two Real.pi_pos.le
        let hθ_Icc : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
          Eq.subst
            (motive := fun s : Set ℝ => θ ∈ s)
            (Set.uIcc_of_le hle)
            hθ_uIcc
        ⟨hθ_Icc, hθ.2⟩)

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
  exact
    hfiniteUnion.subset
      (fun θ hθ =>
        match hθ.2 with
        | ⟨z, hz, hzvanish⟩ =>
            Set.mem_biUnion hz ⟨hθ.1, hzvanish⟩)

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
  exact
    ⟨hfinite.toFinset,
      fun θ hθI hθnot z hz hvanish =>
        let hθEset : θ ∈ Eset :=
          ⟨hθI, ⟨z, hz, hvanish⟩⟩
        let hθE : θ ∈ hfinite.toFinset :=
          hfinite.mem_toFinset.2 hθEset
        hθnot hθE⟩

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
  match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryExceptionSet_ownerRoot
        F hF hF0 ρ hρ with
  | ⟨E, hE⟩ =>
      exact ⟨E, fun θ hθI hθnot => by
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
            rfl⟩

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
  match
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero with
  | ⟨E, hE⟩ =>
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
      have hboth :
          ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
            θ ∉ (E : Set ℝ) ∧ θ ∈ Ι (0 : ℝ) (2 * Real.pi) :=
        hnot_mem.and hmem_interval
      exact hboth.mono (fun θ hθ => hE θ hθ.2 hθ.1)


end
end LFunctions
end Boundary
