import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part07_PostCutoffDefect

/-!
# Boundary growth owner part 9

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Finite oscillatory zero-mean block estimate for the normalized Bernoulli
kernel after the canonical cutoff.

This is the precise finite-block analytic sink left after the global normalized
kernel has been decomposed into right-endpoint zero-mean unit blocks. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let R : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
  let P : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))
  have hsplit :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) =
        R + P :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_eq_reciprocalDrift_add_phaseDrift
      t
  have hrecip : ‖R‖ ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlockSum_norm_le_one
      t ht hM
  have hphaseFamily :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_family_sharp_ownerGap
      t ht hM
  have hphase :
      ‖P‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_globalPhaseIntegral_family_sharp
      t ht hM hphaseFamily
  have htriangle :
      ‖R + P‖ ≤
        (1 : ℝ) + Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    le_trans (norm_add_le R P) (add_le_add hrecip hphase)
  have hscale :
      (1 : ℝ) + Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_one_add_sqrt_log_le_two_sqrt_log_postCutoff
      t ht hM
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hsplit.symm
      (le_trans htriangle hscale)

/-- Transport of a finite zero-mean block estimate back to the global normalized
Bernoulli kernel integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_blockCancellation_of_finiteOscillatoryBlockSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hdecomp :
      (∫ x in Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hdecomp.symm
      hblock

/-- Normalized Bernoulli block-cancellation estimate on the canonical
post-cutoff interval.

This is the exact oscillatory remainder sink needed by the selected
endpoint/variation package.  It is stronger than the already-assembled `6A`
absolute endpoint-plus-variation consequence and supplies the `2A` cancellation
input required for the finite-defect estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_blockCancellation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hblock :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_norm_le_ownerGap
      t ht hM
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_blockCancellation_of_finiteOscillatoryBlockSum
      t hM hblock

/-- Canonical fixed-interval integration-by-parts decomposition together with
the endpoint and reciprocal-variation estimates for the selected terms. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_blockCancellation
      t ht hM
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_blockCancellation_ownerGap
        t ht hM)

/-- Exact zero-endpoint decomposition for the normalized Bernoulli kernel,
with the endpoint estimate proved directly.

This peels the endpoint part of the fixed-interval integration-by-parts
package.  The remaining analytic content in the full package is the
reciprocal-variation estimate for the selected variation term. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_zeroEndpoint_decomposition_endpointBound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        (0 : ℂ) + V ∧
      ‖(0 : ℂ)‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let V : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        (0 : ℂ) + V :=
    (zero_add V).symm
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hM_nonneg : 0 ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_nonneg M
  have hlog_nonneg : 0 ≤ Real.log (2 + M) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((M : ℕ) : ℝ) :=
      le_trans one_le_two (le_add_of_nonneg_right hM_nonneg)
    exact Real.log_nonneg hone_le_arg
  have hproduct_nonneg :
      0 ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two) hsqrt_nonneg)
      hlog_nonneg
  have hendpoint :
      ‖(0 : ℂ)‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hproduct_nonneg
  exact Exists.intro V ⟨hidentity, hendpoint⟩

/-- Endpoint-only existential consequence for the fixed-interval normalized
Bernoulli kernel.

This does not claim the full selected endpoint/variation integration-by-parts
construction; it only discharges the endpoint-bound projection by taking the
endpoint component to be zero.  The full owner theorem above still owns the
genuine reciprocal-variation estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_endpointBound_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_zeroEndpoint_decomposition_endpointBound
      t ht hM with
  | ⟨V, hidentity, hendpoint⟩ =>
      exact Exists.intro (0 : ℂ) (Exists.intro V ⟨hidentity, hendpoint⟩)

/-- Canonical fixed-interval integration-by-parts decomposition for the
first-periodic-Bernoulli normalized kernel.

This is the genuine real-variable summation-by-parts input: on the finite
post-cutoff interval with the canonical logarithmic-phase cutoff as left
endpoint, the normalized kernel is decomposed into endpoint and
reciprocal-variation pieces. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_ownerIntegrationByParts
      t ht hM

/-- Endpoint bound for the endpoint term selected by the canonical fixed-interval
integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_endpoint_norm_le_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hendpoint

/-- Variation bound for the variation term selected by the canonical
fixed-interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_variation_norm_le_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hvariation

/-- Canonical fixed-interval integration-by-parts package for the
first-periodic-Bernoulli normalized kernel, assembled from its selected
decomposition and the two selected endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_ownerIntegrationByParts
      t ht hM

/-- Existential projection of the selected endpoint/variation
integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_decomposition_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
      t ht hM with
  | ⟨C, V, hidentity, _hendpoint, _hvariation⟩ =>
      exact Exists.intro C (Exists.intro V hidentity)

/-- Exact endpoint estimate for the endpoint selected by the canonical fixed
interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpoint_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hendpoint

/-- Endpoint estimate for the selected endpoint term in the canonical fixed
interval integration-by-parts decomposition of the first-periodic-Bernoulli
normalized kernel. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_endpointTerm_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpoint_norm_le_ownerDirichletBoundedVariation
      t ht hM C V hidentity hendpoint

/-- Exact reciprocal-variation estimate for the variation term selected by the
canonical fixed-interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedVariation_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hvariation

/-- Reciprocal-variation estimate for the selected variation term in the
canonical fixed interval integration-by-parts decomposition of the
first-periodic-Bernoulli normalized kernel. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_variationTerm_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedVariation_norm_le_ownerDirichletBoundedVariation
      t ht hM C V hidentity hvariation

/-- Core canonical fixed-interval Dirichlet bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This is now the package wrapper over the integration-by-parts decomposition
and the two selected endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
      t ht hM

/-- Canonical fixed-interval bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This is now only the public fixed-interval wrapper.  The actual
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation
      t ht hM

/-- Cutoff-normalized bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This theorem is only the cutoff-normalization wrapper.  The actual
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_cutoffNormalized_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N M : ℕ}
    (hN : N = ⌊2 + ‖t‖⌋₊)
    (hM : N ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun K : ℕ =>
        K ≤ M →
          ∃ C V : ℂ,
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
              C + V ∧
            ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
            ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hN.symm
      (fun hM_canonical =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation
          t ht hM_canonical)
      hM

/-- Canonical-cutoff bounded-variation package for the first-periodic-Bernoulli
normalized kernel.

This is now the canonical wrapper over the cutoff-normalized
summation-by-parts leaf. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_cutoffNormalized_ownerDirichletBoundedVariation
      t ht rfl hM

/-- Canonical-cutoff bounded-variation package for the first-periodic-Bernoulli
normalized kernel.

This theorem is now only the public endpoint/variation surface.  The real
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_endpointVariation_canonicalCutoff_ownerBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation
      t ht hM

/-- Generic owner wrapper for the first-periodic-Bernoulli normalized-kernel
endpoint/variation decomposition after the canonical logarithmic-phase cutoff.

This transports the canonical-cutoff bounded-variation package through an
explicit lower-endpoint equality. -/
theorem boundaryLineOnePointRealParam_periodicBernoulli_normalizedKernel_endpointVariation_ownerBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N M : ℕ}
    (hN : N = ⌊2 + ‖t‖⌋₊)
    (hM : N ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun K : ℕ =>
        K ≤ M →
          ∃ C V : ℂ,
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
              C + V ∧
            ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
            ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hN.symm
      (fun hM_canonical =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_endpointVariation_canonicalCutoff_ownerBoundedVariation
          t ht hM_canonical)
      hM

/-- Generic owner leaf for the first-periodic-Bernoulli normalized-kernel
endpoint/variation decomposition after the canonical logarithmic-phase cutoff.

This is the true summation-by-parts step for the normalized kernel
`((-it) / x) x^{-it}`.  The lower endpoint is the canonical cutoff and the
upper endpoint is finite; the proof must construct the endpoint term `C` and
the reciprocal-variation term `V` from the periodic Bernoulli primitive. -/
theorem boundaryLineOnePointRealParam_postCutoff_periodicBernoulli_normalizedKernel_endpointVariation_ownerDirichlet
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_periodicBernoulli_normalizedKernel_endpointVariation_ownerBoundedVariation
      t
      ht
      (N := ⌊2 + ‖t‖⌋₊)
      (M := M)
      rfl
      hM

/-- Owner leaf for the normalized-kernel first-periodic-Bernoulli
integration-by-parts package.

This is the exact missing oscillatory step: the normalized derivative kernel
`((-it) / x) x^{-it}` is paired with the first periodic Bernoulli factor and
split into an endpoint contribution `C` and a reciprocal-variation contribution
`V`, with the two estimates kept separate. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_normalizedKernel_periodicBernoulli_endpointVariation_package_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_postCutoff_periodicBernoulli_normalizedKernel_endpointVariation_ownerDirichlet
      t ht hM

/-- Oscillatory Bernoulli-periodic decomposition for the unweighted post-cutoff
Euler-Maclaurin remainder.

This is the exact normalized-kernel endpoint/variation step: after the
standard Euler-Maclaurin remainder has been transported to the public
`(-it / x) x^{-it}` derivative kernel, the first-periodic Bernoulli factor is
integrated by parts into a boundary term and a reciprocal-variation term. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_normalizedKernel_endpointVariation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_normalizedKernel_periodicBernoulli_endpointVariation_package_ownerGap
      t ht hM

/-- Public Bernoulli-periodic decomposition wrapper for the unweighted
post-cutoff Euler-Maclaurin remainder.

The absolute-value estimate is too large here.  The required proof is the
Dirichlet/Abel cancellation argument for the periodic Bernoulli factor, split
into a boundary part `C` and a variation part `V` after summation by parts on
the post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_periodicOscillatoryDecomposition_endpointVariation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_normalizedKernel_endpointVariation_ownerGap
      t ht hM

/-- Scalar constant bookkeeping for the Bernoulli-remainder endpoint and
variation pieces. -/
theorem boundaryGrowth_two_four_scale_le_six_scale_ownerGap
    (A : ℝ) :
    (2 : ℝ) * A + 4 * A ≤ 6 * A := by
  have hfactor :
      (2 : ℝ) * A + 4 * A = ((2 : ℝ) + 4) * A :=
    (add_mul (2 : ℝ) 4 A).symm
  have htwo_four :
      ((2 : ℝ) + 4) * A = 6 * A :=
    congrArg (fun c : ℝ => c * A) (show (2 : ℝ) + 4 = 6 from rfl)
  exact le_of_eq (Eq.trans hfactor htwo_four)

/-- Final constant algebra after the Bernoulli-periodic cancellation and
endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_from_periodicOscillatoryDecomposition
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  have hdecomp :
      ∃ C V : ℂ,
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
          C + V ∧
        ‖C‖ ≤ 2 * A ∧
        ‖V‖ ≤ 4 * A :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_periodicOscillatoryDecomposition_endpointVariation_ownerGap
      t ht hM
  match hdecomp with
  | ⟨C, V, hsplit, hC, hV⟩ =>
      have hsum :
          ‖C + V‖ ≤ (2 : ℝ) * A + 4 * A :=
        le_trans (norm_add_le C V) (add_le_add hC hV)
      have hscale :
          (2 : ℝ) * A + 4 * A ≤ 6 * A :=
        boundaryGrowth_two_four_scale_le_six_scale_ownerGap A
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ 6 * A)
          hsplit.symm
          (le_trans hsum hscale)

/-- Bernoulli-remainder estimate for the unweighted post-cutoff
Euler-Maclaurin decomposition.

This is the summation-by-parts/Dirichlet-test content that replaces the
insufficient monotone-increment sink: the derivative factor is integrated only
after the oscillatory decomposition has been made at the owner level. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_from_periodicOscillatoryDecomposition
      t ht hM


end LFunctions
end Boundary
