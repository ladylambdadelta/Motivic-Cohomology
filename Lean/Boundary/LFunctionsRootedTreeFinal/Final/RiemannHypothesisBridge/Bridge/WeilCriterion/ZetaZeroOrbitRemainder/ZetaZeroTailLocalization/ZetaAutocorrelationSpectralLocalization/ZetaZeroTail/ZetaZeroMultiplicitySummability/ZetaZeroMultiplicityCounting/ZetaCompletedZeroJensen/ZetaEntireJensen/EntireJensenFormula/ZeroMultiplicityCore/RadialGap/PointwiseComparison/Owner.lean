import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.RadialGap.OriginContribution.Owner

/-!
# Jensen radial-gap multiplicity core

This owner layer was split from `ZeroMultiplicityCore.RadialGap.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- A nonzero zero in `closedDisk R` contributes at least its multiplicity times
`log 2` to the doubled-radius Jensen radial-gap sum.

This is the pointwise radial-gap comparison; it is independent of Jensen's
formula itself. -/
theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) = 0) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z = 0 := by
  change
    (if (z : ℂ) = 0 then
      0
    else
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) = 0
  exact if_pos hz₀

theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_closedDisk_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) ≠ 0)
    (hz_disk : ‖(z : ℂ)‖ ≤ R) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z =
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) := by
  change
    (if (z : ℂ) = 0 then
      0
    else
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) =
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  have hclosed :
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) := by
    change
      (if ‖(z : ℂ)‖ ≤ R then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
      else
        0) =
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
    exact if_pos hz_disk
  calc
    (if (z : ℂ) = 0 then
      0
    else
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)
        = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := if_neg hz₀
    _ = (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) := hclosed

theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_not_closedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) ≠ 0)
    (hz_disk : ¬ ‖(z : ℂ)‖ ≤ R) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z = 0 := by
  change
    (if (z : ℂ) = 0 then
      0
    else
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) = 0
  have hclosed_zero :
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z = 0 := by
    change
      (if ‖(z : ℂ)‖ ≤ R then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
      else
        0) = 0
    exact if_neg hz_disk
  calc
    (if (z : ℂ) = 0 then
      0
    else
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)
        = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := if_neg hz₀
    _ = 0 := hclosed_zero

theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_subset_closedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F)
    (hz :
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z ≠ 0) :
    ‖(z : ℂ)‖ ≤ R := by
  match (inferInstance : Decidable ((z : ℂ) = 0)) with
  | isTrue hz₀ =>
      exact False.elim
        (hz (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_eq_zero
          F hF z hz₀))
  | isFalse hz₀_ne =>
      match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
      | isTrue hclosed => exact hclosed
      | isFalse hnot =>
          exact False.elim
            (hz
              (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_not_closedDisk
                F hF z hz₀_ne hnot))

theorem entireFunctionJensenRadialGapSummand_support_subset_closedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {ρ : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz :
      entireFunctionJensenRadialGapSummand F hF ρ z ≠ 0) :
    ‖(z : ℂ)‖ < ρ := by
  match (inferInstance : Decidable ((z : ℂ) = 0)) with
  | isTrue hz₀ =>
      exact False.elim
        (hz (by
          change (if h : (z : ℂ) = 0 then 0 else
            if ‖(z : ℂ)‖ < ρ then
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log (ρ / ‖(z : ℂ)‖)
            else
              0) = 0
          exact dif_pos hz₀))
  | isFalse hz₀_ne =>
      match (inferInstance : Decidable (‖(z : ℂ)‖ < ρ)) with
      | isTrue hlt => exact hlt
      | isFalse hnot =>
          exact False.elim
            (hz (by
              change (if h : (z : ℂ) = 0 then 0 else
                if ‖(z : ℂ)‖ < ρ then
                  (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                    Real.log (ρ / ‖(z : ℂ)‖)
                else
                  0) = 0
              exact Eq.trans (dif_neg hz₀_ne) (if_neg hnot)))

/-- The radial-gap summand vanishes at the origin. -/
theorem entireFunctionJensenRadialGapSummand_eq_zero_of_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {ρ : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) = 0) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  change (if h : (z : ℂ) = 0 then 0 else
    if ‖(z : ℂ)‖ < ρ then
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖)
    else
      0) = 0
  exact dif_pos hz₀

theorem entireFunctionJensenRadialGapSummand_support_subset_nonzeroClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {ρ : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz :
      entireFunctionJensenRadialGapSummand F hF ρ z ≠ 0) :
    (z : ℂ) ≠ 0 ∧ ‖(z : ℂ)‖ < ρ := by
  have hlt := entireFunctionJensenRadialGapSummand_support_subset_closedDisk F hF z hz
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (entireFunctionJensenRadialGapSummand_eq_zero_of_zero F hF z hzero)
  exact ⟨hz0, hlt⟩

theorem entireFunctionJensenRadialGapSummand_eq_mul_log_of_lt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {ρ : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) ≠ 0)
    (hzlt : ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z =
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖) := by
  change (if h : (z : ℂ) = 0 then 0 else
    if ‖(z : ℂ)‖ < ρ then
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖)
    else
      0) =
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
      Real.log (ρ / ‖(z : ℂ)‖)
  exact Eq.trans (dif_neg hz₀) (if_pos hzlt)

theorem entireFunctionJensenRadialGapSummand_eq_zero_of_not_lt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {ρ : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz₀ : (z : ℂ) ≠ 0)
    (hznot : ¬ ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  change (if h : (z : ℂ) = 0 then 0 else
    if ‖(z : ℂ)‖ < ρ then
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖)
    else
      0) = 0
  exact Eq.trans (dif_neg hz₀) (if_neg hznot)

theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_mul_log_two_le_radialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < 2 * R)]
    (hR : 1 ≤ R)
    (z : EntireFunctionZero F) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z * Real.log 2 ≤
      entireFunctionJensenRadialGapSummand F hF (2 * R) z := by
  match (inferInstance : Decidable ((z : ℂ) = 0)) with
  | isTrue hz₀ =>
    have hleft :
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z * Real.log 2 = 0 := by
      calc
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z * Real.log 2
            = 0 * Real.log 2 := by
              exact congrArg (fun t : ℝ => t * Real.log 2)
                (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_eq_zero
                  F hF z hz₀)
        _ = 0 := zero_mul (Real.log 2)
    have hright :
        entireFunctionJensenRadialGapSummand F hF (2 * R) z = 0 :=
      entireFunctionJensenRadialGapSummand_eq_zero_of_zero F hF z hz₀
    calc
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z * Real.log 2
          = 0 := hleft
      _ ≤ 0 := le_rfl
      _ = entireFunctionJensenRadialGapSummand F hF (2 * R) z := hright.symm
  | isFalse hz₀ =>
    match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
    | isTrue hz_disk =>
      have hgap :
          Real.log 2 ≤ Real.log ((2 * R) / ‖(z : ℂ)‖) :=
        log_two_le_log_doubled_radius_div_norm hR hz₀ hz_disk
      have hstrict : ‖(z : ℂ)‖ < 2 * R := by
        have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
        have hR_lt_twoR : R < 2 * R :=
          radius_lt_doubled_radius_of_pos hR_pos
        exact lt_of_le_of_lt hz_disk hR_lt_twoR
      have hmult :
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log 2 ≤
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hgap
          (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF (z : ℂ)))
      have hleft :
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
              Real.log 2 =
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log 2 := by
        exact congrArg (fun t : ℝ => t * Real.log 2)
          (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_closedDisk_of_ne_zero
            F hF z hz₀ hz_disk)
      have hright :
          entireFunctionJensenRadialGapSummand F hF (2 * R) z =
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖) := by
        exact entireFunctionJensenRadialGapSummand_eq_mul_log_of_lt
          F hF z hz₀ hstrict
      calc
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
            Real.log 2 =
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log 2 := hleft
        _ ≤ (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖) := hmult
        _ = entireFunctionJensenRadialGapSummand F hF (2 * R) z :=
          hright.symm
    | isFalse hz_disk =>
      match (inferInstance : Decidable (‖(z : ℂ)‖ < 2 * R)) with
      | isTrue hstrict =>
        have hnonneg :
            0 ≤ (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) :=
          Nat.cast_nonneg _
        have hlog_nonneg :
            0 ≤ Real.log ((2 * R) / ‖(z : ℂ)‖) := by
          exact Real.log_nonneg (by
            have hz_norm_pos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz₀
            exact (one_le_div₀ hz_norm_pos).mpr hstrict.le)
        have hmult :
            0 ≤ (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log ((2 * R) / ‖(z : ℂ)‖) :=
          mul_nonneg hnonneg hlog_nonneg
        have hleft :
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
                Real.log 2 = 0 := by
          calc
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
                Real.log 2 = 0 * Real.log 2 := by
                  exact congrArg (fun t : ℝ => t * Real.log 2)
                    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_not_closedDisk
                      F hF z hz₀ hz_disk)
            _ = 0 := zero_mul (Real.log 2)
        have hright :
            entireFunctionJensenRadialGapSummand F hF (2 * R) z =
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖) := by
          exact entireFunctionJensenRadialGapSummand_eq_mul_log_of_lt
            F hF z hz₀ hstrict
        calc
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
              Real.log 2 = 0 := hleft
          _ ≤ (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log ((2 * R) / ‖(z : ℂ)‖) := hmult
          _ = entireFunctionJensenRadialGapSummand F hF (2 * R) z :=
            hright.symm
      | isFalse hstrict =>
        have hleft :
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
                Real.log 2 = 0 := by
          calc
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
                Real.log 2 = 0 * Real.log 2 := by
                  exact congrArg (fun t : ℝ => t * Real.log 2)
                    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_not_closedDisk
                      F hF z hz₀ hz_disk)
            _ = 0 := zero_mul (Real.log 2)
        have hright :
            entireFunctionJensenRadialGapSummand F hF (2 * R) z = 0 := by
          exact entireFunctionJensenRadialGapSummand_eq_zero_of_not_lt
            F hF z hz₀ hstrict
        calc
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
              Real.log 2 = 0 := hleft
          _ ≤ 0 := le_rfl
          _ = entireFunctionJensenRadialGapSummand F hF (2 * R) z :=
            hright.symm


end
end LFunctions
end Boundary
