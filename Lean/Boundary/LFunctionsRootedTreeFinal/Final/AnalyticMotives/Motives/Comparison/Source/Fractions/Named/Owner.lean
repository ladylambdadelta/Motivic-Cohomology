import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Owner

/-!
# Named analytic localization-input fraction criteria

This file specializes the comparison-source roof-killing criterion to the six
named analytic localization inputs.  The remaining analytic proof obligations
can therefore mention the concrete generator kind instead of repackaging a
generic `TraceLocalizationInput`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- Descent-channel numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_descentChannel_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.descentChannel_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.descentChannel_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.descentChannel inputSource inputTarget)
      source_eq
      numerator_zero

/-- Descent-refinement numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_descentRefinement_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.descentRefinement_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.descentRefinement_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.descentRefinement inputSource inputTarget)
      source_eq
      numerator_zero

/-- Descent-schedule numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_descentSchedule_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.descentSchedule_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.descentSchedule_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.descentSchedule inputSource inputTarget)
      source_eq
      numerator_zero

/-- Interval-Stokes numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_intervalStokes_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.intervalStokes_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.intervalStokes_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.intervalStokes inputSource inputTarget)
      source_eq
      numerator_zero

/-- Interval-Fubini numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_intervalFubini_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.intervalFubini_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.intervalFubini_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.intervalFubini inputSource inputTarget)
      source_eq
      numerator_zero

/-- Tate-weight-drop numerator cancellation kills the represented roof. -/
theorem leftFraction_map_eq_zero_of_numerator_tateWeightDrop_postcomp_zero
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target)
    (inputSource inputTarget : QTraceExpression)
    (source_eq :
      fraction.Y' =
        TraceLocalizationInput.tateWeightDrop_stableSource
          inputSource
          inputTarget)
    (numerator_zero :
      fraction.f ≫
          (eqToHom source_eq ≫
            TraceLocalizationInput.tateWeightDrop_stableMap
              inputSource
              inputTarget) =
        0) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_localizationInput_postcomp_zero
      fraction
      (TraceLocalizationInput.tateWeightDrop inputSource inputTarget)
      source_eq
      numerator_zero

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
