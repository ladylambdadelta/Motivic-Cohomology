import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.StrictDerived.Owner

/-!
# Exactness-to-strict-transport numerator reduction

This file owns the remaining construction interface for reducing adjacent
exactness bounds to strict-support numerator transport.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Exactness above degree `0` supplies a strict lower-support replacement in
the derived category. -/
theorem exactAt_source_strict_lower_replacement
    (sourceComplex : TraceAnalyticAbelianCochainComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree) :
    ∃ sourceReplacement : TraceAnalyticAbelianCochainComplex,
      sourceReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0) ∧
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ≅
        TraceAnalyticDerivedMotiveCategory.objectOf sourceReplacement :=
  TraceAnalyticDerivedMotiveCategory
    .exactAt_source_strict_lower_replacement_of_truncLE_quasiIso
      sourceComplex
      sourceExact

/-- Exactness below degree `1` supplies a strict upper-support replacement in
the derived category. -/
theorem exactAt_target_strict_upper_replacement
    (targetComplex : TraceAnalyticAbelianCochainComplex)
    (targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetComplex.ExactAt degree) :
    ∃ targetReplacement : TraceAnalyticAbelianCochainComplex,
      targetReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1) ∧
      TraceAnalyticDerivedMotiveCategory.objectOf targetReplacement ≅
        TraceAnalyticDerivedMotiveCategory.objectOf targetComplex :=
  TraceAnalyticDerivedMotiveCategory
    .exactAt_target_strict_upper_replacement_of_truncGE_quasiIso
      targetComplex
      targetExact

/-- After strict replacements, the numerator is a morphism from the strict
lower side to the strict upper side, hence its conjugate is zero in the
derived category. -/
theorem leftFraction_numerator_strict_conjugate_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    [sourceReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (sourceIso :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ≅
        TraceAnalyticDerivedMotiveCategory.objectOf sourceReplacement)
    (targetIso :
      TraceAnalyticDerivedMotiveCategory.objectOf targetReplacement ≅
        TraceAnalyticDerivedMotiveCategory.objectOf fraction.Y') :
    sourceIso.inv ≫
        TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          fraction.f ≫
      targetIso.inv =
    0 :=
  TraceAnalyticDerivedMotiveCategory
    .strictSupport_objectOf_morphism_eq_zero
      sourceReplacement
      targetReplacement
      (sourceIso.inv ≫
        TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          fraction.f ≫
        targetIso.inv)

/-- If the strict-replacement conjugate of the numerator is zero, then the
original localized numerator is zero. -/
theorem leftFraction_numerator_maps_to_zero_of_strict_conjugate_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    (sourceIso :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ≅
        TraceAnalyticDerivedMotiveCategory.objectOf sourceReplacement)
    (targetIso :
      TraceAnalyticDerivedMotiveCategory.objectOf targetReplacement ≅
        TraceAnalyticDerivedMotiveCategory.objectOf fraction.Y')
    (conjugateZero :
      sourceIso.inv ≫
          TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
            fraction.f ≫
        targetIso.inv =
      0) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f =
      0 :=
  (IsIso.comp_left_eq_zero
    (f := sourceIso.inv)
    (g :=
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f)).mp
    ((IsIso.comp_right_eq_zero
      (f :=
        sourceIso.inv ≫
          TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
            fraction.f)
      (g := targetIso.inv)).mp
      conjugateZero)

/-- Adjacent exactness bounds reduce the localized numerator to a strict
lower-to-upper map and hence make it zero. -/
theorem exactAtBounds_leftFraction_numerator_maps_to_zero_from_strict_transport
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree)
    (auxiliaryExact :
      ∀ degree : ℤ,
        degree < 1 →
          fraction.Y'.ExactAt degree) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f =
      0 :=
  Exists.elim
    (TraceAnalyticDerivedMotiveCategory
      .exactAt_source_strict_lower_replacement
        sourceComplex
        sourceExact)
    (fun sourceReplacement sourcePackage =>
      And.elim
        sourcePackage
        (fun sourceSupport sourceIso =>
          Exists.elim
            (TraceAnalyticDerivedMotiveCategory
              .exactAt_target_strict_upper_replacement
                fraction.Y'
                auxiliaryExact)
            (fun targetReplacement targetPackage =>
              And.elim
                targetPackage
                (fun targetSupport targetIso =>
                  letI :
                      sourceReplacement.IsStrictlySupported
                        (TraceAnalyticMotivicTStructure
                          .truncLEEmbedding 0) :=
                    sourceSupport
                  letI :
                      targetReplacement.IsStrictlySupported
                        (TraceAnalyticMotivicTStructure
                          .truncGEEmbedding 1) :=
                    targetSupport
                  TraceAnalyticDerivedMotiveCategory
                    .leftFraction_numerator_maps_to_zero_of_strict_conjugate_eq_zero
                      sourceComplex
                      targetComplex
                      fraction
                      sourceReplacement
                      targetReplacement
                      sourceIso
                      targetIso
                      (TraceAnalyticDerivedMotiveCategory
                        .leftFraction_numerator_strict_conjugate_eq_zero
                          sourceComplex
                          targetComplex
                          fraction
                          sourceReplacement
                          targetReplacement
                          sourceIso
                          targetIso)))))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
