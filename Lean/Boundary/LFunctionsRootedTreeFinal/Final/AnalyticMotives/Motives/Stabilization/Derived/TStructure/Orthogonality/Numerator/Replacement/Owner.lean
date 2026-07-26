import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Owner

/-!
# Strict truncation replacements for numerator orthogonality

This file owns the construction of strict lower and upper representatives from
adjacent exactness bounds.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Exactness above degree `0` makes the concrete lower-truncation inclusion a
quasi-isomorphism. -/
theorem exactAt_source_truncLEInclusion_quasiIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex) :=
  let sourceReplacement : TraceAnalyticAbelianCochainComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE 0 sourceComplex
  let sourceInclusion :
      sourceReplacement ⟶ sourceComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex
  letI :
      sourceReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_isStrictlySupported 0 sourceComplex
  { quasiIsoAt :=
      fun degree =>
        Or.elim
          (lt_or_ge 0 degree)
          (fun zero_lt_degree =>
            let sourceReplacementExact :
                sourceReplacement.ExactAt degree :=
              sourceReplacement.exactAt_of_isSupported
                (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)
                degree
                (fun lowerTail =>
                  TraceAnalyticDerivedMotiveCategory
                    .truncLEEmbedding_outside_above_cut
                      0
                      degree
                      zero_lt_degree
                      lowerTail)
            (_root_.quasiIsoAt_iff_exactAt
              sourceInclusion
              degree
              sourceReplacementExact).mpr
              (sourceExact degree zero_lt_degree))
          (fun degree_le_zero =>
            TraceAnalyticDerivedMotiveCategory
              .exactAt_source_truncLEInclusion_quasiIsoAt_nonpositive
                sourceComplex
                degree
                degree_le_zero) }

/-- Exactness below degree `1` makes the concrete upper-truncation projection a
quasi-isomorphism. -/
theorem exactAt_target_truncGEProjection_quasiIso
    (targetComplex : TraceAnalyticAbelianCochainComplex)
    (targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetComplex.ExactAt degree) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex) :=
  let targetReplacement : TraceAnalyticAbelianCochainComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE 1 targetComplex
  let targetProjection :
      targetComplex ⟶ targetReplacement :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGEProjectionMap 1 targetComplex
  letI :
      targetReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE_isStrictlySupported 1 targetComplex
  { quasiIsoAt :=
      fun degree =>
        Or.elim
          (lt_or_ge degree 1)
          (fun degree_lt_one =>
            let targetReplacementExact :
                targetReplacement.ExactAt degree :=
              targetReplacement.exactAt_of_isSupported
                (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
                degree
                (fun upperTail =>
                  TraceAnalyticDerivedMotiveCategory
                    .truncGEEmbedding_outside_below_cut
                      1
                      degree
                      degree_lt_one
                      upperTail)
            (_root_.quasiIsoAt_iff_exactAt
              targetProjection
              degree
              (targetExact degree degree_lt_one)).mpr
              targetReplacementExact)
          (fun one_le_degree =>
            TraceAnalyticDerivedMotiveCategory
              .exactAt_target_truncGEProjection_quasiIsoAt_ge_one
                targetComplex
                degree
                one_le_degree) }


/-- The strict lower replacement is the concrete lower truncation. -/
theorem exactAt_source_strict_lower_replacement_of_truncLE_quasiIso
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
  let sourceReplacement : TraceAnalyticAbelianCochainComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE 0 sourceComplex
  let sourceInclusion :
      sourceReplacement ⟶ sourceComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex
  letI :
      sourceReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_isStrictlySupported 0 sourceComplex
  letI : QuasiIso sourceInclusion :=
    TraceAnalyticDerivedMotiveCategory
      .exactAt_source_truncLEInclusion_quasiIso
        sourceComplex
        sourceExact
  letI :
      IsIso
        (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          sourceInclusion) :=
    TraceAnalyticDerivedMotiveCategory
      .mapOf_isIso_of_quasiIso sourceInclusion
  ⟨sourceReplacement,
    inferInstance,
    (asIso
      (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        sourceInclusion)).symm⟩

/-- The strict upper replacement is the concrete upper truncation. -/
theorem exactAt_target_strict_upper_replacement_of_truncGE_quasiIso
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
  let targetReplacement : TraceAnalyticAbelianCochainComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE 1 targetComplex
  let targetProjection :
      targetComplex ⟶ targetReplacement :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGEProjectionMap 1 targetComplex
  letI :
      targetReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE_isStrictlySupported 1 targetComplex
  letI : QuasiIso targetProjection :=
    TraceAnalyticDerivedMotiveCategory
      .exactAt_target_truncGEProjection_quasiIso
        targetComplex
        targetExact
  letI :
      IsIso
        (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          targetProjection) :=
    TraceAnalyticDerivedMotiveCategory
      .mapOf_isIso_of_quasiIso targetProjection
  ⟨targetReplacement,
    inferInstance,
    (asIso
      (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        targetProjection)).symm⟩

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
