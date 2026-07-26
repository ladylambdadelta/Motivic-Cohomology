import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Support.Cut.Owner

/-!
# Strict-support numerator orthogonality

This file owns the degreewise zero calculation for maps from a complex
strictly supported in degrees `≤ 0` to a complex strictly supported in degrees
`≥ 1`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- At a degree below `1`, the concrete upper-tail support condition makes the
target object zero. -/
theorem truncGE_one_target_isZero_of_degree_lt_one
    (targetComplex : TraceAnalyticAbelianCochainComplex)
    [targetComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (degree : ℤ)
    (degree_lt_one : degree < 1) :
    IsZero (targetComplex.X degree) :=
  targetComplex.isZero_X_of_isStrictlySupported
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
    degree
    (fun upperTail =>
      TraceAnalyticDerivedMotiveCategory
        .truncGEEmbedding_outside_below_cut
          1
          degree
          degree_lt_one
          upperTail)

/-- At a degree at least `1`, the concrete lower-tail support condition makes
the source object zero. -/
theorem truncLE_zero_source_isZero_of_one_le_degree
    (sourceComplex : TraceAnalyticAbelianCochainComplex)
    [sourceComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    (degree : ℤ)
    (one_le_degree : 1 ≤ degree) :
    IsZero (sourceComplex.X degree) :=
  let zero_lt_degree : (0 : ℤ) < degree :=
    lt_of_lt_of_le
      (show (0 : ℤ) < 1 from zero_lt_one)
      one_le_degree
  sourceComplex.isZero_X_of_isStrictlySupported
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)
    degree
    (fun lowerTail =>
      TraceAnalyticDerivedMotiveCategory
        .truncLEEmbedding_outside_above_cut
          0
          degree
          zero_lt_degree
          lowerTail)

/-- A component of a map from strict lower support to strict upper support is
zero in every degree. -/
theorem truncLE_zero_to_truncGE_one_component_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    [sourceComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (hom : sourceComplex ⟶ targetComplex)
    (degree : ℤ) :
    hom.f degree = 0 :=
  Or.elim
    (lt_or_ge degree 1)
    (fun degree_lt_one =>
      (TraceAnalyticDerivedMotiveCategory
        .truncGE_one_target_isZero_of_degree_lt_one
          targetComplex
          degree
          degree_lt_one).eq_of_tgt
        (hom.f degree)
        0)
    (fun one_le_degree =>
      (TraceAnalyticDerivedMotiveCategory
        .truncLE_zero_source_isZero_of_one_le_degree
          sourceComplex
          degree
          one_le_degree).eq_of_src
        (hom.f degree)
        0)

/-- Every map from a complex strictly supported in degrees `≤ 0` to a complex
strictly supported in degrees `≥ 1` is zero. -/
theorem truncLE_zero_to_truncGE_one_hom_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    [sourceComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetComplex.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (hom : sourceComplex ⟶ targetComplex) :
    hom = 0 :=
  HomologicalComplex.hom_ext
    hom
    0
    (fun degree =>
      TraceAnalyticDerivedMotiveCategory
        .truncLE_zero_to_truncGE_one_component_eq_zero
          sourceComplex
          targetComplex
          hom
          degree)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
