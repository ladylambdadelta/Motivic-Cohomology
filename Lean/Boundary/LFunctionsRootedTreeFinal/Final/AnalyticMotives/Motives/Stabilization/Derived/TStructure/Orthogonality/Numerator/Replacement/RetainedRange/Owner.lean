import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Nonboundary.Owner

/-!
# Retained-range quasi-isomorphism facts for truncation replacements

This file owns the retained-range homology-isomorphism parts of the lower and
upper truncation replacement maps.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- In nonpositive degrees, the concrete lower-truncation inclusion induces an
isomorphism on homology. -/
theorem exactAt_source_truncLEInclusion_quasiIsoAt_nonpositive
    (sourceComplex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (degree_le_zero : degree ≤ 0) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)
      degree :=
  Or.elim
    (lt_or_eq_of_le degree_le_zero)
    (fun degree_lt_zero =>
      TraceAnalyticDerivedMotiveCategory
        .exactAt_source_truncLEInclusion_quasiIsoAt_below_zero
          sourceComplex
          degree
          degree_lt_zero)
    (fun degree_eq_zero =>
      Eq.ndrec
        (TraceAnalyticDerivedMotiveCategory
          .exactAt_source_truncLEInclusion_quasiIsoAt_boundary_zero
            sourceComplex)
        degree_eq_zero.symm)

/-- In degrees at least `1`, the concrete upper-truncation projection induces
an isomorphism on homology. -/
theorem exactAt_target_truncGEProjection_quasiIsoAt_ge_one
    (targetComplex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (one_le_degree : 1 ≤ degree) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)
      degree :=
  Or.elim
    (lt_or_eq_of_le one_le_degree)
    (fun one_lt_degree =>
      TraceAnalyticDerivedMotiveCategory
        .exactAt_target_truncGEProjection_quasiIsoAt_above_one
          targetComplex
          degree
          one_lt_degree)
    (fun one_eq_degree =>
      Eq.ndrec
        (TraceAnalyticDerivedMotiveCategory
          .exactAt_target_truncGEProjection_quasiIsoAt_boundary_one
            targetComplex)
        one_eq_degree)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
