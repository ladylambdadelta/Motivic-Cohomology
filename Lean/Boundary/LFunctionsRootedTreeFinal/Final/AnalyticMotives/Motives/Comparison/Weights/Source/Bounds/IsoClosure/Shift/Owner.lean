import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.IsoClosure.Owner

/-!
# Shifts of degreewise iso-closure bounded source complexes

This file records that comparison-source degreewise iso-closure boundedness is
stable under cochain shifts, by reindexing degree `i` to degree `i + n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotiveComparison

/-- Degreewise iso-closure boundedness is preserved by cochain shifts. -/
theorem sourceComplexDegreewiseIsoClosureBoundedBy_shift
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (membership :
      TraceAnalyticMotiveComparison
        .sourceComplexDegreewiseIsoClosureBoundedBy complex bound)
    (shift : ℤ) :
    TraceAnalyticMotiveComparison
      .sourceComplexDegreewiseIsoClosureBoundedBy
        ((CochainComplex.shiftFunctor
          TraceAnalyticAdditiveCategoryObject
          shift).obj complex)
        bound :=
  fun degree =>
    membership (degree + shift)

end TraceAnalyticMotiveComparison

end AnalyticMotives
end LFunctions
end Boundary
