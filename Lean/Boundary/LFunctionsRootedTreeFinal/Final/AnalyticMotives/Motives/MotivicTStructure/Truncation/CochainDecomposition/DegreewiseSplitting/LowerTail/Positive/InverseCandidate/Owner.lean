import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner

/-!
# Positive lower-tail inverse candidate

Positive lower-tail degrees are nonboundary degrees for the paired lower
truncation.  This file names the equality-transport inverse candidate for the
lower inclusion component at such degrees.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The inverse candidate for the lower inclusion component at a positive
normalized lower-tail degree, obtained by transporting along the concrete
object normal form for nonboundary lower-tail truncation. -/
def additiveDecompositionLowerTailSuccLowerMapInverseCandidate
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    complex.X (cut - 1 - (Nat.succ lowerTail : ℤ)) ⟶
      (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
        cut
        complex).X (cut - 1 - (Nat.succ lowerTail : ℤ)) :=
  eqToHom
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .additiveDecompositionTruncLE_X_of_decompositionLowerTail_succ
          cut
          complex
          lowerTail))

/-- The same positive lower-tail inverse candidate, typed as a morphism between
the middle and first objects of the evaluated normalized cochain-decomposition
short complex. -/
def additiveCochainDecompositionLowerTailSuccDegreewiseLowerInverseCandidate
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        (cut - 1 - (Nat.succ lowerTail : ℤ)))).X₂ ⟶
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          (cut - 1 - (Nat.succ lowerTail : ℤ)))).X₁ :=
  TraceAnalyticMotivicTStructure
    .additiveDecompositionLowerTailSuccLowerMapInverseCandidate
      cut
      complex
      lowerTail

/-- The first map of the evaluated normalized cochain-decomposition short
complex at a positive lower-tail degree is the concrete lower-inclusion
component at that degree. -/
theorem additiveCochainDecompositionLowerTailSuccDegreewiseLowerMap_eq_component
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        (cut - 1 - (Nat.succ lowerTail : ℤ)))).f =
      (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
        cut
        complex).f (cut - 1 - (Nat.succ lowerTail : ℤ)) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
