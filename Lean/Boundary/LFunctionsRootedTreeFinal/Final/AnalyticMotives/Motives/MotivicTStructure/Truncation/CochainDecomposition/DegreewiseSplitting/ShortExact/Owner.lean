import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.Assembly.Owner

/-!
# Short exact fields from degreewise splittings

This file turns the concrete degreewise splitting calculus for the normalized
cochain-decomposition short complex into the exact, mono, epi, and short-exact
fields used by the truncation-existence layer.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A degreewise splitting of the additive cochain-decomposition short complex
gives exactness in that degree. -/
theorem additiveCochainDecompositionDegreewiseExact_of_splitting
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (splitting :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).Splitting) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Exact :=
  splitting.exact

/-- A degreewise splitting of the additive cochain-decomposition short complex
makes the first map monic in that degree. -/
theorem additiveCochainDecompositionDegreewiseMono_f_of_splitting
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (splitting :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).Splitting) :
    Mono
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).f :=
  splitting.mono_f

/-- A degreewise splitting of the additive cochain-decomposition short complex
makes the second map epic in that degree. -/
theorem additiveCochainDecompositionDegreewiseEpi_g_of_splitting
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (splitting :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).Splitting) :
    Epi
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g :=
  splitting.epi_g

/-- A degreewise splitting of the additive cochain-decomposition short complex
is a short-exact certificate in that degree. -/
theorem additiveCochainDecompositionDegreewiseShortExact_of_splitting
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (splitting :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).Splitting) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).ShortExact :=
  splitting.shortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
