import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner

/-!
# Fraction notation for derived analytic orthogonality

This file owns the quasi-isomorphism fraction notation used in the
chain-level orthogonality argument.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The quasi-isomorphism class used to form the derived analytic motive
category. -/
abbrev derivedQuasiIsoClass :
    MorphismProperty TraceAnalyticAbelianCochainComplex :=
  HomologicalComplex.quasiIso
    TraceAnalyticAdditiveAbelianEnvelope
    (ComplexShape.up ℤ)

/-- A left-fraction representative of a derived morphism between represented
complexes. -/
abbrev DerivedLeftFraction
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex) :=
  TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass
    .LeftFraction sourceComplex targetComplex

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
