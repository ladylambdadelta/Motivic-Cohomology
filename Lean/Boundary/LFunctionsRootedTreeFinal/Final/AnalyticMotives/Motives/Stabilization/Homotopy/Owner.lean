import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Complexes.Homs.Owner

/-!
# The analytic trace homotopy category

This file quotients analytic trace cochain complexes by chain homotopy.  The
result is still built over `TraceCorQObject`, so morphisms remain represented by
analytic trace-correspondence chain maps modulo explicit homotopies.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The homotopy category of analytic trace cochain complexes. -/
abbrev TraceAnalyticHomotopyCategory :=
  HomotopyCategory TraceCorQObject (ComplexShape.up ℤ)

/-- The quotient functor from analytic trace cochain complexes to their homotopy category. -/
def TraceAnalyticHomotopyCategory.quotientFunctor :
    TraceAnalyticCochainComplex ⥤ TraceAnalyticHomotopyCategory :=
  HomotopyCategory.quotient TraceCorQObject (ComplexShape.up ℤ)

/-- The homotopy-category image of an analytic trace cochain complex. -/
def TraceAnalyticHomotopyCategory.objectOf
    (complex : TraceAnalyticCochainComplex) :
    TraceAnalyticHomotopyCategory :=
  TraceAnalyticHomotopyCategory.quotientFunctor.obj complex

/-- The homotopy-category image of an analytic trace chain map. -/
def TraceAnalyticHomotopyCategory.mapOf
    {source target : TraceAnalyticCochainComplex}
    (hom : TraceAnalyticCochainComplex.Hom source target) :
    TraceAnalyticHomotopyCategory.objectOf source ⟶
      TraceAnalyticHomotopyCategory.objectOf target :=
  TraceAnalyticHomotopyCategory.quotientFunctor.map hom

/-- The object map is the object part of the homotopy quotient functor. -/
theorem TraceAnalyticHomotopyCategory.objectOf_eq
    (complex : TraceAnalyticCochainComplex) :
    TraceAnalyticHomotopyCategory.objectOf complex =
      TraceAnalyticHomotopyCategory.quotientFunctor.obj complex :=
  rfl

/-- The morphism map is the morphism part of the homotopy quotient functor. -/
theorem TraceAnalyticHomotopyCategory.mapOf_eq
    {source target : TraceAnalyticCochainComplex}
    (hom : TraceAnalyticCochainComplex.Hom source target) :
    TraceAnalyticHomotopyCategory.mapOf hom =
      TraceAnalyticHomotopyCategory.quotientFunctor.map hom :=
  rfl

/-- The analytic trace homotopy category is preadditive. -/
def TraceAnalyticHomotopyCategory.preadditiveStructure :
    CategoryTheory.Preadditive TraceAnalyticHomotopyCategory :=
  inferInstance

/-- The analytic trace homotopy category is Q-linear. -/
def TraceAnalyticHomotopyCategory.linearRatStructure :
    CategoryTheory.Linear Rat TraceAnalyticHomotopyCategory :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary
