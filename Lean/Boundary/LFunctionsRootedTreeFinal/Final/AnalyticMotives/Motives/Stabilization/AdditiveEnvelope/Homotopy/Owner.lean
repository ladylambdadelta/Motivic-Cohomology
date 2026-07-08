import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Complexes.Owner

/-!
# Homotopy category of additive analytic complexes

The homotopy quotient is taken after passing to the concrete additive envelope
of finite analytic trace families.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The homotopy category of additive analytic cochain complexes. -/
abbrev TraceAnalyticAdditiveHomotopyCategory :=
  HomotopyCategory TraceAnalyticAdditiveCategoryObject (ComplexShape.up ℤ)

/-- The quotient functor from additive analytic complexes to their homotopy category. -/
def TraceAnalyticAdditiveHomotopyCategory.quotientFunctor :
    TraceAnalyticAdditiveCochainComplex ⥤
      TraceAnalyticAdditiveHomotopyCategory :=
  HomotopyCategory.quotient TraceAnalyticAdditiveCategoryObject (ComplexShape.up ℤ)

/-- The homotopy-category image of an additive analytic cochain complex. -/
def TraceAnalyticAdditiveHomotopyCategory.objectOf
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.obj complex

/-- The homotopy-category image of an additive analytic chain map. -/
def TraceAnalyticAdditiveHomotopyCategory.mapOf
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticAdditiveHomotopyCategory.objectOf source ⟶
      TraceAnalyticAdditiveHomotopyCategory.objectOf target :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map hom

/-- The object map is the object part of the homotopy quotient functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.objectOf_eq
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex =
      TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.obj complex :=
  rfl

/-- The morphism map is the morphism part of the homotopy quotient functor. -/
theorem TraceAnalyticAdditiveHomotopyCategory.mapOf_eq
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    TraceAnalyticAdditiveHomotopyCategory.mapOf hom =
      TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map hom :=
  rfl

/-- The additive analytic homotopy category is preadditive. -/
def TraceAnalyticAdditiveHomotopyCategory.preadditiveStructure :
    CategoryTheory.Preadditive TraceAnalyticAdditiveHomotopyCategory :=
  inferInstance

/-- The additive analytic homotopy category is Q-linear. -/
def TraceAnalyticAdditiveHomotopyCategory.linearRatStructure :
    CategoryTheory.Linear Rat TraceAnalyticAdditiveHomotopyCategory :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary
