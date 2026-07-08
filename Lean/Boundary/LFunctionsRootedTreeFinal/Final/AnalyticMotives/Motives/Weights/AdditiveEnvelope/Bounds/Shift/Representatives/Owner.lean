import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Shift.Homotopy.Owner

/-!
# Concrete bounded representatives for homotopy shifts

The homotopy shift of a bounded analytic complex is canonically isomorphic to
the homotopy image of the concrete shifted bounded complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The canonical comparison from the concrete shifted bounded representative to the shifted
homotopy object. -/
def TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObjectRepresentativeIso
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
        (complex.shift degree) ≅
      TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObject
        complex
        degree :=
  (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.commShiftIso degree).app
    complex.complex

/-- The representative comparison is the quotient-functor shift commutation isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObjectRepresentativeIso_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObjectRepresentativeIso
        complex
        degree =
      (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.commShiftIso degree).app
        complex.complex :=
  rfl

/-- Shifted bounded maps are compatible with the representative comparison isomorphisms. -/
theorem TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap_representativeIso_naturality
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap
        (hom.shift degree) ≫
        (TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObjectRepresentativeIso
          target
          degree).hom =
      (TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedObjectRepresentativeIso
        source
        degree).hom ≫
        TraceAnalyticAdditiveHomotopyCategory.shiftedWeightBoundedMap
          hom
          degree :=
  (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.commShiftIso
    degree).hom.naturality hom

end AnalyticMotives
end LFunctions
end Boundary
