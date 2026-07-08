import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Zero.Owner

/-!
# The concrete zero bounded representative in the bounded stable source

The comparison-source zero bounded complex gives a genuine object of the
bounded stable full subcategory.  This file records that representative
without identifying it yet with the categorical zero object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The stable comparison-source object represented by the zero bounded
complex at a fixed bound belongs to the bounded stable source. -/
theorem zeroStableWeightBoundedObject_membership
    (bound : Nat) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject
        bound) :=
  TraceAnalyticDMgmComparisonSource
    .boundedStableObject_of_sourceStableWeightBoundedObject
      (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)

/-- The zero bounded representative as an object of the bounded stable full
subcategory. -/
def zeroRepresentative
    (bound : Nat) :
    TraceAnalyticDMgmComparisonSource.BoundedStable where
  obj :=
    TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject bound
  property :=
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .zeroStableWeightBoundedObject_membership bound

/-- The ambient object of the bounded zero representative is the stable image
of the zero bounded complex. -/
theorem zeroRepresentative_object
    (bound : Nat) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .zeroRepresentative bound).object =
      TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject
        bound :=
  rfl

/-- The bounded zero representative has the bounded-stable membership proved
from the zero bounded complex. -/
theorem zeroRepresentative_membership
    (bound : Nat) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .zeroRepresentative bound).object :=
  TraceAnalyticDMgmComparisonSource.BoundedStable
    .zeroStableWeightBoundedObject_membership bound

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
