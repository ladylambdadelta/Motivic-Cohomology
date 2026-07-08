import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Zero.Owner

/-!
# Comparison-source zero bounded representatives

This file exposes the concrete bounded zero additive analytic complex under
comparison-facing names, together with its additive homotopy and stable
comparison-source images.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison-facing zero bounded additive analytic complex. -/
def TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy
    (bound : Nat) :
    TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound :=
  TraceAnalyticAdditiveCochainComplex.zeroBoundedBy bound

/-- The comparison-facing zero bounded complex has the concrete zero complex
underneath. -/
theorem TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy_complex
    (bound : Nat) :
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy
      bound).complex =
      TraceAnalyticAdditiveCochainComplex.zeroConcrete :=
  rfl

/-- Every degree object of the comparison-facing zero bounded complex is the
analytic additive zero object. -/
theorem TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy_degreeObject_object
    (bound : Nat)
    (degree : ℤ) :
    ((TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy
        bound).degreeObject degree).object =
      TraceAnalyticAdditiveCategory.zeroObject :=
  rfl

/-- Additive homotopy object represented by the comparison-facing zero bounded
complex. -/
def TraceAnalyticMotiveComparison.sourceZeroWeightBoundedHomotopyObject
    (bound : Nat) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)

/-- The zero bounded homotopy object is the homotopy image of the concrete zero
complex. -/
theorem TraceAnalyticMotiveComparison.sourceZeroWeightBoundedHomotopyObject_eq
    (bound : Nat) :
    TraceAnalyticMotiveComparison.sourceZeroWeightBoundedHomotopyObject bound =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        TraceAnalyticAdditiveCochainComplex.zeroConcrete :=
  rfl

/-- Stable comparison-source object represented by the comparison-facing zero
bounded complex. -/
def TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject
    (bound : Nat) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)

/-- The stable zero bounded object is the comparison-source image of the zero
bounded homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject_eq
    (bound : Nat) :
    TraceAnalyticMotiveComparison.sourceZeroStableWeightBoundedObject bound =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotiveComparison.sourceZeroWeightBoundedHomotopyObject
          bound) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
