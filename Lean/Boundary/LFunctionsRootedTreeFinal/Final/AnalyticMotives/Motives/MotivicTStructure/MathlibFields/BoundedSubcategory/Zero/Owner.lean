import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Zero.Contractible.Owner

/-!
# Zero object of the bounded stable source

The bounded stable source has a zero object represented by the concrete zero
bounded analytic complex.  The proof uses the contractibility of the concrete
zero complex and the faithful full-subcategory inclusion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The canonical bounded zero object, represented by the zero bounded complex
at bound `0`. -/
def zeroObject :
    TraceAnalyticDMgmComparisonSource.BoundedStable :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zeroRepresentative 0

/-- The ambient object of the canonical bounded zero object is a zero object in
the analytic comparison source. -/
theorem zeroObject_ambient_isZero :
    IsZero
      (TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject).object :=
  TraceAnalyticDMgmComparisonSource.BoundedStable
    .sourceZeroStableWeightBoundedObject_isZero 0

/-- The canonical bounded zero object is zero in the bounded full
subcategory. -/
theorem zeroObject_isZero :
    IsZero TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject where
  unique_to :=
    fun target =>
      Nonempty.intro
        { default :=
            TraceAnalyticDMgmComparisonSource.BoundedStable
              .zeroObject_ambient_isZero.to_ target.object
          uniq :=
            fun hom =>
              TraceAnalyticDMgmComparisonSource.BoundedStable
                .zeroObject_ambient_isZero.eq_of_src
                  hom
                  (TraceAnalyticDMgmComparisonSource.BoundedStable
                    .zeroObject_ambient_isZero.to_ target.object) }
  unique_from :=
    fun source =>
      Nonempty.intro
        { default :=
            TraceAnalyticDMgmComparisonSource.BoundedStable
              .zeroObject_ambient_isZero.from_ source.object
          uniq :=
            fun hom =>
              TraceAnalyticDMgmComparisonSource.BoundedStable
                .zeroObject_ambient_isZero.eq_of_tgt
                  hom
                  (TraceAnalyticDMgmComparisonSource.BoundedStable
                    .zeroObject_ambient_isZero.from_ source.object) }

/-- The bounded stable source has a Mathlib zero object. -/
instance instHasZeroObject :
    HasZeroObject TraceAnalyticDMgmComparisonSource.BoundedStable :=
  IsZero.hasZeroObject
    TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject_isZero

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
