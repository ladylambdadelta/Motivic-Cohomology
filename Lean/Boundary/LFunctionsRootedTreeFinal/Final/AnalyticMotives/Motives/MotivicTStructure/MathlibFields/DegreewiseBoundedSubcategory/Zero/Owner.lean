import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Zero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner

/-!
# Zero object of the degreewise bounded stable source

The degreewise bounded stable source contains the bounded stable zero object.
The proof that it is zero is inherited from its ambient zero-object
certificate in the analytic comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The canonical degreewise bounded zero object, obtained from the bounded
stable zero object. -/
def zeroObject :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .ofBoundedStable
      TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject

/-- The ambient object of the canonical degreewise bounded zero object is a
zero object in the analytic comparison source. -/
theorem zeroObject_ambient_isZero :
    IsZero
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .zeroObject).object :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject_ambient_isZero

/-- The canonical degreewise bounded zero object is zero in the degreewise
bounded full subcategory. -/
theorem zeroObject_isZero :
    IsZero
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable.zeroObject where
  unique_to :=
    fun target =>
      Nonempty.intro
        { default :=
            TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .zeroObject_ambient_isZero.to_ target.object
          uniq :=
            fun hom =>
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .zeroObject_ambient_isZero.eq_of_src
                  hom
                  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .zeroObject_ambient_isZero.to_ target.object) }
  unique_from :=
    fun source =>
      Nonempty.intro
        { default :=
            TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .zeroObject_ambient_isZero.from_ source.object
          uniq :=
            fun hom =>
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .zeroObject_ambient_isZero.eq_of_tgt
                  hom
                  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .zeroObject_ambient_isZero.from_ source.object) }

/-- The degreewise bounded stable source has a Mathlib zero object. -/
instance instHasZeroObject :
    HasZeroObject
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  IsZero.hasZeroObject
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .zeroObject_isZero

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
