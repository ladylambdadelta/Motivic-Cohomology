import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Zero.Owner

/-!
# Mathlib zero-object package for the analytic additive envelope

The empty analytic trace family is the concrete zero object of the matrix
category: every matrix from it and every matrix into it is uniquely determined.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- Unique morphisms from the empty analytic trace family. -/
def TraceAnalyticAdditiveCategory.uniqueFromZero
    (target : TraceAnalyticAdditiveCategoryObject) :
    Unique
      (TraceAnalyticAdditiveCategory.zeroObject ⟶ target) where
  default :=
    TraceAnalyticAdditiveCategory.zeroHom
      TraceAnalyticAdditiveCategory.zeroObject
      target
  uniq :=
    fun hom =>
      TraceAnalyticAdditiveCategory.hom_from_zero_ext
        target
        hom
        (TraceAnalyticAdditiveCategory.zeroHom
          TraceAnalyticAdditiveCategory.zeroObject
          target)

/-- Unique morphisms into the empty analytic trace family. -/
def TraceAnalyticAdditiveCategory.uniqueToZero
    (source : TraceAnalyticAdditiveCategoryObject) :
    Unique
      (source ⟶ TraceAnalyticAdditiveCategory.zeroObject) where
  default :=
    TraceAnalyticAdditiveCategory.zeroHom
      source
      TraceAnalyticAdditiveCategory.zeroObject
  uniq :=
    fun hom =>
      TraceAnalyticAdditiveCategory.hom_to_zero_ext
        source
        hom
        (TraceAnalyticAdditiveCategory.zeroHom
          source
          TraceAnalyticAdditiveCategory.zeroObject)

/-- The empty analytic trace family is a zero object in the additive envelope. -/
theorem TraceAnalyticAdditiveCategory.zeroObject_isZero :
    IsZero TraceAnalyticAdditiveCategory.zeroObject where
  unique_to :=
    fun target =>
      Nonempty.intro
        (TraceAnalyticAdditiveCategory.uniqueFromZero target)
  unique_from :=
    fun source =>
      Nonempty.intro
        (TraceAnalyticAdditiveCategory.uniqueToZero source)

/-- The analytic additive envelope has a Mathlib zero object. -/
instance traceAnalyticAdditiveCategory_hasZeroObject :
    HasZeroObject TraceAnalyticAdditiveCategoryObject :=
  IsZero.hasZeroObject
    TraceAnalyticAdditiveCategory.zeroObject_isZero

end AnalyticMotives
end LFunctions
end Boundary
