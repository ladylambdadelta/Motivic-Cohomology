import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Owner

/-!
# Operations on additive-envelope matrix homs

The additive envelope uses ordinary matrix operations: zero, addition,
negation, scalar multiplication, and matrix composition by finite summation of
trace-correspondence composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero matrix-valued analytic trace correspondence. -/
def TraceAnalyticAdditiveHom.zero
    (source target : TraceAnalyticAdditiveObject) :
    TraceAnalyticAdditiveHom source target :=
  fun sourceIndex targetIndex =>
    (0 :
      TraceCorQHom
        (source.component sourceIndex)
        (target.component targetIndex))

/-- Entrywise addition of matrix-valued analytic trace correspondences. -/
def TraceAnalyticAdditiveHom.add
    {source target : TraceAnalyticAdditiveObject}
    (left right : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom source target :=
  fun sourceIndex targetIndex =>
    left sourceIndex targetIndex +
      right sourceIndex targetIndex

/-- Entrywise negation of a matrix-valued analytic trace correspondence. -/
def TraceAnalyticAdditiveHom.neg
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom source target :=
  fun sourceIndex targetIndex =>
    -hom sourceIndex targetIndex

/-- Entrywise scalar multiplication of matrix-valued analytic trace correspondences. -/
def TraceAnalyticAdditiveHom.smul
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target) :
    TraceAnalyticAdditiveHom source target :=
  fun sourceIndex targetIndex =>
    coefficient • hom sourceIndex targetIndex

/-- Matrix composition of analytic trace correspondences. -/
def TraceAnalyticAdditiveHom.comp
    {source middle target : TraceAnalyticAdditiveObject}
    (left : TraceAnalyticAdditiveHom source middle)
    (right : TraceAnalyticAdditiveHom middle target) :
    TraceAnalyticAdditiveHom source target :=
  fun sourceIndex targetIndex =>
    Finset.univ.sum
      (fun middleIndex =>
        TraceCorQHom.comp
          (left sourceIndex middleIndex)
          (right middleIndex targetIndex))

/-- The zero matrix evaluates to the zero trace correspondence. -/
theorem TraceAnalyticAdditiveHom.zero_entry
    (source target : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveHom.zero source target).entry sourceIndex targetIndex =
      0 :=
  rfl

/-- Addition of matrix homs is entrywise addition. -/
theorem TraceAnalyticAdditiveHom.add_entry
    {source target : TraceAnalyticAdditiveObject}
    (left right : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveHom.add left right).entry sourceIndex targetIndex =
      left.entry sourceIndex targetIndex +
        right.entry sourceIndex targetIndex :=
  rfl

/-- Negation of matrix homs is entrywise negation. -/
theorem TraceAnalyticAdditiveHom.neg_entry
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveHom.neg hom).entry sourceIndex targetIndex =
      -hom.entry sourceIndex targetIndex :=
  rfl

/-- Scalar multiplication of matrix homs is entrywise scalar multiplication. -/
theorem TraceAnalyticAdditiveHom.smul_entry
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveObject}
    (hom : TraceAnalyticAdditiveHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveHom.smul coefficient hom).entry sourceIndex targetIndex =
      coefficient • hom.entry sourceIndex targetIndex :=
  rfl

/-- Composition of matrix homs is finite summation over the middle family. -/
theorem TraceAnalyticAdditiveHom.comp_entry
    {source middle target : TraceAnalyticAdditiveObject}
    (left : TraceAnalyticAdditiveHom source middle)
    (right : TraceAnalyticAdditiveHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveHom.comp left right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (left.entry sourceIndex middleIndex)
            (right.entry middleIndex targetIndex)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
