import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Operations.Owner

/-!
# Parent image of algebraized formal-sum operations

This file records term-level parent-image computations for algebraized formal
sum operations.  Whole finite-sum equality is downstream from these term
computations.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- The algebraization selected by a one-term formal sum is the input support. -/
theorem term_at_unit
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.term q A).at PUnit.unit = A :=
  rfl

/-- The parent prime class of a one-term formal sum is the input parent prime. -/
theorem term_parentPrimeGeomAt_unit
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.term q A).parentPrimeGeomAt PUnit.unit =
      A.parentPrimeGeom :=
  rfl

/-- The parent rational term of a one-term formal sum is the expected singleton. -/
theorem term_parentRationalTermAt_unit
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.term q A).parentRationalTermAt PUnit.unit =
      Finsupp.single A.parentPrimeGeom q :=
  rfl

/-- Scaling preserves the parent prime class of each summand. -/
theorem scale_parentPrimeGeomAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    (AlgebraizedContourFormalSum.scale q A).parentPrimeGeomAt i =
      A.parentPrimeGeomAt i :=
  rfl

/-- Scaling multiplies the rational coefficient of each parent singleton. -/
theorem scale_parentRationalTermAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    (AlgebraizedContourFormalSum.scale q A).parentRationalTermAt i =
      Finsupp.single (A.parentPrimeGeomAt i) (q * A.coefficientAt i) :=
  rfl

/-- The left summands of an algebraized sum use the left parent prime classes. -/
theorem add_parentPrimeGeomAt_left
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T)
    (i : S.Index) :
    (AlgebraizedContourFormalSum.add A B).parentPrimeGeomAt (Sum.inl i) =
      A.parentPrimeGeomAt i :=
  rfl

/-- The right summands of an algebraized sum use the right parent prime classes. -/
theorem add_parentPrimeGeomAt_right
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T)
    (j : T.Index) :
    (AlgebraizedContourFormalSum.add A B).parentPrimeGeomAt (Sum.inr j) =
      B.parentPrimeGeomAt j :=
  rfl

/-- The left summands of an algebraized sum use the left parent rational terms. -/
theorem add_parentRationalTermAt_left
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T)
    (i : S.Index) :
    (AlgebraizedContourFormalSum.add A B).parentRationalTermAt (Sum.inl i) =
      A.parentRationalTermAt i :=
  rfl

/-- The right summands of an algebraized sum use the right parent rational terms. -/
theorem add_parentRationalTermAt_right
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T)
    (j : T.Index) :
    (AlgebraizedContourFormalSum.add A B).parentRationalTermAt (Sum.inr j) =
      B.parentRationalTermAt j :=
  rfl

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
