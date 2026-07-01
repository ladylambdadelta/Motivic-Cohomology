import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RationalHom.Owner

/-!
# Algebraization of rational contour formal sums

This file algebraizes a finite rational contour formal sum term-by-term and
constructs the corresponding parent rational finite correspondence.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

/--
Termwise algebraization data for a finite rational contour sum.

Each contour summand is equipped with a parent prime finite correspondence
support over the same smooth algebraized source and target.
-/
structure AlgebraizedContourFormalSum
    {X Y : ContourCorQObject}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y)
    (S : ContourCorQFormalSum X Y) where
  termAlgebraization :
    (i : S.Index) →
      AlgebraizedContourPrimeSupport
        sourceBulk targetBulk (S.correspondenceAt i)

namespace AlgebraizedContourFormalSum

/-- The algebraization selected at one summand. -/
def at
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    AlgebraizedContourPrimeSupport
      sourceBulk targetBulk (S.correspondenceAt i) :=
  A.termAlgebraization i

/-- The parent prime geometric class attached to one summand. -/
def parentPrimeGeomAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    PrimeFiniteCorrespondenceGeom sourceBulk.scheme targetBulk.scheme :=
  (A.at i).parentPrimeGeom

/-- The rational coefficient attached to one algebraized summand. -/
def coefficientAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (_A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    Rat :=
  S.coeffAt i

/-- The parent rational singleton attached to one algebraized summand. -/
def parentRationalTermAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  letI : DecidableEq
      (PrimeFiniteCorrespondenceGeom sourceBulk.scheme targetBulk.scheme) :=
    Classical.decEq _
  Finsupp.single (A.parentPrimeGeomAt i) (A.coefficientAt i)

/-- The parent rational finite correspondence associated to the whole formal sum. -/
def parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  letI : Finite S.Index := S.finiteIndex
  letI : Fintype S.Index := Fintype.ofFinite S.Index
  Finset.univ.sum (fun i : S.Index => A.parentRationalTermAt i)

/-- The parent `SmCorQ` hom associated to the whole formal sum. -/
def parentSmCorQHom
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (_category : SmCorQ (k := G.carrier))
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    SmCorQ.Hom _category sourceBulk.scheme targetBulk.scheme :=
  A.parentRationalCorrespondence

/-- The parent `SmCorQ` hom is the finite sum of the algebraized summands. -/
theorem parentSmCorQHom_eq_sum
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (category : SmCorQ (k := G.carrier))
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    A.parentSmCorQHom category =
      A.parentRationalCorrespondence :=
  rfl

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
