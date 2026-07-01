import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Owner

/-!
# Operations on algebraized contour formal sums

This file proves that termwise algebraization is closed under the formal
zero, term, scaling, and addition operations used before quotienting.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- The empty formal sum has the unique termwise algebraization. -/
def zero
    {X Y : ContourCorQObject}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.zero X Y) where
  termAlgebraization := fun i => nomatch i

/-- A one-term formal sum is algebraized by algebraizing its raw correspondence. -/
def term
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.term q f) where
  termAlgebraization := fun _ => A

/-- A single raw correspondence is algebraized as a coefficient-one term. -/
def single
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.single f) :=
  term 1 A

/-- Scaling a formal sum preserves its termwise support algebraizations. -/
def scale
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.scale q S) where
  termAlgebraization := fun i => A.at i

/-- Adding formal sums combines the termwise algebraizations by disjoint union. -/
def add
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.add S T) where
  termAlgebraization :=
    Sum.elim
      (fun i => A.at i)
      (fun j => B.at j)

/-- Negating a formal sum preserves its termwise support algebraizations. -/
def neg
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.neg S) :=
  scale (-1) A

/-- Subtracting formal sums combines addition with negation of algebraizations. -/
def sub
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T) :
    AlgebraizedContourFormalSum
      sourceBulk targetBulk (ContourCorQFormalSum.sub S T) :=
  add A (neg B)

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
