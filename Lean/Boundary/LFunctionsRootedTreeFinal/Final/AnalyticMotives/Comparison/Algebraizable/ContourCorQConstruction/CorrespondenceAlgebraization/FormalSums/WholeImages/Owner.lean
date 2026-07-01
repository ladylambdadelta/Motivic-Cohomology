import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.OperationImages.Owner

/-!
# Whole parent images of algebraized formal-sum operations

This file upgrades the termwise image computations to finite-sum image
computations in the parent rational finite-correspondence group.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- The parent image of the empty algebraized formal sum is zero. -/
theorem zero_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y) :
    (AlgebraizedContourFormalSum.zero sourceBulk targetBulk).parentRationalCorrespondence =
      0 :=
  Finset.sum_empty

/-- The parent image of a one-term algebraized formal sum is its singleton image. -/
theorem term_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.term q A).parentRationalCorrespondence =
      Finsupp.single A.parentPrimeGeom q :=
  Eq.trans
    (Fintype.sum_unique
      (fun i : PUnit =>
        (AlgebraizedContourFormalSum.term q A).parentRationalTermAt i))
    (term_parentRationalTermAt_unit q A)

/-- Parent rational correspondences add under algebraized formal-sum addition. -/
theorem add_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (B : AlgebraizedContourFormalSum sourceBulk targetBulk T) :
    (AlgebraizedContourFormalSum.add A B).parentRationalCorrespondence =
      A.parentRationalCorrespondence + B.parentRationalCorrespondence :=
  Fintype.sum_sum_type
    (fun i : S.Index ⊕ T.Index =>
      (AlgebraizedContourFormalSum.add A B).parentRationalTermAt i)

/-- Parent rational correspondences scale under algebraized formal-sum scaling. -/
theorem scale_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q : Rat)
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    (AlgebraizedContourFormalSum.scale q A).parentRationalCorrespondence =
      q • A.parentRationalCorrespondence :=
  Eq.trans
    (Finset.sum_congr
      rfl
      (fun i _ =>
        scale_parentRationalTermAt q A i))
    (Eq.trans
      (Finset.sum_congr
        rfl
        (fun i _ =>
          Eq.symm
            (Finsupp.smul_single'
              q
              (A.parentPrimeGeomAt i)
              (A.coefficientAt i))))
      (Eq.symm Finset.smul_sum))

/-- Adding a zero contour term does not change the parent rational correspondence. -/
theorem add_zero_term_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    {f : ContourCorQRawHom X Y}
    (B : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.add
        A (AlgebraizedContourFormalSum.term 0 B)).parentRationalCorrespondence =
      A.parentRationalCorrespondence :=
  Eq.trans
    (add_parentRationalCorrespondence A (AlgebraizedContourFormalSum.term 0 B))
    (Eq.trans
      (congrArg
        (fun R : RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme =>
          A.parentRationalCorrespondence + R)
        (term_parentRationalCorrespondence 0 B))
      (Eq.trans
        (congrArg
          (fun R : RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme =>
            A.parentRationalCorrespondence + R)
          (Finsupp.single_zero B.parentPrimeGeom))
        (add_zero A.parentRationalCorrespondence)))

/-- Collecting equal contour terms matches addition of coefficients in the parent image. -/
theorem collect_terms_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (q r : Rat) {f : ContourCorQRawHom X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk f) :
    (AlgebraizedContourFormalSum.add
        (AlgebraizedContourFormalSum.term q A)
        (AlgebraizedContourFormalSum.term r A)).parentRationalCorrespondence =
      (AlgebraizedContourFormalSum.term (q + r) A).parentRationalCorrespondence :=
  Eq.trans
    (add_parentRationalCorrespondence
      (AlgebraizedContourFormalSum.term q A)
      (AlgebraizedContourFormalSum.term r A))
    (Eq.trans
      (congrArg₂
        (fun R S : RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme =>
          R + S)
        (term_parentRationalCorrespondence q A)
        (term_parentRationalCorrespondence r A))
      (Eq.trans
        (Eq.symm (Finsupp.single_add A.parentPrimeGeom q r))
        (Eq.symm (term_parentRationalCorrespondence (q + r) A))))

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
