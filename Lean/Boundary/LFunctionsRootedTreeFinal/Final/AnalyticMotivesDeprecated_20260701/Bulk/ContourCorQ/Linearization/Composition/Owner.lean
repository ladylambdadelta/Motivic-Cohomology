import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner

/-!
# Composition of rational contour formal sums

This owner defines the formal rational bilinear composition induced by a
contour-correspondence calculus.  The summands are indexed by pairs, with
coefficient product and raw correspondence composition supplied by the
calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQFormalSum

/-- Pairwise composition of finite rational contour formal sums. -/
def comp
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    ContourCorQFormalSum X Z where
  Index := S.Index × T.Index
  finiteIndex := inferInstance
  coefficient := fun p => S.coeffAt p.1 * T.coeffAt p.2
  correspondence := fun p =>
    C.composeAt (S.correspondenceAt p.1) (T.correspondenceAt p.2)

/-- The index type of a composed formal sum is the product of the input index types. -/
def compIndexEquiv
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    (comp C S T).Index = (S.Index × T.Index) :=
  rfl

/-- The coefficient of a composed formal sum is the product of coefficients. -/
theorem comp_coeffAt
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z)
    (i : S.Index) (j : T.Index) :
    (comp C S T).coeffAt (i, j) =
      S.coeffAt i * T.coeffAt j :=
  rfl

/-- The raw correspondence of a composed formal sum is the calculus composite. -/
theorem comp_correspondenceAt
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z)
    (i : S.Index) (j : T.Index) :
    (comp C S T).correspondenceAt (i, j) =
      C.composeAt (S.correspondenceAt i) (T.correspondenceAt j) :=
  rfl

end ContourCorQFormalSum

end AnalyticMotives
end LFunctions
end Boundary
