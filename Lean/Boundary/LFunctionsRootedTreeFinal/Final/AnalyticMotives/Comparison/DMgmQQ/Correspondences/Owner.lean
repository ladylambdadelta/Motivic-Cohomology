import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Generators.Owner

/-!
# Correspondence comparison with `DM_gm(ℚ)_ℚ`

This file owns the comparison between contour-compatible analytic
correspondences and algebraic finite correspondences after analytification.
Contour transport and residue compatibility remain part of the analytic
correspondence data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An abstract morphism interface for the `DM_gm(ℚ)_ℚ` comparison target.
-/
structure DMgmQQMorphismInterface
    (T : DMgmQQTargetInterface) where
  Hom : T.Object → T.Object → Type

/--
Category-level target morphism calculus for the `DM_gm(ℚ)_ℚ` comparison
interface.
-/
structure DMgmQQMorphismCategoryInterface
    {T : DMgmQQTargetInterface}
    (M : DMgmQQMorphismInterface T) where
  identity : (X : T.Object) → M.Hom X X
  compose :
    {X Y Z : T.Object} →
      M.Hom X Y → M.Hom Y Z → M.Hom X Z
  left_identity :
    {X Y : T.Object} →
      (f : M.Hom X Y) →
        compose (identity X) f = f
  right_identity :
    {X Y : T.Object} →
      (f : M.Hom X Y) →
        compose f (identity Y) = f
  associativity :
    {W X Y Z : T.Object} →
      (f : M.Hom W X) →
        (g : M.Hom X Y) →
          (h : M.Hom Y Z) →
            compose (compose f g) h =
              compose f (compose g h)

namespace DMgmQQMorphismCategoryInterface

/-- The identity morphism in the target comparison calculus. -/
def identityAt {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQMorphismCategoryInterface M)
    (X : T.Object) : M.Hom X X :=
  C.identity X

/-- The composite morphism in the target comparison calculus. -/
def composeAt {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQMorphismCategoryInterface M)
    {X Y Z : T.Object}
    (f : M.Hom X Y) (g : M.Hom Y Z) :
    M.Hom X Z :=
  C.compose f g

/-- Left identity law in the target comparison calculus. -/
theorem left_identity_eq {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQMorphismCategoryInterface M)
    {X Y : T.Object} (f : M.Hom X Y) :
    C.composeAt (C.identityAt X) f = f :=
  C.left_identity f

/-- Right identity law in the target comparison calculus. -/
theorem right_identity_eq {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQMorphismCategoryInterface M)
    {X Y : T.Object} (f : M.Hom X Y) :
    C.composeAt f (C.identityAt Y) = f :=
  C.right_identity f

/-- Associativity law in the target comparison calculus. -/
theorem associativity_eq {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQMorphismCategoryInterface M)
    {W X Y Z : T.Object}
    (f : M.Hom W X) (g : M.Hom X Y) (h : M.Hom Y Z) :
    C.composeAt (C.composeAt f g) h =
      C.composeAt f (C.composeAt g h) :=
  C.associativity f g h

end DMgmQQMorphismCategoryInterface

/--
Comparison of a contour-compatible analytic correspondence with a target
motivic correspondence.
-/
structure DMgmQQCorrespondenceComparison
    {T : DMgmQQTargetInterface}
    (M : DMgmQQMorphismInterface T)
    {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) where
  sourceTarget : T.Object
  targetTarget : T.Object
  targetMorphism : M.Hom sourceTarget targetTarget

namespace DMgmQQCorrespondenceComparison

/-- The target-side morphism assigned to an analytic contour correspondence. -/
def morphism {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    {X Y : ContourAdmissibleBulk}
    {C : ContourAnalyticCorrespondence X Y}
    (K : DMgmQQCorrespondenceComparison M C) :
    M.Hom K.sourceTarget K.targetTarget :=
  K.targetMorphism

end DMgmQQCorrespondenceComparison

/--
Category-level comparison from the analytic contour-correspondence calculus to
the target motivic morphism calculus.
-/
structure DMgmQQCorrespondenceCalculusComparison
    {T : DMgmQQTargetInterface}
    (M : DMgmQQMorphismInterface T) where
  analyticCalculus : ContourCorrespondenceCalculus
  targetCategory : DMgmQQMorphismCategoryInterface M
  objectMap : ContourAdmissibleBulk → T.Object
  morphismMap :
    {X Y : ContourAdmissibleBulk} →
      ContourAnalyticCorrespondence X Y →
        M.Hom (objectMap X) (objectMap Y)
  identity_compat :
    (X : ContourAdmissibleBulk) →
      morphismMap (analyticCalculus.identityAt X) =
        targetCategory.identityAt (objectMap X)
  composition_compat :
    {X Y Z : ContourAdmissibleBulk} →
      (F : ContourAnalyticCorrespondence X Y) →
        (G : ContourAnalyticCorrespondence Y Z) →
          morphismMap (analyticCalculus.composeAt F G) =
            targetCategory.composeAt (morphismMap F) (morphismMap G)

namespace DMgmQQCorrespondenceCalculusComparison

/-- The analytic contour-correspondence calculus being compared. -/
def analytic {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M) :
    ContourCorrespondenceCalculus :=
  C.analyticCalculus

/-- The target morphism category calculus used in the comparison. -/
def target {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M) :
    DMgmQQMorphismCategoryInterface M :=
  C.targetCategory

/-- The target object assigned to a contour-admissible bulk. -/
def objectAt {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M)
    (X : ContourAdmissibleBulk) : T.Object :=
  C.objectMap X

/-- The target morphism assigned to a contour-compatible correspondence. -/
def morphismAt {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    M.Hom (C.objectAt X) (C.objectAt Y) :=
  C.morphismMap F

/-- Identity compatibility for the category-level correspondence comparison. -/
theorem identity_compatibility {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M)
    (X : ContourAdmissibleBulk) :
    C.morphismAt (C.analytic.identityAt X) =
      C.target.identityAt (C.objectAt X) :=
  C.identity_compat X

/-- Composition compatibility for the category-level correspondence comparison. -/
theorem composition_compatibility {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (C : DMgmQQCorrespondenceCalculusComparison M)
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) :
    C.morphismAt (C.analytic.composeAt F G) =
      C.target.composeAt (C.morphismAt F) (C.morphismAt G) :=
  C.composition_compat F G

end DMgmQQCorrespondenceCalculusComparison

end AnalyticMotives
end LFunctions
end Boundary
