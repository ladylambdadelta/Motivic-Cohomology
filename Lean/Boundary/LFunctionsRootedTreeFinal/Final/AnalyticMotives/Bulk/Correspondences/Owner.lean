import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Refinement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.ResidueCompatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Constructed.Owner

/-!
# Contour-compatible analytic correspondences

This directory is the morphism-side analogue of finite correspondences.  The
category is meant to start from analytic correspondences equipped with contour
transport and residue compatibility, rather than from ordinary maps with
contours added later.

The proof order is support, allowed refinement, transport, residue
compatibility, and then composition.

Research input: contour theory enters at the morphism level.  A correspondence
is not a plain analytic map with trace data attached later; it carries support,
transport, and residue compatibility before it becomes a transfer.

Execution order from this directory:

1. support composition for finite/proper analytic supports;
2. transport composition for contour systems;
3. residue compatibility under composed transports;
4. identity and associativity laws for contour-compatible correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The contour-compatible correspondence calculus used by analytic motives:
objects are contour-admissible analytic bulks, morphisms are contour-compatible
analytic correspondences, and identities/composition satisfy the category laws.
-/
structure ContourCorrespondenceCalculus where
  laws : ContourCorrespondenceCategoryLawData

namespace ContourCorrespondenceCalculus

/-- The object type of the contour-correspondence calculus. -/
def object (C : ContourCorrespondenceCalculus) : Type :=
  ContourCorrespondenceObject

/-- The morphism type of the contour-correspondence calculus. -/
def hom (C : ContourCorrespondenceCalculus)
    (X Y : C.object) : Type :=
  ContourCorrespondenceHom X Y

/-- The category-level data exposed to the transfer-presheaf layer. -/
def categoryData (C : ContourCorrespondenceCalculus) :
    ContourCorrespondenceCategoryData :=
  ContourCorrespondenceCategoryData.analytic C.laws

/-- The identity correspondence selected by the calculus. -/
def identityAt (C : ContourCorrespondenceCalculus)
    (X : ContourAdmissibleBulk) :
    ContourAnalyticCorrespondence X X :=
  C.laws.identityAt X

/-- The composite correspondence selected by the calculus. -/
def composeAt (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) :
    ContourAnalyticCorrespondence X Z :=
  C.laws.composeAt F G

/-- Left identity law for contour-compatible correspondence composition. -/
theorem left_identity_eq (C : ContourCorrespondenceCalculus)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    C.composeAt (C.identityAt X) F = F :=
  ContourCorrespondenceCategoryLawData.left_identity_eq C.laws F

/-- Right identity law for contour-compatible correspondence composition. -/
theorem right_identity_eq (C : ContourCorrespondenceCalculus)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    C.composeAt F (C.identityAt Y) = F :=
  ContourCorrespondenceCategoryLawData.right_identity_eq C.laws F

/-- Associativity law for contour-compatible correspondence composition. -/
theorem associativity_eq (C : ContourCorrespondenceCalculus)
    {W X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence W X)
    (G : ContourAnalyticCorrespondence X Y)
    (H : ContourAnalyticCorrespondence Y Z) :
    C.composeAt (C.composeAt F G) H =
      C.composeAt F (C.composeAt G H) :=
  ContourCorrespondenceCategoryLawData.associativity_eq C.laws F G H

end ContourCorrespondenceCalculus

end AnalyticMotives
end LFunctions
end Boundary
