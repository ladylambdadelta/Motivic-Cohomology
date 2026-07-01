import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.Owner

/-!
# Bulk analytic motives

This directory is the upstream lane for the analytic-motive category.  Its
objects are bulk contour-admissible analytic objects; boundary streams,
vertical channels, packet norms, and Hilbert/GNS objects are realization
surfaces attached to these bulk objects.

The dependency order is:

1. object core: analytic bulks over the arithmetic base;
2. object systems: compactification boundary, contours, residues, descent, and
   interval admissibility;
3. morphisms: finite/proper contour-compatible analytic correspondences;
4. rational contour-correspondence category `ContourCor_Q`;
5. transfer algebra: `ℚ`-linear presheaves with transfers;
6. localization: descent and interval localization;
7. stabilization: Tate stabilization and compact/idempotent completion.

Declarations in this lane follow that order so the filesystem records the
proof graph.

Research input: the category is a bulk category presented by contour-compatible
correspondences.  Trace/boundary objects are realization surfaces downstream
from this lane.

Execution rule: implement a later item only after the owner files above it have
the declarations needed by its imports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Bulk-side analytic motive construction.  This is the off-realization lane:
contour-admissible bulks, their contour-compatible correspondence calculus,
and the presheaf/localization/Tate/compact-geometric construction generated
from that calculus.
-/
structure BulkAnalyticMotiveConstruction where
  correspondenceCalculus : ContourCorrespondenceCalculus
  presheaves : FunctorialAnalyticPresheafConstruction
  rational_correspondenceLaws_eq :
    presheaves.categoryData.correspondenceLaws =
      correspondenceCalculus.laws

namespace BulkAnalyticMotiveConstruction

/-- The contour-correspondence calculus underlying the bulk construction. -/
def calculus (B : BulkAnalyticMotiveConstruction) :
    ContourCorrespondenceCalculus :=
  B.correspondenceCalculus

/-- The presheaf/localization/Tate/compact construction over the bulk calculus. -/
def presheafConstruction (B : BulkAnalyticMotiveConstruction) :
    FunctorialAnalyticPresheafConstruction :=
  B.presheaves

/-- The rational contour category data used by the presheaf construction. -/
def rationalCategory (B : BulkAnalyticMotiveConstruction) :
    RationalContourCategoryData :=
  B.presheaves.categoryData

/-- The contour-correspondence laws used by rational transfers. -/
def rationalCorrespondenceLaws (B : BulkAnalyticMotiveConstruction) :
    ContourCorrespondenceCategoryLawData :=
  B.rationalCategory.correspondenceLaws

/-- The rational transfer category is linearized from the bulk correspondence calculus. -/
theorem rational_correspondenceLaws_compatibility
    (B : BulkAnalyticMotiveConstruction) :
    B.rationalCategory.correspondenceLaws =
      B.correspondenceCalculus.laws :=
  B.rational_correspondenceLaws_eq

/-- The object type of the bulk correspondence calculus. -/
def correspondenceObject (B : BulkAnalyticMotiveConstruction) : Type :=
  B.correspondenceCalculus.object

/-- The morphism type of the bulk correspondence calculus. -/
def correspondenceHom (B : BulkAnalyticMotiveConstruction)
    (X Y : B.correspondenceObject) : Type :=
  B.correspondenceCalculus.hom X Y

/-- The identity contour correspondence selected by the bulk calculus. -/
def identityAt (B : BulkAnalyticMotiveConstruction)
    (X : ContourAdmissibleBulk) :
    ContourAnalyticCorrespondence X X :=
  B.correspondenceCalculus.identityAt X

/-- The composite contour correspondence selected by the bulk calculus. -/
def composeAt (B : BulkAnalyticMotiveConstruction)
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) :
    ContourAnalyticCorrespondence X Z :=
  B.correspondenceCalculus.composeAt F G

/-- Left identity law for the bulk correspondence calculus. -/
theorem left_identity_eq (B : BulkAnalyticMotiveConstruction)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    B.composeAt (B.identityAt X) F = F :=
  ContourCorrespondenceCalculus.left_identity_eq
    B.correspondenceCalculus F

/-- Right identity law for the bulk correspondence calculus. -/
theorem right_identity_eq (B : BulkAnalyticMotiveConstruction)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    B.composeAt F (B.identityAt Y) = F :=
  ContourCorrespondenceCalculus.right_identity_eq
    B.correspondenceCalculus F

/-- Associativity law for the bulk correspondence calculus. -/
theorem associativity_eq (B : BulkAnalyticMotiveConstruction)
    {W X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence W X)
    (G : ContourAnalyticCorrespondence X Y)
    (H : ContourAnalyticCorrespondence Y Z) :
    B.composeAt (B.composeAt F G) H =
      B.composeAt F (B.composeAt G H) :=
  ContourCorrespondenceCalculus.associativity_eq
    B.correspondenceCalculus F G H

/-- The transfer action carried by the bulk presheaf construction. -/
def transferAction (B : BulkAnalyticMotiveConstruction) :
    RationalContourTransferAction B.presheaves.transfers.presheaf :=
  B.presheaves.transferAction

/--
Reindexing invariance for the transfer action carried by the bulk
construction.
-/
theorem reindexing_pullback_eq
    (B : BulkAnalyticMotiveConstruction)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (B.transferAction).act f = (B.transferAction).act g :=
  FunctorialAnalyticPresheafConstruction.reindexing_pullback_eq
    B.presheaves f g R

/-- Left identity for the transfer action carried by the bulk construction. -/
theorem left_identity_pullback_eq
    (B : BulkAnalyticMotiveConstruction)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (B.transferAction).act
        (B.rationalCategory.compose (B.rationalCategory.identity X) f) =
      (B.transferAction).act f :=
  FunctorialAnalyticPresheafConstruction.left_identity_pullback_eq
    B.presheaves f

/-- Right identity for the transfer action carried by the bulk construction. -/
theorem right_identity_pullback_eq
    (B : BulkAnalyticMotiveConstruction)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (B.transferAction).act
        (B.rationalCategory.compose f (B.rationalCategory.identity Y)) =
      (B.transferAction).act f :=
  FunctorialAnalyticPresheafConstruction.right_identity_pullback_eq
    B.presheaves f

/-- Associativity for the transfer action carried by the bulk construction. -/
theorem associativity_pullback_eq
    (B : BulkAnalyticMotiveConstruction)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (B.transferAction).act
        (B.rationalCategory.compose (B.rationalCategory.compose f g) h) =
      (B.transferAction).act
        (B.rationalCategory.compose f (B.rationalCategory.compose g h)) :=
  FunctorialAnalyticPresheafConstruction.associativity_pullback_eq
    B.presheaves f g h

end BulkAnalyticMotiveConstruction

end AnalyticMotives
end LFunctions
end Boundary
