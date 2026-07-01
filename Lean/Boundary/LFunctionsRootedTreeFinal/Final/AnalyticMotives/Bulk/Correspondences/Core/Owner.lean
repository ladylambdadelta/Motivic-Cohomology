import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.ResidueCompatibility.Owner

/-!
# Core contour-compatible analytic correspondences

This file owns the primitive morphism-side object: a finite/proper analytic
support, contour transport, and residue compatibility.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An RH-backed contour correspondence from `X` to `Y`.

At each pair of contour heights it is a relation between the imported RH
singular supports of the two rectangles.  This is the constructive analogue of
finite correspondences at the current analytic level: support membership is
not a later law field, but part of the relation's definition.
-/
structure RHContourRelationCorrespondence
    (X Y : RHContourAdmissibleBulk) where
  relation : X.Stage → Y.Stage → Set (ℂ × ℂ)
  source_mem :
    (TX : X.Stage) → (TY : Y.Stage) → (p : ℂ × ℂ) →
      p ∈ relation TX TY → p.1 ∈ X.singularSupport TX
  target_mem :
    (TX : X.Stage) → (TY : Y.Stage) → (p : ℂ × ℂ) →
      p ∈ relation TX TY → p.2 ∈ Y.singularSupport TY

namespace RHContourRelationCorrespondence

/-- Membership in a contour relation forces source singular support. -/
theorem mem_source {X Y : RHContourAdmissibleBulk}
    (C : RHContourRelationCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ C.relation TX TY) :
    p.1 ∈ X.singularSupport TX :=
  C.source_mem TX TY p hp

/-- Membership in a contour relation forces target singular support. -/
theorem mem_target {X Y : RHContourAdmissibleBulk}
    (C : RHContourRelationCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ C.relation TX TY) :
    p.2 ∈ Y.singularSupport TY :=
  C.target_mem TX TY p hp

/-- A relation member has source singularity in the imported RH sense. -/
theorem source_singular {X Y : RHContourAdmissibleBulk}
    (C : RHContourRelationCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ C.relation TX TY) :
    X.core.singularPoint p.1 :=
  X.singularSupport_singular TX p.1 (C.mem_source TX TY p hp)

/-- A relation member has target singularity in the imported RH sense. -/
theorem target_singular {X Y : RHContourAdmissibleBulk}
    (C : RHContourRelationCorrespondence X Y)
    (TX : X.Stage) (TY : Y.Stage) (p : ℂ × ℂ)
    (hp : p ∈ C.relation TX TY) :
    Y.core.singularPoint p.2 :=
  Y.singularSupport_singular TY p.2 (C.mem_target TX TY p hp)

end RHContourRelationCorrespondence

/--
A contour-compatible analytic correspondence from `X` to `Y`.  This is the
morphism-side primitive for the transfer category: finite/proper support,
contour transport, and residue compatibility are all present before any trace
realization is applied.
-/
structure ContourAnalyticCorrespondence
    (X Y : ContourAdmissibleBulk) where
  support : AnalyticCorrespondenceSupport X Y
  transport : AnalyticContourTransport support
  residue : AnalyticResidueCompatibility transport

namespace ContourAnalyticCorrespondence

/-- The finite/proper support underlying a contour-compatible correspondence. -/
def supportData {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AnalyticCorrespondenceSupport X Y :=
  C.support

/-- The contour transport underlying a contour-compatible correspondence. -/
def transportData {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AnalyticContourTransport C.support :=
  C.transport

/-- The residue compatibility underlying a contour-compatible correspondence. -/
def residueData {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AnalyticResidueCompatibility C.transport :=
  C.residue

/-- The support core underlying a contour-compatible correspondence. -/
def supportCore {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) : AnalyticBulkCore :=
  C.support.supportCore

/-- The map from the correspondence support to the source bulk core. -/
def mapToSource {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AnalyticBulkCoreHom C.supportCore X.core :=
  C.support.mapToSource

/-- The map from the correspondence support to the target bulk core. -/
def mapToTarget {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AnalyticBulkCoreHom C.supportCore Y.core :=
  C.support.mapToTarget

/-- The support map over the source is proper. -/
theorem proper_over_source {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AlgebraicGeometry.IsProper (C.mapToSource).baseMap :=
  AnalyticCorrespondenceSupport.proper_over_source C.support

/-- The support map over the target is finite. -/
theorem finite_over_target {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y) :
    AlgebraicGeometry.IsFinite (C.mapToTarget).baseMap :=
  AnalyticCorrespondenceSupport.finite_over_target C.support

/-- The target contour stage assigned by a contour-compatible correspondence. -/
def stageAt {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y)
    (s : X.contour.exhaustion.Stage) : Y.contour.exhaustion.Stage :=
  C.transport.stageAt s

/-- The target contour chain assigned by a contour-compatible correspondence. -/
def chainAt {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y)
    (s : X.contour.exhaustion.Stage) :
    AnalyticContourChain Y.boundary :=
  C.transport.chainAt s

/-- The target boundary face assigned by a contour-compatible correspondence. -/
def faceAt {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y)
    (i : X.boundary.FaceIndex) : Y.boundary.FaceIndex :=
  C.transport.faceAt i

/-- The residue commutation datum at a source contour stage and boundary face. -/
def residueCommutationAt {X Y : ContourAdmissibleBulk}
    (C : ContourAnalyticCorrespondence X Y)
    (s : X.contour.exhaustion.Stage) (i : X.boundary.FaceIndex) :
    AnalyticResidueCommutation s i :=
  C.residue.commutationAt s i

end ContourAnalyticCorrespondence

end AnalyticMotives
end LFunctions
end Boundary
