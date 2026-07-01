import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Owner

/-!
# Contour-admissible analytic bulks

This owner collects the object-side inputs for analytic motives.  The split is:

* `Core`: the analytic bulk object itself;
* `BoundarySystem`: compactification and boundary strata;
* `ContourSystem`: contour exhaustions and deformation data;
* `ResidueLedger`: boundary residue maps as morphism-level data;
* `DescentInterval`: descent covers and interval-homotopy admissibility.

Trace streams and channel sums are deliberately downstream from this directory.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The four contour faces of an RH explicit-formula rectangle. -/
inductive RHContourBoundaryFace where
  | right
  | left
  | top
  | bottom
deriving DecidableEq

/--
The constructive contour-admissible bulk used by the analytic-motives lane.
It is not an abstract package of obligations: its core is the RH explicit
formula contour package, its stages are contour heights, and its boundary
faces are the four sides of the imported RH rectangle.
-/
structure RHContourAdmissibleBulk where
  core : ConstructiveAnalyticBulkCore

namespace RHContourBoundaryFace

/-- Reverse the orientation of a rectangle face. -/
def opposite : RHContourBoundaryFace → RHContourBoundaryFace
  | right => left
  | left => right
  | top => bottom
  | bottom => top

/-- The opposite-face operation is involutive. -/
theorem opposite_opposite (f : RHContourBoundaryFace) :
    opposite (opposite f) = f :=
  match f with
  | right => rfl
  | left => rfl
  | top => rfl
  | bottom => rfl

end RHContourBoundaryFace

namespace RHContourAdmissibleBulk

/-- The RH packet carried by a constructive contour-admissible bulk. -/
def packet (X : RHContourAdmissibleBulk) :
    ZetaAdmissibleFunction :=
  X.core.packet

/-- The RH contour family carried by a constructive contour-admissible bulk. -/
def contourFamily (X : RHContourAdmissibleBulk) :
    RHContourFamily :=
  X.core.contourFamily

/-- A contour stage is a height parameter for the imported RH rectangle family. -/
abbrev Stage (_X : RHContourAdmissibleBulk) : Type :=
  ℝ

/-- The rectangle at a contour stage. -/
def rectangle (X : RHContourAdmissibleBulk) (T : X.Stage) :
    RHContourRectangle :=
  X.core.rectangle T

/-- The boundary of the rectangle at a contour stage. -/
def boundary (X : RHContourAdmissibleBulk) (T : X.Stage) : Set ℂ :=
  X.core.boundary T

/-- The interior of the rectangle at a contour stage. -/
def interior (X : RHContourAdmissibleBulk) (T : X.Stage) : Set ℂ :=
  X.core.interior T

/-- Boundary faces are exactly the four sides of the RH rectangle. -/
abbrev FaceIndex (_X : RHContourAdmissibleBulk) : Type :=
  RHContourBoundaryFace

/-- The parametrized path of a rectangle face at stage `T`. -/
def facePath (X : RHContourAdmissibleBulk)
    (T : X.Stage) : X.FaceIndex → ℝ → ℂ
  | RHContourBoundaryFace.right => X.core.rightPath T
  | RHContourBoundaryFace.left => X.core.leftPath T
  | RHContourBoundaryFace.top => X.core.topPath T
  | RHContourBoundaryFace.bottom => X.core.bottomPath T

/-- The trace support at stage `T`: imported RH singular points inside the rectangle. -/
def singularSupport (X : RHContourAdmissibleBulk) (T : X.Stage) : Set ℂ :=
  X.core.rectangleSingularSupport T

/-- Singular support points are singular for the imported RH singular predicate. -/
theorem singularSupport_singular
    (X : RHContourAdmissibleBulk) (T : X.Stage) (z : ℂ)
    (hz : z ∈ X.singularSupport T) :
    X.core.singularPoint z :=
  RHContourBulkCore.rectangleSingularSupport_singular X.core T z hz

/-- Singular support points lie in the selected RH rectangle. -/
theorem singularSupport_mem_rectangle
    (X : RHContourAdmissibleBulk) (T : X.Stage) (z : ℂ)
    (hz : z ∈ X.singularSupport T) :
    z ∈ X.core.rectangleSet T :=
  RHContourBulkCore.rectangleSingularSupport_mem_rectangleSet X.core T z hz

/-- The real edge of the rectangle is inherited from the imported contour family. -/
def realEdge (X : RHContourAdmissibleBulk) : ℝ :=
  X.core.realEdge

/-- The rectangle stores the stage as its height. -/
theorem rectangle_height (X : RHContourAdmissibleBulk) (T : X.Stage) :
    (X.rectangle T).T = T :=
  RHContourBulkCore.rectangle_T X.core T

end RHContourAdmissibleBulk

/--
A contour-admissible analytic bulk.  This is the object-side input for the
analytic-contour correspondence category: a small bulk core, boundary system,
contour system, categorical residue ledger, and conservative descent/interval
data.
-/
structure ContourAdmissibleBulk where
  core : AnalyticBulkCore
  boundary : AnalyticBoundarySystem core
  contour : AnalyticContourSystem boundary
  residue : AnalyticResidueLedger contour
  descentInterval : AnalyticDescentIntervalData contour

/--
The intended object type of the analytic bulk category.

This is deliberately the full contour-admissible bulk, not the RH rectangle
adapter above and not a boundary-stream realization.  An RH contour package can
enter the final category only after its carrier, compactification, contour
system, residue ledger, and descent/interval data have been constructed.
-/
abbrev ContourAdmissibleAnalyticBulk :=
  ContourAdmissibleBulk

namespace ContourAdmissibleBulk

/-- Assemble a full contour-admissible bulk from the split admissibility data. -/
def ofAdmissibility (X : AnalyticBulkCore)
    (A : ContourBulkAdmissibility X) :
    ContourAdmissibleBulk where
  core := X
  boundary := A.boundary.system
  contour := A.contour.system
  residue := A.residue.ledger
  descentInterval := {
    interval := A.interval.interval
    CoverIndex := A.descent.CoverIndex
    cover := A.descent.cover
  }

/-- The analytic bulk core underlying a contour-admissible bulk. -/
def bulkCore (X : ContourAdmissibleBulk) : AnalyticBulkCore :=
  X.core

/-- The boundary system underlying a contour-admissible bulk. -/
def boundarySystem (X : ContourAdmissibleBulk) :
    AnalyticBoundarySystem X.core :=
  X.boundary

/-- The contour system underlying a contour-admissible bulk. -/
def contourSystem (X : ContourAdmissibleBulk) :
    AnalyticContourSystem X.boundary :=
  X.contour

/-- The residue ledger underlying a contour-admissible bulk. -/
def residueLedger (X : ContourAdmissibleBulk) :
    AnalyticResidueLedger X.contour :=
  X.residue

/-- The descent and interval data underlying a contour-admissible bulk. -/
def descentIntervalData (X : ContourAdmissibleBulk) :
    AnalyticDescentIntervalData X.contour :=
  X.descentInterval

/-- The compactification carried by the boundary system of a contour-admissible bulk. -/
def compactification (X : ContourAdmissibleBulk) :
    AnalyticBulkCompactification X.core :=
  X.boundary.compactification

/-- The boundary face selected by an index of a contour-admissible bulk. -/
def faceAt (X : ContourAdmissibleBulk)
    (i : X.boundary.FaceIndex) :
    AnalyticBoundaryFace X.boundary.compactification :=
  X.boundary.faceAt i

/-- The contour exhaustion carried by a contour-admissible bulk. -/
def contourExhaustion (X : ContourAdmissibleBulk) :
    AnalyticContourExhaustion X.boundary :=
  X.contour.exhaustion

/-- The contour chain selected by a contour stage of a contour-admissible bulk. -/
def contourChainAt (X : ContourAdmissibleBulk)
    (s : X.contour.exhaustion.Stage) :
    AnalyticContourChain X.boundary :=
  X.contour.chainAt s

/-- The residue map selected by a contour stage and boundary face. -/
def residueAt (X : ContourAdmissibleBulk)
    (s : X.contour.exhaustion.Stage)
    (i : X.boundary.FaceIndex) :
    AnalyticResidueMap (X.contour.exhaustion.chain s) (X.boundary.face i) :=
  X.residue.residueAt s i

/-- The residue-depth filtration carried by a contour-admissible bulk. -/
def residueFiltration (X : ContourAdmissibleBulk) :
    AnalyticResidueFiltration X.boundary :=
  X.residue.filtrationData

/-- The residue depth of a boundary face of a contour-admissible bulk. -/
def residueDepthAt (X : ContourAdmissibleBulk)
    (i : X.boundary.FaceIndex) : Nat :=
  X.residueFiltration.depthAt i

/-- Boundary incidence does not increase residue depth. -/
theorem incidence_residueDepth_le (X : ContourAdmissibleBulk)
    {lower upper : X.boundary.FaceIndex}
    (I : X.boundary.IncidenceIndex lower upper) :
    X.residueDepthAt upper ≤ X.residueDepthAt lower :=
  AnalyticResidueFiltration.incidence_le X.residueFiltration I

/-- The interval object selected by a contour-admissible bulk. -/
def intervalObject (X : ContourAdmissibleBulk) :
    AnalyticIntervalObject X.core :=
  X.descentInterval.intervalObject

/-- A selected descent cover of a contour-admissible bulk. -/
def descentCoverAt (X : ContourAdmissibleBulk)
    (i : X.descentInterval.CoverIndex) :
    AnalyticContourDescentCover X.contour :=
  X.descentInterval.coverAt i

/-- The target stage of a selected descent cover. -/
def descentCoverTargetStage (X : ContourAdmissibleBulk)
    (i : X.descentInterval.CoverIndex) :
    X.contour.exhaustion.Stage :=
  (X.descentCoverAt i).targetStage

/-- The zero endpoint of the interval object of a contour-admissible bulk. -/
def intervalZeroEndpoint (X : ContourAdmissibleBulk) :
    AnalyticBulkCoreHom X.core (X.intervalObject).intervalCore :=
  (X.intervalObject).zeroEndpoint

/-- The one endpoint of the interval object of a contour-admissible bulk. -/
def intervalOneEndpoint (X : ContourAdmissibleBulk) :
    AnalyticBulkCoreHom X.core (X.intervalObject).intervalCore :=
  (X.intervalObject).oneEndpoint

/-- The interval projection of a contour-admissible bulk. -/
def intervalProjection (X : ContourAdmissibleBulk) :
    AnalyticBulkCoreHom (X.intervalObject).intervalCore X.core :=
  (X.intervalObject).projection

/-- The zero endpoint followed by interval projection is the identity. -/
theorem interval_zero_projection (X : ContourAdmissibleBulk) :
    AnalyticBulkCoreHom.comp
        (X.intervalObject).zero
        (X.intervalObject).projection =
      AnalyticBulkCoreHom.id X.core :=
  (X.intervalObject).zero_projection

/-- The one endpoint followed by interval projection is the identity. -/
theorem interval_one_projection (X : ContourAdmissibleBulk) :
    AnalyticBulkCoreHom.comp
        (X.intervalObject).one
        (X.intervalObject).projection =
      AnalyticBulkCoreHom.id X.core :=
  (X.intervalObject).one_projection

end ContourAdmissibleBulk

end AnalyticMotives
end LFunctions
end Boundary
