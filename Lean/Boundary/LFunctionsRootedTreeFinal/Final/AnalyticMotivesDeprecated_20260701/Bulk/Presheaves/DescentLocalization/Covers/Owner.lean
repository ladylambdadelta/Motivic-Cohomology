import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.DescentCovers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.Owner

/-!
# Descent covers for transfer presheaves

This file owns descent covers as seen by presheaves with contour transfers,
using the conservative contour-cover calculus from the object layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A contour descent cover as seen by a presheaf with transfers.  It records the
target bulk, a chosen contour cover from the object layer, and the presheaf to
which descent will be applied.
-/
structure TransferPresheafDescentCover
    (F : AnalyticPresheafWithTransfers) where
  target : ContourAdmissibleBulk
  cover : AnalyticContourDescentCover target.contour

namespace TransferPresheafDescentCover

/-- The target bulk of a descent cover for a transfer presheaf. -/
def targetBulk {F : AnalyticPresheafWithTransfers}
    (C : TransferPresheafDescentCover F) : ContourAdmissibleBulk :=
  C.target

/-- The object-layer contour descent cover. -/
def contourCover {F : AnalyticPresheafWithTransfers}
    (C : TransferPresheafDescentCover F) :
    AnalyticContourDescentCover C.target.contour :=
  C.cover

/-- The target contour stage of the object-layer descent cover. -/
def targetStage {F : AnalyticPresheafWithTransfers}
    (C : TransferPresheafDescentCover F) :
    C.target.contour.exhaustion.Stage :=
  C.cover.targetStage

/-- The contour stage selected by a cover-piece index. -/
def stageAt {F : AnalyticPresheafWithTransfers}
    (C : TransferPresheafDescentCover F)
    (i : C.cover.CoverIndex) :
    C.target.contour.exhaustion.Stage :=
  C.cover.stage i

/-- The refinement selected by a cover-piece index. -/
def refinementAt {F : AnalyticPresheafWithTransfers}
    (C : TransferPresheafDescentCover F)
    (i : C.cover.CoverIndex) :
    AnalyticContourRefinement
      (C.target.contour.exhaustion.chain (C.stageAt i))
      (C.target.contour.exhaustion.chain C.targetStage) :=
  C.cover.refinementAt i

end TransferPresheafDescentCover

/--
A contour descent cover for a functorial presheaf with transfers, obtained by
applying the existing cover calculus to its underlying lightweight presheaf.
-/
structure FunctorialTransferPresheafDescentCover
    (F : FunctorialAnalyticPresheafWithTransfers) where
  cover : TransferPresheafDescentCover F.forget

namespace FunctorialTransferPresheafDescentCover

/-- The target bulk of a functorial descent cover. -/
def targetBulk {F : FunctorialAnalyticPresheafWithTransfers}
    (C : FunctorialTransferPresheafDescentCover F) :
    ContourAdmissibleBulk :=
  C.cover.target

/-- The underlying lightweight descent cover. -/
def underlying {F : FunctorialAnalyticPresheafWithTransfers}
    (C : FunctorialTransferPresheafDescentCover F) :
    TransferPresheafDescentCover F.forget :=
  C.cover

/-- The target contour stage of a functorial descent cover. -/
def targetStage {F : FunctorialAnalyticPresheafWithTransfers}
    (C : FunctorialTransferPresheafDescentCover F) :
    C.targetBulk.contour.exhaustion.Stage :=
  C.cover.targetStage

/-- The contour stage selected by a functorial cover-piece index. -/
def stageAt {F : FunctorialAnalyticPresheafWithTransfers}
    (C : FunctorialTransferPresheafDescentCover F)
    (i : C.cover.cover.CoverIndex) :
    C.targetBulk.contour.exhaustion.Stage :=
  C.cover.stageAt i

end FunctorialTransferPresheafDescentCover

end AnalyticMotives
end LFunctions
end Boundary
