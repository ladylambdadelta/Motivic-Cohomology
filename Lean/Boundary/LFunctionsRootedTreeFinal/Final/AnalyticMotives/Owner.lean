import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Examples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Owner

/-!
# Analytic motives

This is the fresh analytic-motives lane.

The construction is organized as four mutually checked layers:

1. synthetic trace computad: expressions, rewrite rules, paths, coherences,
   and residue-channel presentations;
2. analytic realization: contour integrals, residues, channels, schedules,
   decay, and Fubini theorems interpret the computad;
3. algebraic-facing realization: Q-linear trace correspondences and the
   representable/Yoneda calculus interpret the same computad;
4. Q-linear trace-correspondence and motive construction over those
   realizations.

The synthetic layer records the computation; the realization layers prove what
the computation means.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top analytic-motives facade: certified presentations count rectangles by payload length. -/
theorem AnalyticMotivesFacade.residueChannel_importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  AnalyticMotivesRoot.rootFacade_residueChannel_importedRectangleCount_eq_length
    presentation

/-- Top analytic-motives facade: compact-generator composition is trace-hom composition. -/
theorem AnalyticMotivesFacade.compactGenerator_comp_traceHom
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    (left ≫ right).traceHom =
      left.traceHom ≫ right.traceHom :=
  AnalyticMotivesRoot.rootFacade_compactGenerator_comp_traceHom
    left
    right

/-- Top analytic-motives facade: representable sections recover trace correspondences. -/
theorem AnalyticMotivesFacade.representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  AnalyticMotivesRoot.rootFacade_representable_sections
    source
    target

/-- Top analytic-motives facade: Stokes analytic and algebraic realizations share a preimage. -/
theorem AnalyticMotivesFacade.stokes_realization_preimage_agreement
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) :=
  AnalyticMotivesRoot.rootFacade_stokes_realization_preimage_agreement
    source
    target

/-- Top analytic-motives facade: completed-zeta residue rectangle soundness is imported. -/
theorem AnalyticMotivesFacade.completedZeta_residueGenerator_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  AnalyticMotivesRoot.rootFacade_completedZeta_residueGenerator_sound
    f
    hPhi
    hR

end AnalyticMotives
end LFunctions
end Boundary
