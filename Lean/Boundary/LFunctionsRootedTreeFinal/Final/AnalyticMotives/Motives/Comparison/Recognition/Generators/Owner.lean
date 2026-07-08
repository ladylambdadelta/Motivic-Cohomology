import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.StableSource.Preimage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Generators.Owner

/-!
# Recognition generator bridges

This file is the first recognition-facing bridge: each analytic rewrite
generator map, viewed as a Yoneda-source representable morphism, determines
the stable-source morphism of its certified trace correspondence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source compact generator of a Stokes rewrite. -/
def TraceAnalyticMotiveRecognition.stokesSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.stokes source target).sourceObject

/-- The target compact generator of a Stokes rewrite. -/
def TraceAnalyticMotiveRecognition.stokesTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.stokes source target).targetObject

/-- The stable-source morphism represented by the analytic Stokes map. -/
def TraceAnalyticMotiveRecognition.stokesStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.stokesSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.stokesTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.stokesMap source target)

/-- The Stokes Yoneda-source preimage is the certified Stokes trace hom. -/
theorem TraceAnalyticMotiveRecognition.stokes_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticRealizationGenerator.stokesMap_preimage source target

/-- The stable-source Stokes map is the source-trace image of the certified
Stokes trace hom. -/
theorem TraceAnalyticMotiveRecognition.stokesStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.stokesStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.stokes source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.stokesMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.stokes_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a residue rewrite. -/
def TraceAnalyticMotiveRecognition.residueSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.residue source target).sourceObject

/-- The target compact generator of a residue rewrite. -/
def TraceAnalyticMotiveRecognition.residueTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.residue source target).targetObject

/-- The stable-source morphism represented by the analytic residue map. -/
def TraceAnalyticMotiveRecognition.residueStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.residueSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.residueTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.residueMap source target)

/-- The residue Yoneda-source preimage is the certified residue trace hom. -/
theorem TraceAnalyticMotiveRecognition.residue_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealizationGenerator.residueMap_preimage source target

/-- The stable-source residue map is the source-trace image of the certified
residue trace hom. -/
theorem TraceAnalyticMotiveRecognition.residueStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.residueStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.residue source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.residueMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.residue_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a channel rewrite. -/
def TraceAnalyticMotiveRecognition.channelSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.channel source target).sourceObject

/-- The target compact generator of a channel rewrite. -/
def TraceAnalyticMotiveRecognition.channelTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.channel source target).targetObject

/-- The stable-source morphism represented by the analytic channel map. -/
def TraceAnalyticMotiveRecognition.channelStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.channelSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.channelTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.channelMap source target)

/-- The channel Yoneda-source preimage is the certified channel trace hom. -/
theorem TraceAnalyticMotiveRecognition.channel_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticRealizationGenerator.channelMap_preimage source target

/-- The stable-source channel map is the source-trace image of the certified
channel trace hom. -/
theorem TraceAnalyticMotiveRecognition.channelStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.channelStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.channel source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.channelMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.channel_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a refinement rewrite. -/
def TraceAnalyticMotiveRecognition.refinementSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.refinement source target).sourceObject

/-- The target compact generator of a refinement rewrite. -/
def TraceAnalyticMotiveRecognition.refinementTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.refinement source target).targetObject

/-- The stable-source morphism represented by the analytic refinement map. -/
def TraceAnalyticMotiveRecognition.refinementStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.refinementSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.refinementTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.refinementMap source target)

/-- The refinement Yoneda-source preimage is the certified refinement trace hom. -/
theorem TraceAnalyticMotiveRecognition.refinement_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticRealizationGenerator.refinementMap_preimage source target

/-- The stable-source refinement map is the source-trace image of the certified
refinement trace hom. -/
theorem TraceAnalyticMotiveRecognition.refinementStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.refinementStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.refinement source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.refinementMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.refinement_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a schedule rewrite. -/
def TraceAnalyticMotiveRecognition.scheduleSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.schedule source target).sourceObject

/-- The target compact generator of a schedule rewrite. -/
def TraceAnalyticMotiveRecognition.scheduleTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.schedule source target).targetObject

/-- The stable-source morphism represented by the analytic schedule map. -/
def TraceAnalyticMotiveRecognition.scheduleStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.scheduleSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.scheduleTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.scheduleMap source target)

/-- The schedule Yoneda-source preimage is the certified schedule trace hom. -/
theorem TraceAnalyticMotiveRecognition.schedule_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticRealizationGenerator.scheduleMap_preimage source target

/-- The stable-source schedule map is the source-trace image of the certified
schedule trace hom. -/
theorem TraceAnalyticMotiveRecognition.scheduleStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.scheduleStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.schedule source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.scheduleMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.schedule_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a weight-drop rewrite. -/
def TraceAnalyticMotiveRecognition.weightDropSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.weightDrop source target).sourceObject

/-- The target compact generator of a weight-drop rewrite. -/
def TraceAnalyticMotiveRecognition.weightDropTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.weightDrop source target).targetObject

/-- The stable-source morphism represented by the analytic weight-drop map. -/
def TraceAnalyticMotiveRecognition.weightDropStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.weightDropSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.weightDropTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.weightDropMap source target)

/-- The weight-drop Yoneda-source preimage is the certified weight-drop trace hom. -/
theorem TraceAnalyticMotiveRecognition.weightDrop_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticRealizationGenerator.weightDropMap_preimage source target

/-- The stable-source weight-drop map is the source-trace image of the certified
weight-drop trace hom. -/
theorem TraceAnalyticMotiveRecognition.weightDropStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.weightDropStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.weightDrop source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.weightDropMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.weightDrop_yonedaSourcePreimageTraceHom
        source
        target))

/-- The source compact generator of a Fubini rewrite. -/
def TraceAnalyticMotiveRecognition.fubiniSourceGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.fubini source target).sourceObject

/-- The target compact generator of a Fubini rewrite. -/
def TraceAnalyticMotiveRecognition.fubiniTargetGenerator
    (source target : QTraceExpression) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject
    (TraceRewriteGenerator.fubini source target).targetObject

/-- The stable-source morphism represented by the analytic Fubini map. -/
def TraceAnalyticMotiveRecognition.fubiniStableSourceMap
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.fubiniSourceGenerator source target) ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj
        (TraceAnalyticMotiveRecognition.fubiniTargetGenerator source target) :=
  TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    (TraceAnalyticRealizationGenerator.fubiniMap source target)

/-- The Fubini Yoneda-source preimage is the certified Fubini trace hom. -/
theorem TraceAnalyticMotiveRecognition.fubini_yonedaSourcePreimageTraceHom
    (source target : QTraceExpression) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticRealizationGenerator.fubiniMap_preimage source target

/-- The stable-source Fubini map is the source-trace image of the certified
Fubini trace hom. -/
theorem TraceAnalyticMotiveRecognition.fubiniStableSourceMap_eq_sourceTraceFunctor_map
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.fubiniStableSourceMap source target =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceRewriteGenerator.fubini source target).traceHom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
      (TraceAnalyticRealizationGenerator.fubiniMap source target))
    (congrArg
      (fun traceHom =>
        TraceAnalyticMotiveComparison.sourceTraceFunctor.map traceHom)
      (TraceAnalyticMotiveRecognition.fubini_yonedaSourcePreimageTraceHom
        source
        target))

end AnalyticMotives
end LFunctions
end Boundary
