import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Facts.Owner

/-!
# Motive-root by-kind rewrite map facts

This file exposes the generic-equality, preimage, and inclusion facts for
by-kind rewrite maps at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive-root Stokes trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.stokesTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.stokesTraceHom source target =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRewriteGenerator.stokesTraceHom_eq
    source
    target

/-- The motive-root residue trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.residueTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.residueTraceHom source target =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRewriteGenerator.residueTraceHom_eq
    source
    target

/-- The motive-root channel trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.channelTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.channelTraceHom source target =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRewriteGenerator.channelTraceHom_eq
    source
    target

/-- The motive-root refinement trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.refinementTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.refinementTraceHom source target =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRewriteGenerator.refinementTraceHom_eq
    source
    target

/-- The motive-root schedule trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.scheduleTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.scheduleTraceHom source target =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRewriteGenerator.scheduleTraceHom_eq
    source
    target

/-- The motive-root weight-drop trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.weightDropTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.weightDropTraceHom source target =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceRewriteGenerator.weightDropTraceHom_eq
    source
    target

/-- The motive-root Fubini trace morphism is the generic trace morphism. -/
theorem TraceAnalyticMotive.fubiniTraceHom_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.fubiniTraceHom source target =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRewriteGenerator.fubiniTraceHom_eq
    source
    target

/-- The motive-root Stokes map is the generic map of the Stokes generator. -/
theorem TraceAnalyticMotive.stokesRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.stokesRepresentableMap source target =
      (TraceRewriteGenerator.stokes source target).representableMap :=
  TraceRewriteGenerator.stokesRepresentableMap_eq
    source
    target

/-- The motive-root residue map is the generic map of the residue generator. -/
theorem TraceAnalyticMotive.residueRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.residueRepresentableMap source target =
      (TraceRewriteGenerator.residue source target).representableMap :=
  TraceRewriteGenerator.residueRepresentableMap_eq
    source
    target

/-- The motive-root channel map is the generic map of the channel generator. -/
theorem TraceAnalyticMotive.channelRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.channelRepresentableMap source target =
      (TraceRewriteGenerator.channel source target).representableMap :=
  TraceRewriteGenerator.channelRepresentableMap_eq
    source
    target

/-- The motive-root refinement map is the generic map of the refinement generator. -/
theorem TraceAnalyticMotive.refinementRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.refinementRepresentableMap source target =
      (TraceRewriteGenerator.refinement source target).representableMap :=
  TraceRewriteGenerator.refinementRepresentableMap_eq
    source
    target

/-- The motive-root schedule map is the generic map of the schedule generator. -/
theorem TraceAnalyticMotive.scheduleRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.scheduleRepresentableMap source target =
      (TraceRewriteGenerator.schedule source target).representableMap :=
  TraceRewriteGenerator.scheduleRepresentableMap_eq
    source
    target

/-- The motive-root weight-drop map is the generic map of the weight-drop generator. -/
theorem TraceAnalyticMotive.weightDropRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.weightDropRepresentableMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableMap :=
  TraceRewriteGenerator.weightDropRepresentableMap_eq
    source
    target

/-- The motive-root Fubini map is the generic map of the Fubini generator. -/
theorem TraceAnalyticMotive.fubiniRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.fubiniRepresentableMap source target =
      (TraceRewriteGenerator.fubini source target).representableMap :=
  TraceRewriteGenerator.fubiniRepresentableMap_eq
    source
    target

/-- The motive-root lifted Stokes map is the generic lifted map of the Stokes generator. -/
theorem TraceAnalyticMotive.stokesRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.stokesRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.stokes source target).representableSubcategoryMap :=
  TraceRewriteGenerator.stokesRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted residue map is the generic lifted map of the residue generator. -/
theorem TraceAnalyticMotive.residueRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.residueRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.residue source target).representableSubcategoryMap :=
  TraceRewriteGenerator.residueRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted channel map is the generic lifted map of the channel generator. -/
theorem TraceAnalyticMotive.channelRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.channelRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.channel source target).representableSubcategoryMap :=
  TraceRewriteGenerator.channelRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted refinement map is the generic lifted map of the refinement generator. -/
theorem TraceAnalyticMotive.refinementRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.refinementRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.refinement source target).representableSubcategoryMap :=
  TraceRewriteGenerator.refinementRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted schedule map is the generic lifted map of the schedule generator. -/
theorem TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.scheduleRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.schedule source target).representableSubcategoryMap :=
  TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted weight-drop map is the generic lifted map of the weight-drop generator. -/
theorem TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.weightDropRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableSubcategoryMap :=
  TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_eq
    source
    target

/-- The motive-root lifted Fubini map is the generic lifted map of the Fubini generator. -/
theorem TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticMotive.fubiniRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.fubini source target).representableSubcategoryMap :=
  TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_eq
    source
    target

/-- The preimage of the motive-root Stokes representable map is the Stokes trace morphism. -/
theorem TraceAnalyticMotive.stokesRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.stokesRepresentableMap source target) =
      TraceAnalyticMotive.stokesTraceHom source target :=
  TraceRewriteGenerator.stokesRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root residue representable map is the residue trace morphism. -/
theorem TraceAnalyticMotive.residueRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.residueRepresentableMap source target) =
      TraceAnalyticMotive.residueTraceHom source target :=
  TraceRewriteGenerator.residueRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root channel representable map is the channel trace morphism. -/
theorem TraceAnalyticMotive.channelRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.channelRepresentableMap source target) =
      TraceAnalyticMotive.channelTraceHom source target :=
  TraceRewriteGenerator.channelRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root refinement representable map is the refinement trace morphism. -/
theorem TraceAnalyticMotive.refinementRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.refinementRepresentableMap source target) =
      TraceAnalyticMotive.refinementTraceHom source target :=
  TraceRewriteGenerator.refinementRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root schedule representable map is the schedule trace morphism. -/
theorem TraceAnalyticMotive.scheduleRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.scheduleRepresentableMap source target) =
      TraceAnalyticMotive.scheduleTraceHom source target :=
  TraceRewriteGenerator.scheduleRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root weight-drop representable map is the weight-drop trace morphism. -/
theorem TraceAnalyticMotive.weightDropRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.weightDropRepresentableMap source target) =
      TraceAnalyticMotive.weightDropTraceHom source target :=
  TraceRewriteGenerator.weightDropRepresentableMap_preimage
    source
    target

/-- The preimage of the motive-root Fubini representable map is the Fubini trace morphism. -/
theorem TraceAnalyticMotive.fubiniRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.fubiniRepresentableMap source target) =
      TraceAnalyticMotive.fubiniTraceHom source target :=
  TraceRewriteGenerator.fubiniRepresentableMap_preimage
    source
    target

/-- Forgetting the motive-root lifted Stokes map gives the Stokes representable map. -/
theorem TraceAnalyticMotive.stokesRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.stokesRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.stokesRepresentableMap source target :=
  TraceRewriteGenerator.stokesRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted residue map gives the residue representable map. -/
theorem TraceAnalyticMotive.residueRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.residueRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.residueRepresentableMap source target :=
  TraceRewriteGenerator.residueRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted channel map gives the channel representable map. -/
theorem TraceAnalyticMotive.channelRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.channelRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.channelRepresentableMap source target :=
  TraceRewriteGenerator.channelRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted refinement map gives the refinement representable map. -/
theorem TraceAnalyticMotive.refinementRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.refinementRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.refinementRepresentableMap source target :=
  TraceRewriteGenerator.refinementRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted schedule map gives the schedule representable map. -/
theorem TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.scheduleRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.scheduleRepresentableMap source target :=
  TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted weight-drop map gives the weight-drop representable map. -/
theorem TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.weightDropRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.weightDropRepresentableMap source target :=
  TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_inclusion
    source
    target

/-- Forgetting the motive-root lifted Fubini map gives the Fubini representable map. -/
theorem TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticMotive.fubiniRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.fubiniRepresentableMap source target :=
  TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_inclusion
    source
    target

/-- The motive-root lifted Stokes map has Stokes trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.stokesRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.stokesRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.stokesTraceHom source target :=
  TraceRewriteGenerator.stokesRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted residue map has residue trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.residueRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.residueRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.residueTraceHom source target :=
  TraceRewriteGenerator.residueRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted channel map has channel trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.channelRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.channelRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.channelTraceHom source target :=
  TraceRewriteGenerator.channelRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted refinement map has refinement trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.refinementRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.refinementRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.refinementTraceHom source target :=
  TraceRewriteGenerator.refinementRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted schedule map has schedule trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.scheduleRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.scheduleRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.scheduleTraceHom source target :=
  TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted weight-drop map has weight-drop trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.weightDropRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.weightDropRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.weightDropTraceHom source target :=
  TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_preimage
    source
    target

/-- The motive-root lifted Fubini map has Fubini trace morphism as Yoneda preimage. -/
theorem TraceAnalyticMotive.fubiniRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceAnalyticMotive.fubiniRepresentableSubcategoryMap source target) =
      TraceAnalyticMotive.fubiniTraceHom source target :=
  TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
