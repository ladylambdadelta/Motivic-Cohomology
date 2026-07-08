import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Maps.Owner

/-!
# By-kind rewrite map facts

This file records the generic-equality, preimage, and inclusion facts for the
by-kind analytic rewrite maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The Stokes trace morphism is the generic trace morphism of the Stokes generator. -/
theorem TraceRewriteGenerator.stokesTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.stokesTraceHom source target =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  rfl

/-- The residue trace morphism is the generic trace morphism of the residue generator. -/
theorem TraceRewriteGenerator.residueTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.residueTraceHom source target =
      (TraceRewriteGenerator.residue source target).traceHom :=
  rfl

/-- The channel trace morphism is the generic trace morphism of the channel generator. -/
theorem TraceRewriteGenerator.channelTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.channelTraceHom source target =
      (TraceRewriteGenerator.channel source target).traceHom :=
  rfl

/-- The refinement trace morphism is the generic trace morphism of the refinement generator. -/
theorem TraceRewriteGenerator.refinementTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.refinementTraceHom source target =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  rfl

/-- The schedule trace morphism is the generic trace morphism of the schedule generator. -/
theorem TraceRewriteGenerator.scheduleTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.scheduleTraceHom source target =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  rfl

/-- The weight-drop trace morphism is the generic trace morphism of the weight-drop generator. -/
theorem TraceRewriteGenerator.weightDropTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.weightDropTraceHom source target =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  rfl

/-- The Fubini trace morphism is the generic trace morphism of the Fubini generator. -/
theorem TraceRewriteGenerator.fubiniTraceHom_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.fubiniTraceHom source target =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  rfl

/-- The preimage of the Stokes representable map is the Stokes trace morphism. -/
theorem TraceRewriteGenerator.stokesRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.stokesRepresentableMap source target) =
      TraceRewriteGenerator.stokesTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.stokes source target)

/-- The preimage of the residue representable map is the residue trace morphism. -/
theorem TraceRewriteGenerator.residueRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.residueRepresentableMap source target) =
      TraceRewriteGenerator.residueTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.residue source target)

/-- The preimage of the channel representable map is the channel trace morphism. -/
theorem TraceRewriteGenerator.channelRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.channelRepresentableMap source target) =
      TraceRewriteGenerator.channelTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.channel source target)

/-- The preimage of the refinement representable map is the refinement trace morphism. -/
theorem TraceRewriteGenerator.refinementRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.refinementRepresentableMap source target) =
      TraceRewriteGenerator.refinementTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.refinement source target)

/-- The preimage of the schedule representable map is the schedule trace morphism. -/
theorem TraceRewriteGenerator.scheduleRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.scheduleRepresentableMap source target) =
      TraceRewriteGenerator.scheduleTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.schedule source target)

/-- The preimage of the weight-drop representable map is the weight-drop trace morphism. -/
theorem TraceRewriteGenerator.weightDropRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.weightDropRepresentableMap source target) =
      TraceRewriteGenerator.weightDropTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.weightDrop source target)

/-- The preimage of the Fubini representable map is the Fubini trace morphism. -/
theorem TraceRewriteGenerator.fubiniRepresentableMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceRewriteGenerator.fubiniRepresentableMap source target) =
      TraceRewriteGenerator.fubiniTraceHom source target :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.fubini source target)

/-- Forgetting the lifted Stokes map gives the Stokes representable map. -/
theorem TraceRewriteGenerator.stokesRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.stokesRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.stokes source target)

/-- Forgetting the lifted residue map gives the residue representable map. -/
theorem TraceRewriteGenerator.residueRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.residueRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.residue source target)

/-- Forgetting the lifted channel map gives the channel representable map. -/
theorem TraceRewriteGenerator.channelRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.channelRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.channel source target)

/-- Forgetting the lifted refinement map gives the refinement representable map. -/
theorem TraceRewriteGenerator.refinementRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.refinementRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.refinement source target)

/-- Forgetting the lifted schedule map gives the schedule representable map. -/
theorem TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.scheduleRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.schedule source target)

/-- Forgetting the lifted weight-drop map gives the weight-drop representable map. -/
theorem TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.weightDropRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.weightDrop source target)

/-- Forgetting the lifted Fubini map gives the Fubini representable map. -/
theorem TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_inclusion
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceRewriteGenerator.fubiniRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceRewriteGenerator.representableSubcategoryMap_inclusion
    (TraceRewriteGenerator.fubini source target)

/-- The lifted Stokes map has Stokes trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.stokesRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.stokesRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.stokesTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.stokes source target)

/-- The lifted residue map has residue trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.residueRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.residueRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.residueTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.residue source target)

/-- The lifted channel map has channel trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.channelRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.channelRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.channelTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.channel source target)

/-- The lifted refinement map has refinement trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.refinementRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.refinementRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.refinementTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.refinement source target)

/-- The lifted schedule map has schedule trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.scheduleRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.scheduleTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.schedule source target)

/-- The lifted weight-drop map has weight-drop trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.weightDropRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.weightDropTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.weightDrop source target)

/-- The lifted Fubini map has Fubini trace morphism as Yoneda preimage. -/
theorem TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_preimage
    (source target : QTraceExpression) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
        (TraceRewriteGenerator.fubiniRepresentableSubcategoryMap source target) =
      TraceRewriteGenerator.fubiniTraceHom source target :=
  TraceRewriteGenerator.representableSubcategoryMap_preimage
    (TraceRewriteGenerator.fubini source target)

/-- The Stokes map is the generic representable map of the Stokes generator. -/
theorem TraceRewriteGenerator.stokesRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.stokesRepresentableMap source target =
      (TraceRewriteGenerator.stokes source target).representableMap :=
  rfl

/-- The residue map is the generic representable map of the residue generator. -/
theorem TraceRewriteGenerator.residueRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.residueRepresentableMap source target =
      (TraceRewriteGenerator.residue source target).representableMap :=
  rfl

/-- The channel map is the generic representable map of the channel generator. -/
theorem TraceRewriteGenerator.channelRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.channelRepresentableMap source target =
      (TraceRewriteGenerator.channel source target).representableMap :=
  rfl

/-- The refinement map is the generic representable map of the refinement generator. -/
theorem TraceRewriteGenerator.refinementRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.refinementRepresentableMap source target =
      (TraceRewriteGenerator.refinement source target).representableMap :=
  rfl

/-- The schedule map is the generic representable map of the schedule generator. -/
theorem TraceRewriteGenerator.scheduleRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.scheduleRepresentableMap source target =
      (TraceRewriteGenerator.schedule source target).representableMap :=
  rfl

/-- The weight-drop map is the generic representable map of the weight-drop generator. -/
theorem TraceRewriteGenerator.weightDropRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.weightDropRepresentableMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableMap :=
  rfl

/-- The Fubini map is the generic representable map of the Fubini generator. -/
theorem TraceRewriteGenerator.fubiniRepresentableMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.fubiniRepresentableMap source target =
      (TraceRewriteGenerator.fubini source target).representableMap :=
  rfl

/-- The lifted Stokes map is the generic lifted map of the Stokes generator. -/
theorem TraceRewriteGenerator.stokesRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.stokesRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.stokes source target).representableSubcategoryMap :=
  rfl

/-- The lifted residue map is the generic lifted map of the residue generator. -/
theorem TraceRewriteGenerator.residueRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.residueRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.residue source target).representableSubcategoryMap :=
  rfl

/-- The lifted channel map is the generic lifted map of the channel generator. -/
theorem TraceRewriteGenerator.channelRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.channelRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.channel source target).representableSubcategoryMap :=
  rfl

/-- The lifted refinement map is the generic lifted map of the refinement generator. -/
theorem TraceRewriteGenerator.refinementRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.refinementRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.refinement source target).representableSubcategoryMap :=
  rfl

/-- The lifted schedule map is the generic lifted map of the schedule generator. -/
theorem TraceRewriteGenerator.scheduleRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.scheduleRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.schedule source target).representableSubcategoryMap :=
  rfl

/-- The lifted weight-drop map is the generic lifted map of the weight-drop generator. -/
theorem TraceRewriteGenerator.weightDropRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.weightDropRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.weightDrop source target).representableSubcategoryMap :=
  rfl

/-- The lifted Fubini map is the generic lifted map of the Fubini generator. -/
theorem TraceRewriteGenerator.fubiniRepresentableSubcategoryMap_eq
    (source target : QTraceExpression) :
    TraceRewriteGenerator.fubiniRepresentableSubcategoryMap source target =
      (TraceRewriteGenerator.fubini source target).representableSubcategoryMap :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
