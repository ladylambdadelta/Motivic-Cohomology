universe u

namespace TraceCalc
namespace CategoryInfra

/-- Monoidal data carried by the active presentation itself. -/
class MonoidalPresentation (presentation : Type u) where
  tensorObj : presentation → presentation → presentation
  tensorAssoc :
    ∀ X Y Z : presentation,
      tensorObj (tensorObj X Y) Z = tensorObj X (tensorObj Y Z)

end CategoryInfra
end TraceCalc
