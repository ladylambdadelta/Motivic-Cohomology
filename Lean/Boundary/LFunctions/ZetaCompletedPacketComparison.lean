import Boundary.LFunctions.ZetaGuinandWeilExplicitFormula
import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary completed packet comparison

This file composes the owned arrows:

`Weil form → zero Krein → explicit boundary sum → boundary-defect Gram → packet norm square`

The only analytic dependency is the imported Guinand–Weil explicit-formula
input typeclass.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The zero-side Krein gram equals the boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_eq_boundaryDefectGram
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedBoundaryDefectGram f := by
  calc
    zetaCompletedZeroKreinGram f
        = ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f :=
          zeta_completed_explicit_formula_autocorrelation f
    _   = zetaCompletedBoundaryDefectGram f := by
          simpa using
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
              (f := f))

/-- The completed Weil form on an autocorrelation equals the packet norm square. -/
theorem zetaWeilFormCompleted_eq_packetNormSq
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedPacketNormSq f := by
  calc
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f)
        = zetaCompletedZeroKreinGram f :=
          zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)
    _   = zetaCompletedBoundaryDefectGram f :=
          zetaCompletedZeroKreinGram_eq_boundaryDefectGram
            (f := f)
    _   = zetaCompletedPacketNormSq f :=
          zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The completed Weil form on an autocorrelation equals the packet norm square without
the explicit-formula input class. -/
theorem zetaWeilFormCompleted_eq_packetNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedPacketNormSq f := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)]
  exact zetaCompletedZeroKreinGram_eq_completedPacketNormSq f

/-- The completed Weil form on an autocorrelation is nonnegative without the
explicit-formula input class. -/
theorem zetaWeilFormCompleted_autocorrelation_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_eq_packetNormSq_classFree]
  exact zetaCompletedPacketNormSq_nonnegative f

/-- The completed Weil form on an autocorrelation is nonnegative. -/
theorem zetaWeilFormCompleted_autocorrelation_nonnegative
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaWeilFormCompleted_autocorrelation_nonnegative_classFree f

/-- The completed zero-side Krein form of the reflected autocorrelation agrees with the
boundary-defect Gram of the original autocorrelation. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect
    (f := f)

/-- The boundary-defect Gram is invariant under reflection of the autocorrelation probe. -/
theorem zetaCompletedBoundaryDefectGram_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  rfl

/-- The reflected autocorrelation has the same completed packet norm square as the original. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedPacketNormSq_eq_boundaryDefectGram,
    zetaCompletedPacketNormSq_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_autocorrelation_reflect]

/-- The completed Weil form of the reflected autocorrelation is the original boundary-defect Gram. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram]
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect (f := f)

/-- The completed Weil form of the reflected autocorrelation is the original packet norm square. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The completed Weil form of the reflected autocorrelation is nonnegative. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq]
  exact zetaCompletedPacketNormSq_nonnegative _

/-- The completed Weil form of the reflected autocorrelation is the packet norm square, class-free. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq f

/-- The completed Weil form of the reflected autocorrelation is nonnegative, class-free. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  exact zetaWeilFormCompleted_autocorrelation_reflect_nonnegative f

/-- The reflected autocorrelation packet norm square compatibility exposed in the comparison file. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect'
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedPacketNormSq_autocorrelation_reflect f

/-- The completed Weil form of the reflected autocorrelation is the packet norm square of the
original autocorrelation. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_eq_packetNormSq (f :=
    ZetaAdmissibleFunction.autocorrelation (ZetaAdmissibleFunction.zetaAdmissibleDagger f))]
  exact zetaCompletedPacketNormSq_autocorrelation_reflect f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
