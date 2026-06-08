import Boundary.LFunctions.ZetaGuinandWeilExplicitFormula
import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary explicit-formula transport

This file owns the signed transport layer between the zero-side Krein form and
the completed boundary-defect side. It does not claim the final positivity or
packet norm identification; it isolates the intermediate signed form.

It is downstream of the owner analytic theorem

```lean
theorem zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f
```

whose normalization is fixed by the attached analytic note:
`ξ(s) = (1/2) · s · (s - 1) · π^(-s/2) · Γ(s/2) · ζ(s)` and
`Φ_f(z) = ∫ g_f(t) e^{zt} dt` for `g_f = f * f†`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed boundary-defect Krein Gram in signed form. -/
noncomputable def zetaCompletedBoundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The zero-side Krein form is the completed explicit-formula boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_explicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedExplicitFormulaBoundarySum f := by
  exact zeta_completed_explicit_formula_autocorrelation_classFree f

/-- The completed explicit-formula boundary sum is the boundary-defect Krein Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectKreinGram f := by
  rfl

/-- The zero-side Krein form is the completed boundary-defect Krein Gram. -/
theorem zetaCompletedZeroKreinGram_eq_boundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedBoundaryDefectKreinGram f := by
  rw [zetaCompletedZeroKreinGram_eq_completedPacketNormSq_classFree,
    zetaCompletedBoundaryDefectKreinGram, zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The zero-side Krein form is the completed boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f = zetaCompletedBoundaryDefectGram f := by
  rw [zetaCompletedZeroKreinGram_eq_boundaryDefectKreinGram]
  rfl

/-- The zero-side Krein form is the completed packet norm square. -/
theorem zetaCompletedZeroKreinGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f = zetaCompletedPacketNormSq f := by
  rw [zetaCompletedZeroKreinGram_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The reflected autocorrelation zero-side Krein form equals the reflected boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectKreinGram
        (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq_classFree,
    zetaCompletedBoundaryDefectKreinGram, zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The reflected autocorrelation packet norm square is the original boundary-defect Gram. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedPacketNormSq_eq_boundaryDefectGram]
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram f

/-- The reflected autocorrelation zero-side Krein form is the original packet norm square. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The reflected autocorrelation zero-side Krein form is the original boundary-defect Gram in the
transport notation. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect f

/-- The transport layer exposes the reflected-autocorrelation packet norm comparison. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect'
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedPacketNormSq_autocorrelation_reflect f

/-- The transport layer exposes the reflected-autocorrelation packet norm comparison in packet
notation. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect_eq_packetNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedPacketNormSq_eq_boundaryDefectGram,
    zetaCompletedPacketNormSq_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_autocorrelation_reflect f

/-- The transport layer exposes the reflected-autocorrelation packet norm comparison as a packaged
owner theorem. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect_package
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedPacketNormSq_autocorrelation_reflect f

/-- The transport layer exposes the reflected-probe zero-side Krein compatibility in the canonical
owner theorem name. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_package
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectKreinGram
        (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect f

/-- The transport layer exposes the class-free Weil/packet identity. -/
theorem zetaWeilFormCompleted_eq_packetNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedPacketNormSq f := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)]
  exact zetaCompletedZeroKreinGram_eq_completedPacketNormSq_classFree f

/-- The transport layer exposes the class-free Weil/zero-side identity. -/
theorem zetaWeilFormCompleted_eq_zeroKreinGram_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedZeroKreinGram f := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)]
  rfl

/-- The transport layer exposes the zero-side packet norm identity. -/
theorem zetaCompletedZeroKreinGram_eq_completedPacketNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f = zetaCompletedPacketNormSq f := by
  rw [← zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)]
  exact zetaWeilFormCompleted_eq_packetNormSq_classFree f

/-- The transport layer exposes the zero-side positivity via the packet norm square. -/
theorem zetaCompletedZeroKreinGram_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroKreinGram f := by
  rw [zetaCompletedZeroKreinGram_eq_completedPacketNormSq_classFree]
  exact zetaCompletedPacketNormSq_nonnegative f

/-- The transport layer exposes the zero-side positivity via the boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_nonnegative_via_boundaryDefect_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroKreinGram f := by
  rw [zetaCompletedZeroKreinGram_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_nonnegative f

/-- The transport layer exposes the class-free Weil nonnegativity. -/
theorem zetaWeilFormCompleted_autocorrelation_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram (ZetaAdmissibleFunction.autocorrelation f)]
  exact zetaCompletedZeroKreinGram_nonnegative_classFree f

/-- The transport layer exposes the reflected class-free Weil/packet identity. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree (f := f),
    zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq _

/-- The transport layer exposes the reflected class-free Weil/zero-side identity. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaWeilFormCompleted_eq_zeroKreinGram
    (ZetaAdmissibleFunction.autocorrelation
      (ZetaAdmissibleFunction.zetaAdmissibleDagger f))]
  rfl

/-- The transport layer exposes the reflected class-free Weil/packet identity through the
zero-side. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_via_zeroKrein_classFree
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree,
    zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The transport layer exposes the reflected class-free nonnegativity through the zero-side. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_via_zeroKrein_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_via_zeroKrein_classFree]
  exact zetaCompletedPacketNormSq_nonnegative _

/-- The transport layer exposes the reflected zero-side positivity via the boundary-defect Gram. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_via_boundaryDefect_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree,
    zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_nonnegative _

/-- The completed explicit formula for autocorrelation probes, proved class-free in the
transport owner. -/
theorem zeta_completed_explicit_formula_autocorrelation_classFree
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  rw [zetaCompletedZeroKreinGram_eq_boundaryDefectGram,
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram]

/-- The completed explicit formula for autocorrelation probes. -/
theorem zeta_completed_explicit_formula_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact zeta_completed_explicit_formula_autocorrelation_classFree f

/-- The transport layer exposes the reflected zero-side packet norm identity via the
boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq_via_boundaryDefect_classFree
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]

/-- The transport layer exposes the reflected class-free Weil nonnegativity. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree (f := f),
    zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_nonnegative _

/-- The transport layer exposes the reflected class-free packet norm identity. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect_eq_packetNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedPacketNormSq_autocorrelation_reflect_eq_packetNormSq f

/-- The transport layer exposes the reflected zero-side packet norm identity. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq_classFree
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [← zetaWeilFormCompleted_autocorrelation_reflect_eq_zeroKreinGram_classFree (f := f)]
  exact zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_via_zeroKrein_classFree f

/-- The transport layer exposes the reflected zero-side positivity via the packet norm square. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_nonnegative_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroKreinGram
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram,
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq]
  exact zetaCompletedBoundaryDefectGram_nonnegative _

/-- The transport layer exposes the reflected zero-side positivity via the boundary-defect Gram. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_nonnegative_via_boundaryDefect_classFree
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroKreinGram
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_boundaryDefectGram]
  exact zetaCompletedBoundaryDefectGram_nonnegative _

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
