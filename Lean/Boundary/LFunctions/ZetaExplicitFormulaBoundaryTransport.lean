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

/-- The completed explicit-formula boundary sum in signed form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The completed boundary-defect Krein Gram in signed form. -/
noncomputable def zetaCompletedBoundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The zero-side Krein form is the completed explicit-formula boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_explicitFormulaBoundarySum
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedExplicitFormulaBoundarySum f := by
  exact zeta_completed_explicit_formula_autocorrelation f

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
  calc
    zetaCompletedZeroKreinGram f
        = zetaCompletedExplicitFormulaBoundarySum f :=
          zetaCompletedZeroKreinGram_eq_explicitFormulaBoundarySum f
    _   = zetaCompletedBoundaryDefectKreinGram f :=
          zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
