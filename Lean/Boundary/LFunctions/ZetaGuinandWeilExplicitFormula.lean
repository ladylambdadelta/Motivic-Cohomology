import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary Guinand-Weil explicit formula input

This file owns the single analytic input theorem needed to connect the
zero-side Krein form to the completed explicit-formula boundary sum.

The exact target, as recorded in the project analytic note, is the
autocorrelation identity for the completed zeta explicit formula:

```text
ξ(s) = (1/2) · s · (s - 1) · π^(-s/2) · Γ(s/2) · ζ(s)
g_f(t) = (f * f†)(t)
f†(t) = conjugate (f(-t))
Φ_f(z) = ∫_{ℝ} g_f(t) e^{z t} dt
```

with proof chain:

```text
completed log derivative -> residue theorem -> horizontal decay ->
vertical decomposition -> completed explicit formula
```

The theorem is intentionally isolated behind a typeclass so downstream files
can consume the analytic bridge without introducing more packaging.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed explicit-formula boundary sum in signed form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The imported Guinand-Weil explicit-formula input for completed zeta. -/
class ZetaGuinandWeilExplicitFormulaInput : Prop where
  completed_explicit_formula_autocorrelation :
    ∀ f : ZetaAdmissibleFunction,
      zetaCompletedZeroKreinGram f =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f

/-- The completed explicit formula for autocorrelation probes. -/
theorem zeta_completed_explicit_formula_autocorrelation
    [ZetaGuinandWeilExplicitFormulaInput]
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact ZetaGuinandWeilExplicitFormulaInput.completed_explicit_formula_autocorrelation f

end
end LFunctions
end Boundary
