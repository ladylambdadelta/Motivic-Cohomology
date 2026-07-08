import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.SeedMap.Owner

/-!
# Zero-pole finite-square trace value

This file owns the first concrete analytic trace-value bridge for the
completed-zeta finite-rectangle adapter.

The definitions below expose the two concrete analytic sides of the imported
finite-square residue theorem:

* the finite square boundary integral around the zero correction pole;
* the corresponding `2*pi*i` normalized local residue trace value.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic boundary trace value for the zero-pole finite square. -/
noncomputable def completedZetaZeroPoleFiniteSquareBoundaryTrace
    (f : ZetaAdmissibleFunction) (R : ℝ) : ℂ :=
  finiteRectangleSquareBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
    (0 : ℂ)
    R

/-- The analytic residue trace value for the zero-pole finite square. -/
noncomputable def completedZetaZeroPoleFiniteSquareResidueTrace
    (f : ZetaAdmissibleFunction) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))

/--
The imported zero-pole finite-square residue theorem, expressed as equality of
the two concrete analytic trace values selected above.
-/
theorem completedZetaZeroPoleFiniteSquareBoundaryTrace_eq_residueTrace
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_finiteSquareBoundaryIntegral_eq_residue
    f hPhi hR

/-- The zero-pole finite-square boundary value is a boundary analytic trace value. -/
theorem completedZetaZeroPoleFiniteSquareBoundaryTrace_eq_analyticBoundary
    (f : ZetaAdmissibleFunction) (R : ℝ) :
    AnalyticTraceValue.boundary
        (completedZetaZeroPoleFiniteSquareBoundaryTrace f R) =
      completedZetaZeroPoleFiniteSquareBoundaryTrace f R :=
  AnalyticTraceValue.boundary_eq
    (completedZetaZeroPoleFiniteSquareBoundaryTrace f R)

/-- The zero-pole finite-square residue value is a residue analytic trace value. -/
theorem completedZetaZeroPoleFiniteSquareResidueTrace_eq_analyticResidue
    (f : ZetaAdmissibleFunction) :
    AnalyticTraceValue.residue
        (completedZetaZeroPoleFiniteSquareResidueTrace f) =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  AnalyticTraceValue.residue_eq
    (completedZetaZeroPoleFiniteSquareResidueTrace f)

end AnalyticMotives
end LFunctions
end Boundary
