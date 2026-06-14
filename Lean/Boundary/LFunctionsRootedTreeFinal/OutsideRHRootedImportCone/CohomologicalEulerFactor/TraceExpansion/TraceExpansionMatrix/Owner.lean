import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionMatrix.TraceExpansionMatrixFormalLog.Owner

/-!
# Formal logarithmic trace expansions: matrix public surface

This file is the public import surface for the matrix trace-expansion lane.
It intentionally contains no proof bodies. The owner files below expose the
named coefficient, entry, determinant, and formal-log bridges consumed by the
non-matrix trace expansion surface.

Implementation ownership is split into:

* `TraceExpansionMatrixResolvent` for resolvent and coefficient calculus;
* `TraceExpansionMatrixDeterminant` for determinant/adjugate identities;
* `TraceExpansionMatrixFormalLog` for formal-log and Euler-polynomial consequences.

Downstream files should import this file when they need the complete matrix API,
and should import the owner files directly only when they are extending one of
those owner layers.
-/
