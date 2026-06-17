import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionCore.TraceExpansionCore
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionCoefficient.TraceExpansionCoefficient
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionEuler.TraceExpansionEuler
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionMatrix.TraceExpansionMatrix
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionGeometric.TraceExpansionGeometric
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionTransport.TraceExpansionTransport

/-!
# Formal logarithmic trace expansions: public surface

This file is the public import surface for the formal trace-expansion lane.
It deliberately contains no proof bodies. The proof ownership is distributed as
follows:

* `TraceExpansionCore` owns the formal logarithm, finite geometric inverse, and
  core coefficient computations;
* `TraceExpansionCoefficient` owns coefficient-facing wrappers;
* `TraceExpansionEuler` owns scalar Euler-factor trace expansions;
* `TraceExpansionMatrix` owns the complete matrix trace-expansion API;
* `TraceExpansionGeometric` owns finite geometric inverse identities;
* `TraceExpansionTransport` owns coefficient transport through the inverse.

Downstream files should import this file for the assembled trace-expansion API.
New proofs should be added to the owner file listed above, then re-exported here
through this import surface.
-/
