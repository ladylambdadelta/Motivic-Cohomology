-- This file has been split into organized sections for maintainability.
-- All theorems are re-exported here for backwards compatibility.

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Owner

/-!
# Endpoint cap-collar Cauchy balances for finite Abel-Plana

This file owns the left and right endpoint half-collar domains, oriented boundary
identifications, and normalized endpoint cap-collar balance theorems.

This file now re-exports the split components for backwards compatibility:
- Foundation.Owner: helper lemmas about complex numbers and real bounds
- Left.Owner: left endpoint cap collar domain and theorems
- Right.Owner: right endpoint cap collar domain and theorems
- Combined.Owner: balance and owner theorems using both endpoints

New code should import from the specific sections for clarity. Existing code
using this file will continue to work without modification.
-/
