import TraceCalc.LayerE.MotivicRecognition.RealizationAgreementStatements

namespace AxiomCheckPackage8B
open TraceCalc.MotivicRecognition
open TraceCalc.ClassicalPeriods

-- Package 8B status: SEALED ON ACTIVE ROUTE.
-- The exact agreement formulas, tomography-level provider theorems, internal
-- realization-functor projections, and certified realization-comparison
-- instantiation all exist on the active route.

-- Helper shim defined in GeometricRealizations.lean (universe-safe morphism-existence extractor)
#print axioms GeometricFramedPeriodFunctoriality.morphismExists
#print axioms GeometricFramedPeriodFunctoriality.fullPeriodMatrixAgreement_holds

-- Four tomography-level provider theorems proved in RealizationAgreementStatements.lean
#print axioms ComparisonIsomorphismAgreementStatement.from_tomography
#print axioms BettiAgreementStatement.from_tomography
#print axioms DeRhamAgreementStatement.from_tomography
#print axioms PeriodMatrixAgreementStatement.from_tomography

-- Sealed owner-route projections from the internal realization functor
#print axioms comparisonIso_agreement_from_internal_realization_functor
#print axioms bettiAgreement_from_internal_realization_functor
#print axioms deRhamAgreement_from_internal_realization_functor
#print axioms periodMatrix_agreement_from_internal_realization_functor

-- Certified instantiation of the exact four agreement targets
#print axioms CertifiedRealizationComparisonTarget.ofTomography
#print axioms CertifiedRealizationComparisonTarget.ofInternalRealizationFunctor

end AxiomCheckPackage8B
