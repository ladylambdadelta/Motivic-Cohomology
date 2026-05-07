import TraceCalc.MotivicRecognition.RealizationAgreementStatements

namespace AxiomCheckPackage8B
open TraceCalc.MotivicRecognition
open TraceCalc.ClassicalPeriods

-- Package 8B conditional provider theorems (conditioned on GeometricRealizationTomographySoundness)

-- Helper shim defined in GeometricRealizations.lean (universe-safe morphism-existence extractor)
#print axioms GeometricFramedPeriodFunctoriality.morphismExists
#print axioms GeometricFramedPeriodFunctoriality.fullPeriodMatrixAgreement_holds

-- Four conditional provider theorems proved in RealizationAgreementStatements.lean
#print axioms ComparisonIsomorphismAgreementStatement.from_tomography
#print axioms BettiAgreementStatement.from_tomography
#print axioms DeRhamAgreementStatement.from_tomography
#print axioms PeriodMatrixAgreementStatement.from_tomography

end AxiomCheckPackage8B
