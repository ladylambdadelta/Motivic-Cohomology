import TraceCalc.MotivicRecognition.PeriodFaithfulnessProviderProofs

/-!
# Package 8A axiom receipt

Axiom receipts for the three sealed theorems and the provider constructor
from the injective-extension period faithfulness sub-packet.

**Accepted baseline**: [propext, Quot.sound]
  (Classical.choice is absent here; none of the proofs use choice.)

**Not sealed in this file**:
- Full Package 8: `RealizationComparisonTarget` fields
  (`bettiAgreementTarget`, `deRhamAgreementTarget`, `periodMatrixAgreementTarget`).
- `proofRelevantPeriodStatementTarget`: blocked on P6.
-/

open TraceCalc.MotivicRecognition

#print axioms scalar_period_faithfulness_via_injective_extensions_bridge
#print axioms internal_period_faithfulness_of_injective_extensions_bridge
#print axioms legacyComparisonFaithfulnessInput_from_injective_extensions
#print axioms PeriodFaithfulnessProvider.ofInjectiveExtensions
