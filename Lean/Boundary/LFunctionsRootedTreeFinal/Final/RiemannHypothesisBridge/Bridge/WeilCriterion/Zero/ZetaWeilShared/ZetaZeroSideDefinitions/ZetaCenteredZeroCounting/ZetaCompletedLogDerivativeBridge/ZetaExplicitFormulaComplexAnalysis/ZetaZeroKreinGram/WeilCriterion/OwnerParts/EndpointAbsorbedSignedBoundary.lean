import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedSignedBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceKernelSplit

/-!
# Endpoint-absorbed signed completed boundary

This file owns the signed-boundary normal form after the two endpoint
diagonal fibers have been removed.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The normalized signed reserve before subtracting the negative
archimedean variation. -/
noncomputable def zetaCompletedNormalizedSignedReserveScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalPrimeBoundaryScalar f +
    zetaCompletedPhysicalCorrectionBoundaryScalar f +
    zetaCompletedArchimedeanPositiveVariationScalar f

/-- The normalized endpoint debt from the two completed-zeta endpoint fibers. -/
noncomputable def zetaCompletedEndpointDiagonalDebtScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  (zetaCompletedEndpointCorrectionPacket f).diagonalDebt

/-- The normalized negative archimedean variation scalar. -/
noncomputable def zetaCompletedNegativeArchimedeanDebtScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedArchimedeanNegativeVariationScalar f

/-- The finite-shadow trace-reserve domination needed after removing the
completed-zeta endpoint fibers. -/
def ZetaCompletedEndpointTraceReserveDomination
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedEndpointDiagonalDebtScalar f +
      zetaCompletedNegativeArchimedeanDebtScalar f ≤
    zetaCompletedNormalizedSignedReserveScalar f

/-- The trace-compression form of endpoint reserve domination.  The endpoint
debt is expressed as the Gram of the two endpoint fibers. -/
def ZetaCompletedEndpointTraceReserveCompression
    (f : ZetaAdmissibleFunction) : Prop :=
  (completedWeilEndpointTraceFiber f).gram +
      zetaCompletedNegativeArchimedeanDebtScalar f ≤
    zetaCompletedNormalizedSignedReserveScalar f

/-- The named endpoint diagonal debt is the endpoint trace-fiber Gram. -/
theorem zetaCompletedEndpointDiagonalDebtScalar_eq_endpointTraceFiber_gram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedEndpointDiagonalDebtScalar f =
      (completedWeilEndpointTraceFiber f).gram :=
  (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f).symm

/-- Trace-reserve domination transports across endpoint-debt normalization. -/
theorem zetaCompletedEndpointTraceReserveCompression_of_traceReserveDomination
    (f : ZetaAdmissibleFunction)
    (reserveDomination :
      ZetaCompletedEndpointTraceReserveDomination f) :
    ZetaCompletedEndpointTraceReserveCompression f :=
  Eq.subst
    (motive := fun value : ℝ =>
      value + zetaCompletedNegativeArchimedeanDebtScalar f ≤
        zetaCompletedNormalizedSignedReserveScalar f)
    (zetaCompletedEndpointDiagonalDebtScalar_eq_endpointTraceFiber_gram f)
    reserveDomination

/-- Trace-compression domination transports back to the named endpoint debt. -/
theorem zetaCompletedEndpointTraceReserveDomination_of_traceCompression
    (f : ZetaAdmissibleFunction)
    (compression :
      ZetaCompletedEndpointTraceReserveCompression f) :
    ZetaCompletedEndpointTraceReserveDomination f :=
  Eq.subst
    (motive := fun value : ℝ =>
      value + zetaCompletedNegativeArchimedeanDebtScalar f ≤
        zetaCompletedNormalizedSignedReserveScalar f)
    (zetaCompletedEndpointDiagonalDebtScalar_eq_endpointTraceFiber_gram f).symm
    compression

/-- Endpoint reserve domination is equivalent to the concrete endpoint-fiber
trace-compression inequality. -/
theorem zetaCompletedEndpointTraceReserveDomination_iff_traceCompression
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedEndpointTraceReserveDomination f ↔
      ZetaCompletedEndpointTraceReserveCompression f :=
  Iff.intro
    (zetaCompletedEndpointTraceReserveCompression_of_traceReserveDomination f)
    (zetaCompletedEndpointTraceReserveDomination_of_traceCompression f)

/-- The completed boundary real part is the normalized signed boundary scalar. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_signedBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      zetaCompletedNormalizedSignedBoundaryScalar f :=
  completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedSignedScalar
    f

/-- Endpoint absorption in boundary-channel coordinates. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_sub_endpointDebt
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointAbsorbedPhysicalScalar f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
        zetaCompletedEndpointDiagonalDebtScalar f :=
  completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
    f

/-- Replace the boundary channel by the normalized signed scalar after endpoint
debt subtraction. -/
theorem completedBoundaryChannel_sub_endpointDebt_eq_signedBoundary_sub_endpointDebt
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
        zetaCompletedEndpointDiagonalDebtScalar f =
      zetaCompletedNormalizedSignedBoundaryScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f :=
  congrArg
    (fun value : ℝ =>
      value - zetaCompletedEndpointDiagonalDebtScalar f)
    (completedBoundaryChannel_convolutionAutocorrelation_re_eq_signedBoundaryScalar
      f)

/-- The endpoint-absorbed physical scalar is the signed boundary scalar minus
the endpoint diagonal debt. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_signedBoundary_sub_endpointDebt
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointAbsorbedPhysicalScalar f =
      zetaCompletedNormalizedSignedBoundaryScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f :=
  Eq.trans
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_sub_endpointDebt
      f)
    (completedBoundaryChannel_sub_endpointDebt_eq_signedBoundary_sub_endpointDebt
      f)

/-- The signed boundary scalar is reserve minus negative archimedean debt. -/
theorem zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negativeDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedNormalizedSignedBoundaryScalar f =
      zetaCompletedNormalizedSignedReserveScalar f -
        zetaCompletedNegativeArchimedeanDebtScalar f :=
  zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negative f

/-- Endpoint and negative-debt subtraction commute in the absorbed scalar. -/
theorem reserve_sub_negativeDebt_sub_endpointDebt_eq_reserve_sub_endpointDebt_sub_negativeDebt
    (reserve endpointDebt negativeDebt : ℝ) :
    (reserve - negativeDebt) - endpointDebt =
      (reserve - endpointDebt) - negativeDebt :=
  calc
    (reserve - negativeDebt) - endpointDebt =
        (reserve + -negativeDebt) + -endpointDebt :=
      congrArg
        (fun value : ℝ => value + -endpointDebt)
        (sub_eq_add_neg reserve negativeDebt)
    _ = reserve + (-negativeDebt + -endpointDebt) :=
      add_assoc reserve (-negativeDebt) (-endpointDebt)
    _ = reserve + (-endpointDebt + -negativeDebt) :=
      congrArg
        (fun value : ℝ => reserve + value)
        (add_comm (-negativeDebt) (-endpointDebt))
    _ = (reserve + -endpointDebt) + -negativeDebt :=
      (add_assoc reserve (-endpointDebt) (-negativeDebt)).symm
    _ = (reserve - endpointDebt) - negativeDebt :=
      congrArg₂ HSub.hSub
        (sub_eq_add_neg reserve endpointDebt).symm
        (Eq.refl negativeDebt)

/-- Replace signed-boundary coordinates by reserve coordinates after endpoint
debt subtraction. -/
theorem signedBoundary_sub_endpointDebt_eq_reserve_sub_endpointDebt_sub_negativeDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedNormalizedSignedBoundaryScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f =
      (zetaCompletedNormalizedSignedReserveScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f) -
        zetaCompletedNegativeArchimedeanDebtScalar f :=
  Eq.trans
    (congrArg
      (fun value : ℝ =>
        value - zetaCompletedEndpointDiagonalDebtScalar f)
      (zetaCompletedNormalizedSignedBoundaryScalar_eq_reserve_sub_negativeDebt
        f))
    (reserve_sub_negativeDebt_sub_endpointDebt_eq_reserve_sub_endpointDebt_sub_negativeDebt
      (zetaCompletedNormalizedSignedReserveScalar f)
      (zetaCompletedEndpointDiagonalDebtScalar f)
      (zetaCompletedNegativeArchimedeanDebtScalar f))

/-- Endpoint absorption unfolds to reserve minus endpoint debt minus negative
archimedean debt. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_endpointDebt_sub_negativeDebt
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointAbsorbedPhysicalScalar f =
      (zetaCompletedNormalizedSignedReserveScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f) -
        zetaCompletedNegativeArchimedeanDebtScalar f :=
  Eq.trans
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_signedBoundary_sub_endpointDebt
      f)
    (signedBoundary_sub_endpointDebt_eq_reserve_sub_endpointDebt_sub_negativeDebt
      f)

/-- Nonnegativity of the reserve-minus-negative expression gives domination of
the negative debt by the endpoint-reduced reserve. -/
theorem negativeDebt_le_reserve_sub_endpointDebt_of_reserve_sub_endpointDebt_sub_negativeDebt_nonnegative
    (reserve endpointDebt negativeDebt : ℝ)
    (differenceNonnegative : 0 ≤ (reserve - endpointDebt) - negativeDebt) :
    negativeDebt ≤ reserve - endpointDebt :=
  sub_nonneg.mp differenceNonnegative

/-- Domination of the negative debt gives nonnegativity of the
reserve-minus-negative expression. -/
theorem reserve_sub_endpointDebt_sub_negativeDebt_nonnegative_of_negativeDebt_le
    (reserve endpointDebt negativeDebt : ℝ)
    (domination : negativeDebt ≤ reserve - endpointDebt) :
    0 ≤ (reserve - endpointDebt) - negativeDebt :=
  sub_nonneg.mpr domination

/-- Endpoint absorbed nonnegativity implies the endpoint-reduced reserve
dominates the negative debt. -/
theorem negativeDebt_le_reserve_sub_endpointDebt_of_endpointAbsorbedPhysicalScalar_nonnegative
    (f : ZetaAdmissibleFunction)
    (absorbedNonnegative :
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f) :
    zetaCompletedNegativeArchimedeanDebtScalar f ≤
      zetaCompletedNormalizedSignedReserveScalar f -
        zetaCompletedEndpointDiagonalDebtScalar f :=
  negativeDebt_le_reserve_sub_endpointDebt_of_reserve_sub_endpointDebt_sub_negativeDebt_nonnegative
    (zetaCompletedNormalizedSignedReserveScalar f)
    (zetaCompletedEndpointDiagonalDebtScalar f)
    (zetaCompletedNegativeArchimedeanDebtScalar f)
    (Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_endpointDebt_sub_negativeDebt
        f)
      absorbedNonnegative)

/-- Endpoint-reduced reserve domination implies endpoint absorbed
nonnegativity. -/
theorem endpointAbsorbedPhysicalScalar_nonnegative_of_negativeDebt_le_reserve_sub_endpointDebt
    (f : ZetaAdmissibleFunction)
    (domination :
      zetaCompletedNegativeArchimedeanDebtScalar f ≤
        zetaCompletedNormalizedSignedReserveScalar f -
          zetaCompletedEndpointDiagonalDebtScalar f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_endpointDebt_sub_negativeDebt
      f).symm
    (reserve_sub_endpointDebt_sub_negativeDebt_nonnegative_of_negativeDebt_le
      (zetaCompletedNormalizedSignedReserveScalar f)
      (zetaCompletedEndpointDiagonalDebtScalar f)
      (zetaCompletedNegativeArchimedeanDebtScalar f)
      domination)

/-- Endpoint absorption is exactly domination of the negative archimedean debt
by the reserve after removing endpoint diagonal debt. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_negativeDebt_le_reserve_sub_endpointDebt
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f ↔
      zetaCompletedNegativeArchimedeanDebtScalar f ≤
        zetaCompletedNormalizedSignedReserveScalar f -
          zetaCompletedEndpointDiagonalDebtScalar f :=
  Iff.intro
    (negativeDebt_le_reserve_sub_endpointDebt_of_endpointAbsorbedPhysicalScalar_nonnegative
      f)
    (endpointAbsorbedPhysicalScalar_nonnegative_of_negativeDebt_le_reserve_sub_endpointDebt
      f)

/-- Subtracting endpoint debt and then negative debt is the same as
subtracting their combined trace debt. -/
theorem reserve_sub_endpointDebt_sub_negativeDebt_eq_reserve_sub_combinedDebt
    (reserve endpointDebt negativeDebt : ℝ) :
    (reserve - endpointDebt) - negativeDebt =
      reserve - (endpointDebt + negativeDebt) :=
  calc
    (reserve - endpointDebt) - negativeDebt =
        (reserve + -endpointDebt) + -negativeDebt :=
      congrArg
        (fun value : ℝ => value + -negativeDebt)
        (sub_eq_add_neg reserve endpointDebt)
    _ = reserve + (-endpointDebt + -negativeDebt) :=
      add_assoc reserve (-endpointDebt) (-negativeDebt)
    _ = reserve + -(endpointDebt + negativeDebt) :=
      congrArg
        (fun value : ℝ => reserve + value)
        (neg_add endpointDebt negativeDebt).symm
    _ = reserve - (endpointDebt + negativeDebt) :=
      (sub_eq_add_neg reserve (endpointDebt + negativeDebt)).symm

/-- Endpoint absorption is equivalently nonnegativity after removing the
combined endpoint and negative-variation trace debt. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_combinedDebt
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointAbsorbedPhysicalScalar f =
      zetaCompletedNormalizedSignedReserveScalar f -
        (zetaCompletedEndpointDiagonalDebtScalar f +
          zetaCompletedNegativeArchimedeanDebtScalar f) :=
  Eq.trans
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_endpointDebt_sub_negativeDebt
      f)
    (reserve_sub_endpointDebt_sub_negativeDebt_eq_reserve_sub_combinedDebt
      (zetaCompletedNormalizedSignedReserveScalar f)
      (zetaCompletedEndpointDiagonalDebtScalar f)
      (zetaCompletedNegativeArchimedeanDebtScalar f))

/-- Endpoint absorbed nonnegativity implies domination of the combined trace
debt. -/
theorem combinedDebt_le_reserve_of_endpointAbsorbedPhysicalScalar_nonnegative
    (f : ZetaAdmissibleFunction)
    (absorbedNonnegative :
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f) :
    ZetaCompletedEndpointTraceReserveDomination f :=
  sub_nonneg.mp
    (Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_combinedDebt
        f)
      absorbedNonnegative)

/-- Domination of the combined trace debt implies endpoint absorbed
nonnegativity. -/
theorem endpointAbsorbedPhysicalScalar_nonnegative_of_combinedDebt_le_reserve
    (f : ZetaAdmissibleFunction)
    (reserveDomination :
      ZetaCompletedEndpointTraceReserveDomination f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_reserve_sub_combinedDebt
      f).symm
    (sub_nonneg.mpr reserveDomination)

/-- Endpoint absorption is exactly domination of endpoint diagonal debt plus
negative archimedean variation by the positive trace reserve. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_combinedDebt_le_reserve
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f ↔
      ZetaCompletedEndpointTraceReserveDomination f :=
  Iff.intro
    (combinedDebt_le_reserve_of_endpointAbsorbedPhysicalScalar_nonnegative
      f)
    (endpointAbsorbedPhysicalScalar_nonnegative_of_combinedDebt_le_reserve
      f)

/-- The combined trace-reserve domination theorem proves endpoint absorption. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceReserveDomination
    (f : ZetaAdmissibleFunction)
    (reserveDomination :
      ZetaCompletedEndpointTraceReserveDomination f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_combinedDebt_le_reserve
    f).mpr reserveDomination

/-- The positive endpoint trace-remainder theorem gives the endpoint
trace-reserve compression inequality. -/
theorem zetaCompletedEndpointTraceReserveCompression_owner
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedEndpointTraceReserveCompression f :=
  zetaCompletedEndpointTraceReserveCompression_of_traceReserveDomination
    f
    (combinedDebt_le_reserve_of_endpointAbsorbedPhysicalScalar_nonnegative
      f
      (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
        f
        (completedWeilEndpointTraceRemainder_nonnegative_owner f)))

/-- Owner theorem for endpoint trace-reserve domination in debt-coordinate
form. -/
theorem zetaCompletedEndpointTraceReserveDomination_owner
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedEndpointTraceReserveDomination f :=
  zetaCompletedEndpointTraceReserveDomination_of_traceCompression
    f
    (zetaCompletedEndpointTraceReserveCompression_owner f)

/-- Expanded form of endpoint trace-reserve domination. -/
theorem zetaCompletedEndpointTraceReserveDomination_iff_combinedDebt_le_reserve
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedEndpointTraceReserveDomination f ↔
      zetaCompletedEndpointDiagonalDebtScalar f +
          zetaCompletedNegativeArchimedeanDebtScalar f ≤
        zetaCompletedNormalizedSignedReserveScalar f :=
  Iff.rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
