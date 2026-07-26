import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.EndpointCorrectionPacket

/-!
# Endpoint trace reconstruction

This file owns the endpoint-compression scalar for the completed Weil
boundary.  The scalar is the positive-trace remainder that remains after
removing the two endpoint diagonal fibers from the physical boundary trace.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two-dimensional endpoint fiber reconstructed from the completed
boundary trace. -/
structure CompletedWeilEndpointTraceFiber where
  negativeFiber : ℂ
  positiveFiber : ℂ

namespace CompletedWeilEndpointTraceFiber

/-- The diagonal Gram scalar of the endpoint fiber. -/
noncomputable def gram (fiber : CompletedWeilEndpointTraceFiber) : ℝ :=
  Complex.normSq fiber.negativeFiber +
    Complex.normSq fiber.positiveFiber

/-- The endpoint fiber Gram is nonnegative. -/
theorem gram_nonnegative
    (fiber : CompletedWeilEndpointTraceFiber) :
    0 ≤ fiber.gram := by
  exact add_nonneg
    (Complex.normSq_nonneg fiber.negativeFiber)
    (Complex.normSq_nonneg fiber.positiveFiber)

end CompletedWeilEndpointTraceFiber

/-- Adding back the named endpoint compression remainder recovers the original
physical scalar. -/
theorem endpointTraceDebt_add_sub_cancel
    (physical debt : ℝ) :
    physical = debt + (physical - debt) := by
  have hright : debt + (physical - debt) = physical := by
    calc
      debt + (physical - debt) =
          debt + (physical + -debt) := by
        exact congrArg (fun value : ℝ => debt + value)
          (sub_eq_add_neg physical debt)
      _ = (debt + physical) + -debt := by
        exact (add_assoc debt physical (-debt)).symm
      _ = (physical + debt) + -debt := by
        exact congrArg
          (fun value : ℝ => value + -debt)
          (add_comm debt physical)
      _ = physical + (debt + -debt) := by
        exact add_assoc physical debt (-debt)
      _ = physical + 0 := by
        exact congrArg
          (fun value : ℝ => physical + value)
          (add_neg_cancel debt)
      _ = physical := by
        exact add_zero physical
  exact hright.symm

/-- The endpoint trace-compression remainder attached to an admissible seed.

This is the scalar whose nonnegativity says that the physical completed
boundary trace dominates the two endpoint diagonal fibers. -/
noncomputable def completedWeilEndpointTraceRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt

/-- The endpoint trace fiber attached to an admissible seed. -/
noncomputable def completedWeilEndpointTraceFiber
    (f : ZetaAdmissibleFunction) :
    CompletedWeilEndpointTraceFiber :=
  { negativeFiber :=
      (zetaCompletedEndpointCorrectionPacket f).negativeEndpoint
    positiveFiber :=
      (zetaCompletedEndpointCorrectionPacket f).positiveEndpoint }

/-- The endpoint trace fiber Gram is the endpoint diagonal debt. -/
theorem completedWeilEndpointTraceFiber_gram_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    (completedWeilEndpointTraceFiber f).gram =
      (zetaCompletedEndpointCorrectionPacket f).diagonalDebt := by
  rfl

/-- The endpoint trace fiber Gram is the sum of the two endpoint evaluation
norm-squares. -/
theorem completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add
    (f : ZetaAdmissibleFunction) :
    (completedWeilEndpointTraceFiber f).gram =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) := by
  rfl

/-- The endpoint trace fiber Gram is nonnegative. -/
theorem completedWeilEndpointTraceFiber_gram_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ (completedWeilEndpointTraceFiber f).gram :=
  (completedWeilEndpointTraceFiber f).gram_nonnegative

/-- The endpoint trace remainder is the endpoint-absorbed physical scalar. -/
theorem completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointTraceRemainder f =
      completedWeilEndpointAbsorbedPhysicalScalar f := by
  rfl

/-- The physical boundary trace splits into endpoint diagonal debt plus the
named endpoint trace remainder. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointDebt_add_traceRemainder
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      (zetaCompletedEndpointCorrectionPacket f).diagonalDebt +
        completedWeilEndpointTraceRemainder f := by
  let physical : ℝ :=
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
  let debt : ℝ :=
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  have split : physical = debt + (physical - debt) :=
    endpointTraceDebt_add_sub_cancel physical debt
  exact split

/-- The physical boundary trace splits into the endpoint fiber Gram plus the
named endpoint trace remainder. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointFiberGram_add_traceRemainder
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      (completedWeilEndpointTraceFiber f).gram +
        completedWeilEndpointTraceRemainder f := by
  exact Eq.trans
    (completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointDebt_add_traceRemainder
      f)
    (congrArg
      (fun value : ℝ => value + completedWeilEndpointTraceRemainder f)
      (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f).symm)

/-- Positive-kernel endpoint trace split for the physical boundary trace. -/
def ZetaCompletedEndpointTracePositiveKernelSplit
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ kernelRemainder : ℝ,
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      (completedWeilEndpointTraceFiber f).gram + kernelRemainder ∧
    0 ≤ kernelRemainder

/-- Endpoint trace-remainder nonnegativity gives the positive-kernel split. -/
theorem zetaCompletedEndpointTracePositiveKernelSplit_of_traceRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (traceRemainderNonnegative :
      0 ≤ completedWeilEndpointTraceRemainder f) :
    ZetaCompletedEndpointTracePositiveKernelSplit f :=
  ⟨completedWeilEndpointTraceRemainder f,
    completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointFiberGram_add_traceRemainder f,
    traceRemainderNonnegative⟩

/-- Nonnegativity of the endpoint trace remainder is exactly endpoint
absorption. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_iff_absorbedPhysical
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeilEndpointTraceRemainder f ↔
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f := by
  constructor
  · intro remainderNonnegative
    exact Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar f)
      remainderNonnegative
  · intro absorbedNonnegative
    exact Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar f).symm
      absorbedNonnegative

/-- Nonnegativity of the endpoint trace remainder is exactly domination of the
endpoint fiber Gram by the physical boundary trace. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_iff_endpointFiberGram_le_boundary
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeilEndpointTraceRemainder f ↔
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  constructor
  · intro traceRemainderNonnegative
    have diagonalBound :
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
      (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
        f).mp
        ((completedWeilEndpointTraceRemainder_nonnegative_iff_absorbedPhysical
          f).mp traceRemainderNonnegative)
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))
      (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f).symm
      diagonalBound
  · intro endpointFiberBound
    have diagonalBound :
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
      Eq.subst
        (motive := fun value : ℝ =>
          value ≤
            Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))
        (completedWeilEndpointTraceFiber_gram_eq_diagonalDebt f)
        endpointFiberBound
    exact
      (completedWeilEndpointTraceRemainder_nonnegative_iff_absorbedPhysical
        f).mpr
        ((completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
          f).mpr diagonalBound)

/-- A positive-kernel endpoint trace split gives nonnegativity of the named
endpoint trace remainder. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_of_positiveKernelSplit
    (f : ZetaAdmissibleFunction)
    (positiveKernelSplit :
      ZetaCompletedEndpointTracePositiveKernelSplit f) :
    0 ≤ completedWeilEndpointTraceRemainder f := by
  match positiveKernelSplit with
  | ⟨kernelRemainder, boundarySplit, kernelNonnegative⟩ =>
      have endpointFiberBound :
          (completedWeilEndpointTraceFiber f).gram ≤
            Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
        have endpointFiberLeSplit :
            (completedWeilEndpointTraceFiber f).gram ≤
              (completedWeilEndpointTraceFiber f).gram + kernelRemainder :=
          le_add_of_nonneg_right kernelNonnegative
        exact Eq.subst
          (motive := fun value : ℝ =>
            (completedWeilEndpointTraceFiber f).gram ≤ value)
          boundarySplit.symm
          endpointFiberLeSplit
      exact
        (completedWeilEndpointTraceRemainder_nonnegative_iff_endpointFiberGram_le_boundary
          f).mpr endpointFiberBound

/-- The positive-kernel endpoint trace split is equivalent to nonnegativity of
the named endpoint trace remainder. -/
theorem zetaCompletedEndpointTracePositiveKernelSplit_iff_traceRemainder_nonnegative
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedEndpointTracePositiveKernelSplit f ↔
      0 ≤ completedWeilEndpointTraceRemainder f := by
  constructor
  · intro positiveKernelSplit
    exact
      completedWeilEndpointTraceRemainder_nonnegative_of_positiveKernelSplit
        f positiveKernelSplit
  · intro traceRemainderNonnegative
    exact
      zetaCompletedEndpointTracePositiveKernelSplit_of_traceRemainder_nonnegative
        f traceRemainderNonnegative

/-- Endpoint trace-compression nonnegativity gives endpoint absorption. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
    (f : ZetaAdmissibleFunction)
    (traceRemainderNonnegative :
      0 ≤ completedWeilEndpointTraceRemainder f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  (completedWeilEndpointTraceRemainder_nonnegative_iff_absorbedPhysical f).mp
    traceRemainderNonnegative

/-- Endpoint trace-compression nonnegativity gives the existential split form
used by older bridge statements. -/
theorem exists_endpointTraceRemainder_split_of_traceRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (traceRemainderNonnegative :
      0 ≤ completedWeilEndpointTraceRemainder f) :
    ∃ remainder : ℝ,
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt + remainder ∧
      0 ≤ remainder :=
  ⟨completedWeilEndpointTraceRemainder f,
    completedBoundaryChannel_convolutionAutocorrelation_re_eq_endpointDebt_add_traceRemainder f,
    traceRemainderNonnegative⟩

/-- Endpoint trace-compression nonnegativity proves nonnegativity of the
canonical completed Weil boundary on one autocorrelation probe. -/
theorem completedWeilBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointTraceRemainder
    (f : ZetaAdmissibleFunction)
    (traceRemainderNonnegative :
      0 ≤ completedWeilEndpointTraceRemainder f) :
    0 ≤ Complex.re
      (completedWeilBoundaryChannel (convolutionAutocorrelation f)) := by
  exact completedWeilBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_absorbedPhysical
    f
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
      f traceRemainderNonnegative)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
