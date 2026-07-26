import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.AdmissiblePackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels

/-!
# Completed-zeta endpoint correction packet

The poles of the meromorphic completed zeta function occur at centered
spectral coordinates `-1 / 2` and `1 / 2`.  On an autocorrelation probe their
combined correction is a Hermitian cross-pairing of the two seed evaluations,
not a centered evaluation at `0`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two seed evaluations at the completed-zeta endpoint coordinates. -/
structure ZetaCompletedEndpointCorrectionPacket where
  negativeEndpoint : ℂ
  positiveEndpoint : ℂ

/-- The endpoint packet attached to an admissible seed. -/
noncomputable def zetaCompletedEndpointCorrectionPacket
    (f : ZetaAdmissibleFunction) : ZetaCompletedEndpointCorrectionPacket where
  negativeEndpoint :=
    zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))
  positiveEndpoint :=
    zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)

/-- The Hermitian cross-pairing carried by an endpoint packet. -/
noncomputable def ZetaCompletedEndpointCorrectionPacket.crossPairing
    (packet : ZetaCompletedEndpointCorrectionPacket) : ℂ :=
  packet.negativeEndpoint * star packet.positiveEndpoint +
    packet.positiveEndpoint * star packet.negativeEndpoint

/-- The negative endpoint projection of the canonical packet. -/
theorem zetaCompletedEndpointCorrectionPacket_negativeEndpoint
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedEndpointCorrectionPacket f).negativeEndpoint =
      zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  exact Eq.refl _

/-- The positive endpoint projection of the canonical packet. -/
theorem zetaCompletedEndpointCorrectionPacket_positiveEndpoint
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedEndpointCorrectionPacket f).positiveEndpoint =
      zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ) := by
  exact Eq.refl _

/-- The endpoint cross-pairing is fixed by complex conjugation. -/
theorem ZetaCompletedEndpointCorrectionPacket.crossPairing_star
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    star packet.crossPairing = packet.crossPairing := by
  let negativeValue : ℂ := packet.negativeEndpoint
  let positiveValue : ℂ := packet.positiveEndpoint
  have firstTerm :
      star (negativeValue * star positiveValue) =
        positiveValue * star negativeValue := by
    calc
      star (negativeValue * star positiveValue) =
          star (star positiveValue) * star negativeValue := by
        exact star_mul negativeValue (star positiveValue)
      _ = positiveValue * star negativeValue := by
        exact congrArg
          (fun value : ℂ => value * star negativeValue)
          (star_star positiveValue)
  have secondTerm :
      star (positiveValue * star negativeValue) =
        negativeValue * star positiveValue := by
    calc
      star (positiveValue * star negativeValue) =
          star (star negativeValue) * star positiveValue := by
        exact star_mul positiveValue (star negativeValue)
      _ = negativeValue * star positiveValue := by
        exact congrArg
          (fun value : ℂ => value * star positiveValue)
          (star_star negativeValue)
  calc
    star packet.crossPairing =
        star (negativeValue * star positiveValue) +
          star (positiveValue * star negativeValue) := by
      exact star_add
        (negativeValue * star positiveValue)
        (positiveValue * star negativeValue)
    _ = positiveValue * star negativeValue +
          negativeValue * star positiveValue := by
      exact congrArg₂ HAdd.hAdd firstTerm secondTerm
    _ = negativeValue * star positiveValue +
          positiveValue * star negativeValue := by
      exact add_comm
        (positiveValue * star negativeValue)
        (negativeValue * star positiveValue)
    _ = packet.crossPairing := by
      exact Eq.refl _

/-- The endpoint correction of an autocorrelation probe is exactly the
Hermitian cross-pairing of its two seed endpoint evaluations. -/
theorem completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_eq_crossPairing
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointCorrectionChannel (convolutionAutocorrelation f) =
      (zetaCompletedEndpointCorrectionPacket f).crossPairing := by
  let negativePoint : ℂ := -(1 / 2 : ℂ)
  let positivePoint : ℂ := 1 / 2
  let negativeValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f negativePoint
  let positiveValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f positivePoint
  have negativeOpposite : -negativePoint = positivePoint := by
    exact neg_neg (1 / 2 : ℂ)
  have positiveOpposite : -positivePoint = negativePoint := by
    exact Eq.refl _
  have negativeFactorization :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) negativePoint =
        negativeValue * star positiveValue := by
    have factorization :=
      zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
        f (-(1 / 2 : ℝ))
    have negativeCast : ((-(1 / 2 : ℝ) : ℝ) : ℂ) = negativePoint := by
      unfold negativePoint
      have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) :=
        Complex.ofReal_div 1 2
      exact (Complex.ofReal_neg (1 / 2 : ℝ)).trans
        (congrArg Neg.neg hhalf)
    have oppositeCast : -((-(1 / 2 : ℝ) : ℝ) : ℂ) = positivePoint := by
      exact Eq.trans (congrArg Neg.neg negativeCast) negativeOpposite
    exact Eq.trans
      (congrArg
        (fun point : ℂ =>
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) point)
        negativeCast.symm)
      (Eq.trans factorization
        (congrArg₂ HMul.hMul
          (congrArg (zetaCompletedExplicitFormulaPhi f) negativeCast)
          (congrArg
            (fun point : ℂ =>
              star (zetaCompletedExplicitFormulaPhi f point))
            oppositeCast)))
  have positiveFactorization :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) positivePoint =
        positiveValue * star negativeValue := by
    have factorization :=
      zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
        f (1 / 2 : ℝ)
    have positiveCast : (((1 / 2 : ℝ) : ℝ) : ℂ) = positivePoint := by
      unfold positivePoint
      exact Complex.ofReal_div 1 2
    have oppositeCast : -(((1 / 2 : ℝ) : ℝ) : ℂ) = negativePoint := by
      exact Eq.trans (congrArg Neg.neg positiveCast) positiveOpposite
    exact Eq.trans
      (congrArg
        (fun point : ℂ =>
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) point)
        positiveCast.symm)
      (Eq.trans factorization
        (congrArg₂ HMul.hMul
          (congrArg (zetaCompletedExplicitFormulaPhi f) positiveCast)
          (congrArg
            (fun point : ℂ =>
              star (zetaCompletedExplicitFormulaPhi f point))
            oppositeCast)))
  calc
    completedWeilEndpointCorrectionChannel (convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) negativePoint +
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) positivePoint := by
      exact completedWeilEndpointCorrectionChannel_eq
        (convolutionAutocorrelation f)
    _ = negativeValue * star positiveValue +
          positiveValue * star negativeValue := by
      exact congrArg₂ HAdd.hAdd
        negativeFactorization positiveFactorization
    _ = (zetaCompletedEndpointCorrectionPacket f).crossPairing := by
      exact Eq.refl _

/-- The elementary expansion behind endpoint square completion. -/
theorem endpoint_sum_conjSquare_eq_diagonal_add_cross
    (negativeValue positiveValue : ℂ) :
    (negativeValue + positiveValue) *
        star (negativeValue + positiveValue) =
      (negativeValue * star negativeValue +
        positiveValue * star positiveValue) +
        (negativeValue * star positiveValue +
          positiveValue * star negativeValue) := by
  calc
    (negativeValue + positiveValue) *
        star (negativeValue + positiveValue) =
        (negativeValue + positiveValue) *
          (star negativeValue + star positiveValue) := by
      exact congrArg
        (fun value : ℂ => (negativeValue + positiveValue) * value)
        (star_add negativeValue positiveValue)
    _ = negativeValue * (star negativeValue + star positiveValue) +
          positiveValue * (star negativeValue + star positiveValue) := by
      exact add_mul negativeValue positiveValue
        (star negativeValue + star positiveValue)
    _ = (negativeValue * star negativeValue +
          negativeValue * star positiveValue) +
        (positiveValue * star negativeValue +
          positiveValue * star positiveValue) := by
      exact congrArg₂ HAdd.hAdd
        (mul_add negativeValue (star negativeValue) (star positiveValue))
        (mul_add positiveValue (star negativeValue) (star positiveValue))
    _ = (negativeValue * star negativeValue +
          positiveValue * star positiveValue) +
        (negativeValue * star positiveValue +
          positiveValue * star negativeValue) := by
      let diagonalNegative : ℂ := negativeValue * star negativeValue
      let crossNegativePositive : ℂ := negativeValue * star positiveValue
      let crossPositiveNegative : ℂ := positiveValue * star negativeValue
      let diagonalPositive : ℂ := positiveValue * star positiveValue
      calc
        (diagonalNegative + crossNegativePositive) +
            (crossPositiveNegative + diagonalPositive) =
            diagonalNegative +
              (crossNegativePositive +
                (crossPositiveNegative + diagonalPositive)) := by
          exact add_assoc diagonalNegative crossNegativePositive
            (crossPositiveNegative + diagonalPositive)
        _ = diagonalNegative +
              ((crossNegativePositive + crossPositiveNegative) +
                diagonalPositive) := by
          exact congrArg
            (fun value : ℂ => diagonalNegative + value)
            (add_assoc crossNegativePositive crossPositiveNegative
              diagonalPositive).symm
        _ = diagonalNegative +
              (diagonalPositive +
                (crossNegativePositive + crossPositiveNegative)) := by
          exact congrArg
            (fun value : ℂ => diagonalNegative + value)
            (add_comm
              (crossNegativePositive + crossPositiveNegative)
              diagonalPositive)
        _ = (diagonalNegative + diagonalPositive) +
              (crossNegativePositive + crossPositiveNegative) := by
          exact (add_assoc diagonalNegative diagonalPositive
            (crossNegativePositive + crossPositiveNegative)).symm

/-- The endpoint cross-pairing is the completed square minus its two
diagonal endpoint squares. -/
theorem ZetaCompletedEndpointCorrectionPacket.crossPairing_eq_completedSquare_sub_diagonal
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    packet.crossPairing =
      (packet.negativeEndpoint + packet.positiveEndpoint) *
          star (packet.negativeEndpoint + packet.positiveEndpoint) -
        (packet.negativeEndpoint * star packet.negativeEndpoint +
          packet.positiveEndpoint * star packet.positiveEndpoint) := by
  have expansion := endpoint_sum_conjSquare_eq_diagonal_add_cross
    packet.negativeEndpoint packet.positiveEndpoint
  let diagonal : ℂ :=
    packet.negativeEndpoint * star packet.negativeEndpoint +
      packet.positiveEndpoint * star packet.positiveEndpoint
  let cross : ℂ := packet.crossPairing
  have crossAddDiagonal :
      cross + diagonal =
        (packet.negativeEndpoint + packet.positiveEndpoint) *
          star (packet.negativeEndpoint + packet.positiveEndpoint) := by
    exact Eq.trans
      (add_comm cross diagonal)
      expansion.symm
  exact (eq_sub_iff_add_eq).mpr crossAddDiagonal

/-- The nonnegative square obtained by completing the two endpoint
coordinates. -/
noncomputable def ZetaCompletedEndpointCorrectionPacket.completedSquare
    (packet : ZetaCompletedEndpointCorrectionPacket) : ℝ :=
  Complex.normSq (packet.negativeEndpoint + packet.positiveEndpoint)

/-- The two diagonal endpoint squares introduced by square completion. -/
noncomputable def ZetaCompletedEndpointCorrectionPacket.diagonalDebt
    (packet : ZetaCompletedEndpointCorrectionPacket) : ℝ :=
  Complex.normSq packet.negativeEndpoint +
    Complex.normSq packet.positiveEndpoint

/-- The completed endpoint square is nonnegative. -/
theorem ZetaCompletedEndpointCorrectionPacket.completedSquare_nonnegative
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    0 ≤ packet.completedSquare := by
  exact Complex.normSq_nonneg
    (packet.negativeEndpoint + packet.positiveEndpoint)

/-- The endpoint diagonal debt is nonnegative. -/
theorem ZetaCompletedEndpointCorrectionPacket.diagonalDebt_nonnegative
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    0 ≤ packet.diagonalDebt := by
  exact add_nonneg
    (Complex.normSq_nonneg packet.negativeEndpoint)
    (Complex.normSq_nonneg packet.positiveEndpoint)

/-- The completed endpoint square is controlled by twice the diagonal
endpoint debt. -/
theorem ZetaCompletedEndpointCorrectionPacket.completedSquare_le_two_diagonalDebt
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    packet.completedSquare ≤ 2 * packet.diagonalDebt := by
  let negativeNorm : ℝ := ‖packet.negativeEndpoint‖
  let positiveNorm : ℝ := ‖packet.positiveEndpoint‖
  have endpointNormBound :
      ‖packet.negativeEndpoint + packet.positiveEndpoint‖ ≤
        negativeNorm + positiveNorm :=
    norm_add_le packet.negativeEndpoint packet.positiveEndpoint
  have endpointNormSquareBound :
      ‖packet.negativeEndpoint + packet.positiveEndpoint‖ ^ 2 ≤
        (negativeNorm + positiveNorm) ^ 2 :=
    pow_le_pow_left₀
      (norm_nonneg (packet.negativeEndpoint + packet.positiveEndpoint))
      endpointNormBound
      2
  have twoDiagonalBound :
      (negativeNorm + positiveNorm) ^ 2 ≤
        2 * (negativeNorm ^ 2 + positiveNorm ^ 2) :=
    add_sq_le
  calc
    packet.completedSquare =
        ‖packet.negativeEndpoint + packet.positiveEndpoint‖ ^ 2 := by
      exact Complex.normSq_eq_norm_sq
        (packet.negativeEndpoint + packet.positiveEndpoint)
    _ ≤ (negativeNorm + positiveNorm) ^ 2 :=
      endpointNormSquareBound
    _ ≤ 2 * (negativeNorm ^ 2 + positiveNorm ^ 2) :=
      twoDiagonalBound
    _ = 2 * packet.diagonalDebt := by
      exact congrArg
        (fun value : ℝ => 2 * value)
        (congrArg₂ HAdd.hAdd
          (Complex.normSq_eq_norm_sq packet.negativeEndpoint).symm
          (Complex.normSq_eq_norm_sq packet.positiveEndpoint).symm)

/-- The real endpoint cross-pairing is its completed square minus the named
diagonal endpoint debt. -/
theorem ZetaCompletedEndpointCorrectionPacket.crossPairing_re_eq_completedSquare_sub_diagonalDebt
    (packet : ZetaCompletedEndpointCorrectionPacket) :
    Complex.re packet.crossPairing =
      packet.completedSquare - packet.diagonalDebt := by
  let negativeValue : ℂ := packet.negativeEndpoint
  let positiveValue : ℂ := packet.positiveEndpoint
  have squareEquality :
      (negativeValue + positiveValue) *
          star (negativeValue + positiveValue) =
        (Complex.normSq (negativeValue + positiveValue) : ℂ) := by
    exact Complex.mul_conj (negativeValue + positiveValue)
  have negativeDiagonalEquality :
      negativeValue * star negativeValue =
        (Complex.normSq negativeValue : ℂ) := by
    exact Complex.mul_conj negativeValue
  have positiveDiagonalEquality :
      positiveValue * star positiveValue =
        (Complex.normSq positiveValue : ℂ) := by
    exact Complex.mul_conj positiveValue
  have complexEquality :
      packet.crossPairing =
        (Complex.normSq (negativeValue + positiveValue) : ℂ) -
          ((Complex.normSq negativeValue : ℂ) +
            (Complex.normSq positiveValue : ℂ)) := by
    exact Eq.trans
      packet.crossPairing_eq_completedSquare_sub_diagonal
      (congrArg₂ HSub.hSub
        squareEquality
        (congrArg₂ HAdd.hAdd
          negativeDiagonalEquality positiveDiagonalEquality))
  have realEquality := congrArg Complex.re complexEquality
  exact Eq.trans realEquality
    (Eq.trans
      (Complex.sub_re
        (Complex.normSq (negativeValue + positiveValue) : ℂ)
        ((Complex.normSq negativeValue : ℂ) +
          (Complex.normSq positiveValue : ℂ)))
      (congrArg₂ HSub.hSub
        (Complex.ofReal_re (Complex.normSq (negativeValue + positiveValue)))
        (Eq.trans
          (Complex.add_re
            (Complex.normSq negativeValue : ℂ)
            (Complex.normSq positiveValue : ℂ))
          (congrArg₂ HAdd.hAdd
            (Complex.ofReal_re (Complex.normSq negativeValue))
            (Complex.ofReal_re (Complex.normSq positiveValue))))))

/-- The autocorrelation endpoint correction has the completed-square minus
diagonal-debt scalar normal form. -/
theorem completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (completedWeilEndpointCorrectionChannel
          (convolutionAutocorrelation f)) =
      (zetaCompletedEndpointCorrectionPacket f).completedSquare -
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt := by
  have endpointReconstruction :
      completedWeilEndpointCorrectionChannel
          (convolutionAutocorrelation f) =
        (zetaCompletedEndpointCorrectionPacket f).crossPairing :=
    completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_eq_crossPairing
      f
  exact Eq.trans
    (congrArg Complex.re endpointReconstruction)
    ((zetaCompletedEndpointCorrectionPacket f).crossPairing_re_eq_completedSquare_sub_diagonalDebt)

/-- The physical boundary scalar after absorbing the two diagonal endpoint
squares introduced by endpoint square completion. -/
noncomputable def completedWeilEndpointAbsorbedPhysicalScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt

/-- The endpoint-absorbed physical scalar is the raw physical boundary
scalar minus the two endpoint diagonal squares. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    completedWeilEndpointAbsorbedPhysicalScalar f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt := by
  exact Eq.refl _

/-- The endpoint absorption inequality is exactly the nonnegativity of the
endpoint-absorbed physical scalar. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_diagonalDebt_le_boundary
    (f : ZetaAdmissibleFunction)
    (endpointDebtBound :
      (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f := by
  have hsub :
      0 ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
          (zetaCompletedEndpointCorrectionPacket f).diagonalDebt :=
    sub_nonneg.mpr endpointDebtBound
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
      f).symm
    hsub

/-- Nonnegativity of the endpoint-absorbed physical scalar is exactly the
statement that the physical boundary dominates the endpoint diagonal debt. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_iff_diagonalDebt_le_boundary
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f ↔
      (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  constructor
  · intro hnonnegative
    have hsub :
        0 ≤
          Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) -
            (zetaCompletedEndpointCorrectionPacket f).diagonalDebt :=
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
          f)
        hnonnegative
    exact sub_nonneg.mp hsub
  · intro endpointDebtBound
    exact
      completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_diagonalDebt_le_boundary
        f endpointDebtBound

/-- If the physical boundary splits as endpoint diagonal debt plus a
remainder, then the endpoint-absorbed physical scalar is that remainder. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_eq_remainder_of_boundary_eq_diagonalDebt_add_remainder
    (f : ZetaAdmissibleFunction)
    (remainder : ℝ)
    (boundarySplit :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt + remainder) :
    completedWeilEndpointAbsorbedPhysicalScalar f = remainder := by
  let physical : ℝ :=
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
  let debt : ℝ :=
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  have absorbedUnfold :
      completedWeilEndpointAbsorbedPhysicalScalar f = physical - debt :=
    completedWeilEndpointAbsorbedPhysicalScalar_eq_boundaryChannel_re_sub_diagonalDebt
      f
  have split : physical = debt + remainder := boundarySplit
  have cancel :
      (debt + remainder) - debt = remainder := by
    calc
      (debt + remainder) - debt =
          (debt + remainder) + -debt := by
        exact sub_eq_add_neg (debt + remainder) debt
      _ = debt + (remainder + -debt) := by
        exact add_assoc debt remainder (-debt)
      _ = debt + (-debt + remainder) := by
        exact congrArg
          (fun value : ℝ => debt + value)
          (add_comm remainder (-debt))
      _ = (debt + -debt) + remainder := by
        exact (add_assoc debt (-debt) remainder).symm
      _ = 0 + remainder := by
        exact congrArg
          (fun value : ℝ => value + remainder)
          (add_neg_cancel debt)
      _ = remainder := by
        exact zero_add remainder
  exact absorbedUnfold.trans
    ((congrArg (fun value : ℝ => value - debt) split).trans cancel)

/-- A nonnegative trace-reconstruction remainder proves endpoint absorption. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_boundary_eq_diagonalDebt_add_nonnegativeRemainder
    (f : ZetaAdmissibleFunction)
    (remainder : ℝ)
    (boundarySplit :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt + remainder)
    (remainderNonnegative : 0 ≤ remainder) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilEndpointAbsorbedPhysicalScalar_eq_remainder_of_boundary_eq_diagonalDebt_add_remainder
      f remainder boundarySplit).symm
    remainderNonnegative

/-- A nonnegative trace-reconstruction remainder is equivalently a direct
domination of endpoint diagonal debt by the physical boundary. -/
theorem endpointDiagonalDebt_le_boundary_of_boundary_eq_diagonalDebt_add_nonnegativeRemainder
    (f : ZetaAdmissibleFunction)
    (remainder : ℝ)
    (boundarySplit :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        (zetaCompletedEndpointCorrectionPacket f).diagonalDebt + remainder)
    (remainderNonnegative : 0 ≤ remainder) :
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let debt : ℝ :=
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  have debtLeSplit : debt ≤ debt + remainder :=
    le_add_of_nonneg_right remainderNonnegative
  exact Eq.subst
    (motive := fun value : ℝ => debt ≤ value)
    boundarySplit.symm
    debtLeSplit

/-- The completed Weil boundary is the endpoint-absorbed physical scalar plus
the nonnegative completed endpoint square. -/
theorem completedWeilBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_completedSquare
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (completedWeilBoundaryChannel (convolutionAutocorrelation f)) =
      completedWeilEndpointAbsorbedPhysicalScalar f +
        (zetaCompletedEndpointCorrectionPacket f).completedSquare := by
  let physical : ℝ :=
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
  let square : ℝ :=
    (zetaCompletedEndpointCorrectionPacket f).completedSquare
  let debt : ℝ :=
    (zetaCompletedEndpointCorrectionPacket f).diagonalDebt
  have boundarySplit :
      Complex.re
          (completedWeilBoundaryChannel (convolutionAutocorrelation f)) =
        physical +
          Complex.re
            (completedWeilEndpointCorrectionChannel
              (convolutionAutocorrelation f)) := by
    exact Eq.trans
      (congrArg Complex.re
        (completedWeilBoundaryChannel_eq
          (convolutionAutocorrelation f)))
      (Complex.add_re
        (completedBoundaryChannel (convolutionAutocorrelation f))
        (completedWeilEndpointCorrectionChannel
          (convolutionAutocorrelation f)))
  have correctionSplit :
      Complex.re
          (completedWeilEndpointCorrectionChannel
            (convolutionAutocorrelation f)) =
        square - debt :=
    completedWeilEndpointCorrectionChannel_convolutionAutocorrelation_re_eq_completedSquare_sub_diagonalDebt
      f
  have scalarRegroup :
      physical + (square - debt) = (physical - debt) + square := by
    calc
      physical + (square - debt) =
          physical + (square + (-debt)) := by
        exact congrArg
          (fun value : ℝ => physical + value)
          (sub_eq_add_neg square debt)
      _ = physical + ((-debt) + square) := by
        exact congrArg
          (fun value : ℝ => physical + value)
          (add_comm square (-debt))
      _ = (physical + (-debt)) + square := by
        exact (add_assoc physical (-debt) square).symm
      _ = (physical - debt) + square := by
        exact congrArg
          (fun value : ℝ => value + square)
          (sub_eq_add_neg physical debt).symm
  exact Eq.trans boundarySplit
    (Eq.trans
      (congrArg (fun value : ℝ => physical + value) correctionSplit)
      scalarRegroup)

/-- Nonnegativity of the endpoint-absorbed physical scalar is sufficient for
nonnegativity of the canonical completed Weil boundary. -/
theorem completedWeilBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_absorbedPhysical
    (f : ZetaAdmissibleFunction)
    (absorbedPhysicalNonnegative :
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f) :
    0 ≤ Complex.re
      (completedWeilBoundaryChannel (convolutionAutocorrelation f)) := by
  have completedSquareNonnegative :
      0 ≤ (zetaCompletedEndpointCorrectionPacket f).completedSquare :=
    (zetaCompletedEndpointCorrectionPacket f).completedSquare_nonnegative
  have sumNonnegative :
      0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f +
        (zetaCompletedEndpointCorrectionPacket f).completedSquare :=
    add_nonneg absorbedPhysicalNonnegative completedSquareNonnegative
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilBoundaryChannel_convolutionAutocorrelation_re_eq_absorbedPhysical_add_completedSquare
      f).symm
    sumNonnegative

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
