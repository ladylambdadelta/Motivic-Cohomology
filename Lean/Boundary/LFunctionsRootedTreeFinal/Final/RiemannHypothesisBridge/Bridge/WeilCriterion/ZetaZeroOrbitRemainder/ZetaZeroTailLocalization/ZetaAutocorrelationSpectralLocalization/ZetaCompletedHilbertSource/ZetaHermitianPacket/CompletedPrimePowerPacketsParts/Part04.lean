import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPacketsParts.Part03

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The raw completed positive prime defect-kernel presentation is its coordinate sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_positiveCoordinateTsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      ∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f := by
  exact Eq.refl _

/-- The finite completed prime defect-square expansion passes to the completed prime-power
realization.

This is the completed transport theorem for the three prime channels: positive defect
square, symmetrized two-face coefficient, and diagonal debt.  It is not proved from
real-axis spectral-coordinate summability; the owner proof must pass through the finite
defect-square windows, the prime distribution transport, and the completed contour
realization. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  exact sub_add_cancel (Df - Tf + T) T

/-- If the completed diagonal-debt coordinate presentation transports to the owner completed
diagonal debt, then the raw completed positive coordinate presentation has the owner positive
channel as its real scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  let Pcoord : ℂ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Dcoord : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f
  let Powner : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let Downer : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  have hcoord_complex : Pcoord + T = Dcoord :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
      f hmajorant
  have howner_complex : Powner + T = Downer :=
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f
  have hcoord_re :
      Complex.re Pcoord + Complex.re T = Complex.re Dcoord := by
    calc
      Complex.re Pcoord + Complex.re T = Complex.re (Pcoord + T) := by
        exact (Complex.add_re Pcoord T).symm
      _ = Complex.re Dcoord := by
        exact congrArg Complex.re hcoord_complex
  have howner_re :
      completedPrimeDefectKernelPositiveChannel f + Complex.re T =
        Complex.re Downer := by
    calc
      completedPrimeDefectKernelPositiveChannel f + Complex.re T =
          Complex.re Powner + Complex.re T := by
        exact Eq.refl _
      _ = Complex.re (Powner + T) := by
        exact (Complex.add_re Powner T).symm
      _ = Complex.re Downer := by
        exact congrArg Complex.re howner_complex
  have hsame_sum :
      Complex.re Pcoord + Complex.re T =
        completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
    exact hcoord_re.trans (hdiagonal.trans howner_re.symm)
  have hcancel :
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
        (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T := by
    exact congrArg (fun x : ℝ => x + -Complex.re T) hsame_sum
  have hleft :
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
        Complex.re Pcoord := by
    calc
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
          Complex.re Pcoord + (Complex.re T + -Complex.re T) := by
        exact add_assoc (Complex.re Pcoord) (Complex.re T) (-Complex.re T)
      _ = Complex.re Pcoord + 0 := by
        exact congrArg
          (fun x : ℝ => Complex.re Pcoord + x)
          (add_neg_cancel (Complex.re T))
      _ = Complex.re Pcoord := by
        exact add_zero (Complex.re Pcoord)
  have hright :
      (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T =
        completedPrimeDefectKernelPositiveChannel f := by
    calc
      (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T =
          completedPrimeDefectKernelPositiveChannel f +
            (Complex.re T + -Complex.re T) := by
        exact add_assoc
          (completedPrimeDefectKernelPositiveChannel f)
          (Complex.re T)
          (-Complex.re T)
      _ = completedPrimeDefectKernelPositiveChannel f + 0 := by
        exact congrArg
          (fun x : ℝ => completedPrimeDefectKernelPositiveChannel f + x)
          (add_neg_cancel (Complex.re T))
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact add_zero (completedPrimeDefectKernelPositiveChannel f)
  calc
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        Complex.re Pcoord := by
      exact Eq.refl _
    _ =
        (Complex.re Pcoord + Complex.re T) + -Complex.re T := by
      exact hleft.symm
    _ =
        (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T := by
      exact hcancel
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact hright

/-- Under spectral-majorant summability, comparing the raw completed positive coordinate
presentation with the owner positive channel is equivalent to comparing the corresponding
diagonal-debt presentations. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_iff_diagonalDebtCoordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
  constructor
  · intro hpositive
    let Pcoord : ℂ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f
    let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
    let Dcoord : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f
    let Powner : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
    let Downer : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
    have hcoord_complex : Pcoord + T = Dcoord :=
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
        f hmajorant
    have howner_complex : Powner + T = Downer :=
      zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f
    have hcoord_re :
        Complex.re Dcoord =
          zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + Complex.re T := by
      calc
        Complex.re Dcoord = Complex.re (Pcoord + T) := by
          exact congrArg Complex.re hcoord_complex.symm
        _ = Complex.re Pcoord + Complex.re T := by
          exact Complex.add_re Pcoord T
        _ =
            zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
              Complex.re T := by
          exact Eq.refl _
    have howner_re :
        Complex.re Downer =
          completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
      calc
        Complex.re Downer = Complex.re (Powner + T) := by
          exact congrArg Complex.re howner_complex.symm
        _ = Complex.re Powner + Complex.re T := by
          exact Complex.add_re Powner T
        _ =
            completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
          exact Eq.refl _
    calc
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          Complex.re Dcoord := by
        exact Eq.refl _
      _ =
          zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re T := by
        exact hcoord_re
      _ =
          completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
        exact congrArg (fun x : ℝ => x + Complex.re T) hpositive
      _ = Complex.re Downer := by
        exact howner_re.symm
      _ = Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
        exact Eq.refl _
  · intro hdiagonal
    exact
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
        f hmajorant hdiagonal

/-- Diagonal-debt finite-window convergence to the owner completed diagonal debt identifies
the raw positive coordinate presentation with the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  have hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    tendsto_nhds_unique hcoordinateLimit hdiagonalOwnerLimit
  exact
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonal

/-- The owner completed diagonal debt has zero real part once the completed and reconstructed
two-face real coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    (f : ZetaAdmissibleFunction)
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  have hfinite : Complex.re Df = 0 := by
    exact zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_completedLowerWeightNormalization
      f
  have hre :
      Complex.re (Df - Tf + Tc) =
        Complex.re Df - Complex.re Tf + Complex.re Tc := by
    calc
      Complex.re (Df - Tf + Tc) =
          Complex.re (Df - Tf) + Complex.re Tc := by
        exact Complex.add_re (Df - Tf) Tc
      _ = (Complex.re Df - Complex.re Tf) + Complex.re Tc := by
        exact congrArg (fun x : ℝ => x + Complex.re Tc)
          (Complex.sub_re Df Tf)
      _ = Complex.re Df - Complex.re Tf + Complex.re Tc := by
        exact Eq.refl _
  calc
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re (Df - Tf + Tc) := by
      exact Eq.refl _
    _ = Complex.re Df - Complex.re Tf + Complex.re Tc := by
      exact hre
    _ = 0 - Complex.re Tf + Complex.re Tc := by
      exact congrArg
        (fun x : ℝ => x - Complex.re Tf + Complex.re Tc)
        hfinite
    _ = 0 - Complex.re Tf + Complex.re Tf := by
      exact congrArg
        (fun x : ℝ => 0 - Complex.re Tf + x)
        htwoFace
    _ = -Complex.re Tf + Complex.re Tf := by
      exact congrArg
        (fun x : ℝ => x + Complex.re Tf)
        (zero_sub (Complex.re Tf))
    _ = 0 := by
      exact neg_add_cancel (Complex.re Tf)

/-- The completed positive prime defect-kernel channel is the finite positive prime defect
form transported through the completed defect-square expansion. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  let Pc : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  have hfinite :
      zetaPrimeDefectKernelPositiveForm f + Tf = Df :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    Complex.re ((Df - Tf + Tc) - Tc) =
        Complex.re (Df - Tf) := by
      exact congrArg Complex.re (add_sub_cancel_right (Df - Tf) Tc)
    _ = Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
      have hpositive : Df - Tf = zetaPrimeDefectKernelPositiveForm f := by
        calc
          Df - Tf = (zetaPrimeDefectKernelPositiveForm f + Tf) - Tf := by
            exact congrArg (fun z : ℂ => z - Tf) hfinite.symm
          _ = zetaPrimeDefectKernelPositiveForm f := by
            exact add_sub_cancel_right (zetaPrimeDefectKernelPositiveForm f) Tf
      exact congrArg Complex.re hpositive

/-- Under the current finite-display lower-weight normalization, the owner completed positive
prime defect-kernel channel has zero real scalar. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f = 0 := by
  calc
    completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
      exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
    _ = 0 := by
      exact zetaPrimeDefectKernelPositiveForm_re_eq_zero_of_completedLowerWeightNormalization
        f

/-- Diagonal-coordinate vanishing and positive-channel faithfulness force the
completed two-face real scalar to vanish. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_diagonalCoordinate_zero_and_positiveChannel
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hfaithful :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
  let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let Dcoord : ℝ :=
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
  have hpositiveZero : P = 0 := by
    calc
      P =
          zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
        unfold P
        exact Eq.refl _
      _ =
          completedPrimeDefectKernelPositiveChannel f := by
        exact hfaithful
      _ = 0 := by
        exact completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
          f
  have hexpansion : P + T = Dcoord := by
    unfold P
    unfold T
    unfold Dcoord
    calc
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact Eq.refl _
      _ =
          Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
              zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact
          (Complex.add_re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
            (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
      _ =
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
        exact congrArg Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
            f hmajorant)
  have hsumZero : P + T = 0 := by
    calc
      P + T = Dcoord := by
        exact hexpansion
      _ =
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
        unfold Dcoord
        exact Eq.refl _
      _ = 0 := by
        exact hdiagonal
  have htransport : T = P + T := by
    calc
      T = 0 + T := by
        exact (zero_add T).symm
      _ = P + T := by
        exact congrArg (fun value : ℝ => value + T) hpositiveZero.symm
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = T := by
      unfold T
      exact Eq.refl _
    _ = P + T := by
      exact htransport
    _ = 0 := by
      exact hsumZero

/-- The completed positive prime defect-kernel channel is nonnegative. -/
theorem completedPrimeDefectKernelPositiveChannel_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedPrimeDefectKernelPositiveChannel f := by
  have hchannel :
      completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) :=
    completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hchannel.symm
    (zetaPrimeDefectKernelPositiveForm_re_nonnegative f)

/-- The completed symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.im
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
          f).symm
    _ = 0 := by
      exact complex_im_tsum_eq_zero_of_forall_im_eq_zero
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_im_eq_zero ι f)

/-- The completed prime two-face boundary coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        Complex.im (-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
    _ =
        -Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact Complex.neg_im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    _ = -0 := by
      exact congrArg Neg.neg
        (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)
    _ = 0 := by
      exact neg_zero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
