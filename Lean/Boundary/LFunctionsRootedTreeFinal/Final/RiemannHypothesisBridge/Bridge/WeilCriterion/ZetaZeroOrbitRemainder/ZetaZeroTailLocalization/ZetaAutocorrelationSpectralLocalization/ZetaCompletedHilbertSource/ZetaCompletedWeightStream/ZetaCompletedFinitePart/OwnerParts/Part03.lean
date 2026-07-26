import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.OwnerParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

theorem completedCorrectedBoundaryWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ completedCorrectedBoundaryWindow N f := by
  unfold completedCorrectedBoundaryWindow
  exact zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_nonnegative N f

/-- Finite-part convergence to the completed physical finite-part boundary channel. This is the
genuine completed-normalization theorem before comparison with the explicit-formula boundary
functional. -/
theorem finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (completedFinitePartBoundaryChannel f)) := by
  let c : ℝ := completedFinitePartBoundaryChannel f
  have hrem :
      Tendsto (fun N : ℕ => finitePartBoundaryRemainder N f) atTop (𝓝 0) :=
    finitePartBoundaryRemainder_tendsto_zero f
  have hsum :
      Tendsto
        (fun N : ℕ => c + finitePartBoundaryRemainder N f)
        atTop
        (𝓝 (c + 0)) := by
    exact (tendsto_const_nhds.add hrem)
  have htarget : c + 0 = c := by
    exact add_zero c
  have hfinite :
      (fun N : ℕ => finitePartBoundaryWindow N f) =
      (fun N : ℕ => c + finitePartBoundaryRemainder N f) := by
    funext N
    exact finitePartBoundaryWindow_eq_boundaryChannel_add_remainder N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 c))
    hfinite.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto (fun N : ℕ => c + finitePartBoundaryRemainder N f) atTop (𝓝 x))
      htarget
      hsum)

/-- The completed physical finite-part channel is the real explicit-formula completed boundary
channel on the convolution-autocorrelation probe.  This is the owner bridge between the
renormalized square-energy completion and the explicit-formula boundary functional. -/
theorem completedFinitePartBoundaryChannel_eq_completedBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  have hprime :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel g) := by
    unfold g
    exact completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have harch :
      zetaArchimedeanAutocorrelationSquareEnergy f =
        Complex.re (archimedeanBoundaryChannel g) := by
    unfold g
    unfold archimedeanBoundaryChannel
    exact (zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f).symm
  have hcorr :
      zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (poleBoundaryChannel g) := by
    unfold g
    unfold poleBoundaryChannel
    exact (zetaCorrectionAutocorrelationChannel_eq_squareEnergy f).symm
  have hcompletion :
      Complex.re (completionBoundaryChannel g) = 0 := by
    unfold g
    unfold completionBoundaryChannel
    exact Complex.zero_re
  have hboundary :
      Complex.re (completedBoundaryChannel g) =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
    have hdecomp :
        completedBoundaryChannel g =
          primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g +
            completionBoundaryChannel g :=
      completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
    calc
      Complex.re (completedBoundaryChannel g) =
          Complex.re
            (primeBoundaryChannel g +
              archimedeanBoundaryChannel g +
              poleBoundaryChannel g +
              completionBoundaryChannel g) := by
        exact congrArg Complex.re hdecomp
      _ =
          Complex.re
              (primeBoundaryChannel g +
                archimedeanBoundaryChannel g +
                poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        exact Complex.add_re
          (primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g)
          (completionBoundaryChannel g)
      _ =
          (Complex.re (primeBoundaryChannel g + archimedeanBoundaryChannel g) +
              Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ => x + Complex.re (completionBoundaryChannel g))
          (Complex.add_re
            (primeBoundaryChannel g + archimedeanBoundaryChannel g)
            (poleBoundaryChannel g))
      _ =
          ((Complex.re (primeBoundaryChannel g) +
              Complex.re (archimedeanBoundaryChannel g)) +
            Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ =>
            (x + Complex.re (poleBoundaryChannel g)) +
              Complex.re (completionBoundaryChannel g))
          (Complex.add_re (primeBoundaryChannel g) (archimedeanBoundaryChannel g))
      _ =
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        rfl
  unfold completedFinitePartBoundaryChannel
  calc
    completedPrimeOffDiagonalChannel f +
        zetaArchimedeanAutocorrelationSquareEnergy f +
        zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hprime harch)
        hcorr
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          0 := by
      exact (add_zero
        (Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g))).symm
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) + x)
        hcompletion.symm
    _ = Complex.re (completedBoundaryChannel g) := by
      exact hboundary.symm

/-- Finite-part convergence to the completed boundary channel. This is the genuine completed
normalization theorem: diagonal debt cancellation has already happened inside
`finitePartBoundaryWindow`, so no separate convergence of the raw prime window is asserted. -/
theorem finitePartBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      Tendsto
        (fun N : ℕ => finitePartBoundaryWindow N f)
        atTop
        (𝓝 (completedFinitePartBoundaryChannel f)) :=
    finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto (fun N : ℕ => finitePartBoundaryWindow N f) atTop (𝓝 x))
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f)
    hfinite

/-- The finite positive square-energy windows, after finite diagonal-debt absorption, converge
to the completed boundary channel.  This is pure assembly: the absorption-renormalized positive
window is the finite-part window, and the finite-part window has the tail convergence
certificate above. -/
theorem finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_boundaryChannel f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
