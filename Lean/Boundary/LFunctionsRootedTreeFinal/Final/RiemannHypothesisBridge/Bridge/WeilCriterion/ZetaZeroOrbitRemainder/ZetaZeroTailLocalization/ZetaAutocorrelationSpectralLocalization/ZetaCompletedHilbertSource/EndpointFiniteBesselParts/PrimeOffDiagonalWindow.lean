import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction

/-!
# Prime off-diagonal finite-window stabilization

This file owns the finite-window stabilization of the prime off-diagonal
channel used by endpoint trace exhaustion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A rectangular cutoff containing all bounded genuine prime-power centers
contains the corresponding off-diagonal support finset in the genuine window. -/
theorem zetaPrimeOffDiagonalSupportFinsetOfBound_subset_window_of_box_bound
    (f : ZetaAdmissibleFunction) (B : ℝ) (cutoff : ℕ)
    (hcutoff :
      ∀ ι : ZetaPrimePowerIndex,
        ZetaPrimePowerIndex.IsGenuine ι →
          ZetaPrimePowerIndex.center ι ≤ B →
            ι ∈ ZetaPrimePowerIndex.box cutoff) :
    zetaPrimeOffDiagonalSupportFinsetOfBound f B ⊆
      ZetaPrimePowerIndex.window cutoff :=
  fun ι hι =>
  let hsupport :
      ZetaPrimePowerIndex.IsGenuine ι ∧
        ZetaPrimePowerIndex.center ι ≤ B :=
    (mem_zetaPrimeOffDiagonalSupportFinsetOfBound_iff f B ι).mp hι
  let hbox : ι ∈ ZetaPrimePowerIndex.box cutoff :=
    hcutoff ι hsupport.left hsupport.right
  (ZetaPrimePowerIndex.mem_window_iff_mem_box_and_isGenuine cutoff ι).mpr
    (And.intro hbox hsupport.left)

/-- The bounded off-diagonal support finset is eventually contained in every
sufficiently large genuine prime-power window. -/
theorem zetaPrimeOffDiagonalSupportFinsetOfBound_eventually_subset_window
    (f : ZetaAdmissibleFunction) (B : ℝ) :
    ∀ᶠ N in atTop,
      zetaPrimeOffDiagonalSupportFinsetOfBound f B ⊆
        ZetaPrimePowerIndex.window N :=
  match ZetaPrimePowerIndex.exists_box_bound_of_isGenuine_center_le B with
  | ⟨cutoff, hcutoff⟩ =>
      let hsubsetCutoff :
          zetaPrimeOffDiagonalSupportFinsetOfBound f B ⊆
            ZetaPrimePowerIndex.window cutoff :=
        zetaPrimeOffDiagonalSupportFinsetOfBound_subset_window_of_box_bound
          f B cutoff hcutoff
      Filter.eventually_atTop.2
        (Exists.intro cutoff
          fun N hcutoffLe =>
            fun ι hι =>
              ZetaPrimePowerIndex.window_mono hcutoffLe
                (hsubsetCutoff hι))

/-- Once a finite window contains the finite off-diagonal support, its
off-diagonal sum is the completed off-diagonal channel. -/
theorem zetaPrimeOffDiagonalChannel_eq_completed_of_supportFinset_subset_window
    (f : ZetaAdmissibleFunction) {B : ℝ}
    (hB : ∀ a ∈ tsupport (convolutionAutocorrelationKernel f), a ≤ B)
    (N : ℕ)
    (hsubset :
      zetaPrimeOffDiagonalSupportFinsetOfBound f B ⊆
        ZetaPrimePowerIndex.window N) :
    zetaPrimeOffDiagonalChannel N f = completedPrimeOffDiagonalChannel f :=
  let houtsideWindow :
      ∀ ι : ZetaPrimePowerIndex,
        ι ∉ ZetaPrimePowerIndex.window N →
          zetaPrimeOffDiagonalCoordinate ι f = 0 :=
    fun ι hιWindow =>
      let hιSupport :
          ι ∉ zetaPrimeOffDiagonalSupportFinsetOfBound f B :=
        fun hιSupport =>
          hιWindow (hsubset hιSupport)
      zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_mem_supportFinsetOfBound
        ι f hB hιSupport
  let hhasSum :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaPrimeOffDiagonalCoordinate ι f)
        (∑ ι in ZetaPrimePowerIndex.window N,
          zetaPrimeOffDiagonalCoordinate ι f) :=
    hasSum_sum_of_ne_finset_zero houtsideWindow
  let htsum :
      (∑' ι : ZetaPrimePowerIndex,
          zetaPrimeOffDiagonalCoordinate ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          zetaPrimeOffDiagonalCoordinate ι f :=
    hhasSum.tsum_eq
  let hwindow :
      zetaPrimeOffDiagonalChannel N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          zetaPrimeOffDiagonalCoordinate ι f :=
    Eq.refl (zetaPrimeOffDiagonalChannel N f)
  let hcompleted :
      completedPrimeOffDiagonalChannel f =
        ∑' ι : ZetaPrimePowerIndex,
          zetaPrimeOffDiagonalCoordinate ι f :=
    Eq.refl (completedPrimeOffDiagonalChannel f)
  hwindow.trans (htsum.symm.trans hcompleted.symm)

/-- Eventually the finite prime off-diagonal windows have stabilized to the
completed prime off-diagonal channel. -/
theorem zetaPrimeOffDiagonalChannel_eventually_eq_completed_source
    (f : ZetaAdmissibleFunction) :
    ∀ᶠ N in atTop,
      zetaPrimeOffDiagonalChannel N f = completedPrimeOffDiagonalChannel f :=
  match exists_convolutionAutocorrelationKernelSupportUpperBound f with
  | ⟨B, hB⟩ =>
      (zetaPrimeOffDiagonalSupportFinsetOfBound_eventually_subset_window
        f B).mono
        (fun N hsubset =>
          zetaPrimeOffDiagonalChannel_eq_completed_of_supportFinset_subset_window
            f hB N hsubset)

/-- Eventually the finite prime off-diagonal windows vanish. -/
theorem zetaPrimeOffDiagonalChannel_eventually_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ∀ᶠ N in atTop,
      zetaPrimeOffDiagonalChannel N f = 0 :=
  (zetaPrimeOffDiagonalChannel_eventually_eq_completed_source f).mono
    (fun N hN =>
      hN.trans
        (completedPrimeOffDiagonalChannel_eq_zero_ownerTraceReconstruction
          f D))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
