import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.ProjectionEnergyCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.PositiveSampleWindowBessel
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed prime-center Hilbert-frame Bessel bound

This file owns the analytic Bessel theorem for finite projections of the
completed weighted prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- A positive sample norm-square window upper bound gives a weighted
prime-center window projection upper bound. -/
theorem completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_of_positiveSampleNormSqWindow_upperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hsample :
      ∃ C : ℝ,
        ∀ N : ℕ,
          (∑ index in ZetaPrimePowerIndex.window N,
            zetaCompletedPrimePositiveWeightedSampleNormSq index f) ≤ C) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
          N f ≤ C :=
  match hsample with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun N : ℕ =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ C)
            (completedWeightedPrimeSamplingWindowProjectionEnergy_eq_positiveSampleNormSqWindow_hilbertFrame
              N f).symm
            (hC N)⟩

/-- Genuine-window projection energies for completed weighted prime-center
sampling are uniformly bounded. -/
theorem completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
          N f ≤ C :=
  completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_of_positiveSampleNormSqWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
          N f ≤ C :=
  completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_of_positiveSampleNormSqWindow_upperBound_hilbertFrame
    f
    (zetaCompletedPrimePositiveWeightedSampleNormSq_window_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- A genuine-window upper bound gives a rectangular-box upper bound. -/
theorem completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_of_windowProjectionEnergy_upperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hwindow :
      ∃ C : ℝ,
        ∀ N : ℕ,
          completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
            N f ≤ C) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f ≤ C :=
  match hwindow with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun N : ℕ =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ C)
            (completedWeightedPrimeSamplingBoxProjectionEnergy_eq_windowProjectionEnergy_hilbertFrame
              N f).symm
            (hC N)⟩

/-- Rectangular-box projection energies for completed weighted prime-center
sampling are uniformly bounded. -/
theorem completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f ≤ C :=
  completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_of_windowProjectionEnergy_upperBound_hilbertFrame
    f
    (completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f ≤ C :=
  completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_of_windowProjectionEnergy_upperBound_hilbertFrame
    f
    (completedWeightedPrimeSamplingWindowProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- A rectangular-box upper bound gives a finite projection-energy upper
bound. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_boxProjectionEnergy_upperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hbox :
      ∃ C : ℝ,
        ∀ N : ℕ,
          completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame
            N f ≤ C) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C :=
  match hbox with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
        match
          completedWeightedPrimeSamplingProjectionEnergy_le_boxProjectionEnergy_hilbertFrame
            s f with
        | ⟨N, hsN⟩ =>
            le_trans hsN (hC N)⟩

theorem completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C :=
  completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_boxProjectionEnergy_upperBound_hilbertFrame
    f
    (completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- A scalar upper-bounds all finite completed weighted prime-center projection
energies. -/
def CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C

/-- Hilbert-frame Bessel domination for the completed weighted prime-center
sampling projection stream. -/
def CompletedWeightedPrimeSamplingHilbertFrameBesselBound_source
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
      f C

/-- A diagonal-debt real-coordinate `HasSum` gives the finite Hilbert-frame
Bessel upper-bound package for completed weighted prime-center projections. -/
theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_of_diagonalDebtCoordinate_re_hasSum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    CompletedWeightedPrimeSamplingHilbertFrameBesselBound_source f :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_exists_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum with
  | ⟨B, hB⟩ =>
      ⟨B,
        fun s : Finset ZetaPrimePowerIndex =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ B)
            (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
              s f).symm
            (hB s)⟩

/-- Positive-kernel split for every finite completed weighted prime-center
projection energy. -/
def CompletedWeightedPrimeSamplingFinitePositiveKernelSplit_source
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ R : ℝ,
        C = completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f + R ∧
          0 ≤ R

/-- The finite positive-kernel complement after removing one finite
prime-center projection from a proposed trace scalar. -/
noncomputable def completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
    (C : ℝ) (s : Finset ZetaPrimePowerIndex)
    (f : ZetaAdmissibleFunction) : ℝ :=
  C - completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f

/-- The finite positive-kernel complement unfolds to trace scalar minus finite
projection energy. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplement_eq_sub_source
    (C : ℝ) (s : Finset ZetaPrimePowerIndex)
    (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingFinitePositiveKernelComplement_source C s f =
      C - completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f :=
  Eq.refl
    (completedWeightedPrimeSamplingFinitePositiveKernelComplement_source C s f)

/-- A scalar is its finite projection plus the corresponding subtraction
complement. -/
theorem completedWeightedPrimeSampling_traceScalar_eq_projection_add_sub_complement
    (C P : ℝ) :
    C = P + (C - P) :=
  let hstep1 :
        P + (C - P) = P + (C + -P) :=
    congrArg
      (fun value : ℝ => P + value)
      (sub_eq_add_neg C P)
  let hstep2 :
      P + (C + -P) = (P + C) + -P :=
    (add_assoc P C (-P)).symm
  let hstep3 :
      (P + C) + -P = (C + P) + -P :=
    congrArg
      (fun value : ℝ => value + -P)
      (add_comm P C)
  let hstep4 :
      (C + P) + -P = C + (P + -P) :=
    add_assoc C P (-P)
  let hstep5 :
      C + (P + -P) = C + 0 :=
    congrArg
      (fun value : ℝ => C + value)
      (add_neg_cancel P)
  let hstep6 :
      C + 0 = C :=
    add_zero C
  let hright : P + (C - P) = C :=
    hstep1.trans
      (hstep2.trans
        (hstep3.trans
          (hstep4.trans
            (hstep5.trans hstep6))))
  hright.symm

/-- Nonnegativity of all finite positive-kernel complements for one trace
scalar. -/
def CompletedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    0 ≤ completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
      C s f

/-- A finite-window positive-kernel complement frame records the existence of a
complement term, its subtraction identity, and its nonnegativity. -/
def CompletedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (s : Finset ZetaPrimePowerIndex) : Prop :=
  ∃ complement : ℝ,
    complement =
      completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
        C s f ∧
    C =
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f +
        complement ∧
    0 ≤ complement

/-- The finite completed weighted prime-center projection-energy range is
bounded above at the Hilbert-frame owner level. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_range_bddAbove_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
            s f)) :=
  match
    completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_boxProjectionEnergy_upperBound_hilbertFrame
      f
      (completedWeightedPrimeSamplingBoxProjectionEnergy_upperBound_hilbertFrame_source
        f Cpos Cneg kpos kneg hpos hneg) with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun value hvalue =>
          match hvalue with
          | ⟨s, hs⟩ => hs ▸ hC s⟩

/-- A bounded finite projection-energy range gives a concrete trace-scalar
upper-bound package. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_range_bddAbove_hilbertFrame_source
    (f : ZetaAdmissibleFunction)
    (hbounded :
      BddAbove
        (Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
              s f))) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C :=
  match hbounded with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
          hC (Set.mem_range_self s)⟩

/-- Analytic trace-scalar domination of all finite completed weighted
prime-center projection energies. -/
theorem completedWeightedPrimeSamplingPositiveKernelTraceScalar_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C :=
  completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_range_bddAbove_hilbertFrame_source
    f
    (completedWeightedPrimeSamplingProjectionEnergy_range_bddAbove_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- A trace scalar dominating a finite projection has a nonnegative subtraction
complement. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplement_nonnegative_of_upperBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (s : Finset ZetaPrimePowerIndex)
    (hupper :
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C) :
    0 ≤
      completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
        C s f :=
  let hle :
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C :=
    hupper s
  let hsub :
      0 ≤ C - completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f :=
    sub_nonneg.mpr hle
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeightedPrimeSamplingFinitePositiveKernelComplement_eq_sub_source
      C s f).symm
    hsub

/-- A trace scalar dominating finite projections constructs the finite-window
positive-kernel complement frame. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_of_upperBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (s : Finset ZetaPrimePowerIndex)
    (hupper :
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C) :
    CompletedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
      f C s :=
  let R : ℝ :=
    completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
      C s f
  let hR_eq :
      R =
        completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
          C s f :=
    Eq.refl R
  let hR_nonnegative : 0 ≤ R :=
    completedWeightedPrimeSamplingFinitePositiveKernelComplement_nonnegative_of_upperBound_source
      f C s hupper
  let hR_sub :
      R =
        C - completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f :=
    Eq.trans hR_eq
      (completedWeightedPrimeSamplingFinitePositiveKernelComplement_eq_sub_source
        C s f)
  let hsplit :
      C =
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f +
          R :=
    let P : ℝ :=
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f
    let hbase : C = P + (C - P) :=
      completedWeightedPrimeSampling_traceScalar_eq_projection_add_sub_complement
        C P
    Eq.trans hbase
      (congrArg
        (fun value : ℝ => P + value)
        hR_sub.symm)
  ⟨R, hR_eq, hsplit, hR_nonnegative⟩

/-- Hilbert positive-kernel construction for the completed weighted
prime-center sampling complement frames. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        CompletedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
          f C s :=
  match completedWeightedPrimeSamplingPositiveKernelTraceScalar_source
      f Cpos Cneg kpos kneg hpos hneg with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_of_upperBound_source
            f C s hC⟩

/-- A finite-window positive-kernel complement frame gives pointwise complement
nonnegativity. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplement_nonnegative_of_frame_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (s : Finset ZetaPrimePowerIndex)
    (hframe :
      CompletedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
        f C s) :
    0 ≤
      completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
        C s f :=
  match hframe with
  | ⟨R, hR⟩ =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hR.left
        hR.right.right

/-- Positive-kernel complement frames give one trace scalar whose finite
complements are all nonnegative. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_of_frame_source
    (f : ZetaAdmissibleFunction)
    (hframes :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          CompletedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
            f C s) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
        f C :=
  match hframes with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingFinitePositiveKernelComplement_nonnegative_of_frame_source
            f C s (hC s)⟩

/-- Source existence of a nonnegative finite positive-kernel complement for
completed weighted prime-center projections. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
        f C :=
  completedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_of_frame_source
    f
    (completedWeightedPrimeSamplingFinitePositiveKernelComplementFrame_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- Nonnegative finite complements give the explicit positive-kernel split. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelSplit_of_complementNonnegative_source
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      ∃ C : ℝ,
        CompletedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
          f C) :
    CompletedWeightedPrimeSamplingFinitePositiveKernelSplit_source f :=
  match hcomplement with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
        let R : ℝ :=
          completedWeightedPrimeSamplingFinitePositiveKernelComplement_source
            C s f
        let hR_nonnegative : 0 ≤ R := hC s
        let hR_eq :
            R =
              C - completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
                s f :=
          completedWeightedPrimeSamplingFinitePositiveKernelComplement_eq_sub_source
            C s f
        let hsplitC :
            C =
              completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f +
                R :=
          let P : ℝ :=
            completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f
          let hbase : C = P + (C - P) :=
            completedWeightedPrimeSampling_traceScalar_eq_projection_add_sub_complement
              C P
          Eq.trans hbase
            (congrArg
              (fun value : ℝ => P + value)
              hR_eq.symm)
        ⟨R, hsplitC, hR_nonnegative⟩⟩

/-- Source positive-kernel split for finite completed weighted prime-center
projection energies. -/
theorem completedWeightedPrimeSamplingFinitePositiveKernelSplit_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedWeightedPrimeSamplingFinitePositiveKernelSplit_source f :=
  completedWeightedPrimeSamplingFinitePositiveKernelSplit_of_complementNonnegative_source
    f
    (completedWeightedPrimeSamplingFinitePositiveKernelComplementNonnegative_source
      f Cpos Cneg kpos kneg hpos hneg)

/-- A positive-kernel split gives the Hilbert-frame Bessel upper bound. -/
theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_of_positiveKernelSplit_source
    (f : ZetaAdmissibleFunction)
    (hsplit :
      CompletedWeightedPrimeSamplingFinitePositiveKernelSplit_source f) :
    CompletedWeightedPrimeSamplingHilbertFrameBesselBound_source f :=
  match hsplit with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun s : Finset ZetaPrimePowerIndex =>
        match hC s with
        | ⟨R, hR⟩ =>
            let hnonnegative : 0 ≤ R := hR.right
            let hle :
                completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
                  completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f + R :=
              le_add_of_nonneg_right hnonnegative
            Eq.subst
              (motive := fun value : ℝ =>
                completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
                  value)
              hR.left.symm
              hle⟩

/-- Source Hilbert-frame Bessel domination for completed weighted prime-center
sampling. -/
theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedWeightedPrimeSamplingHilbertFrameBesselBound_source f :=
  completedWeightedPrimeSamplingHilbertFrameBesselBound_of_positiveKernelSplit_source
    f
    (completedWeightedPrimeSamplingFinitePositiveKernelSplit_source
      f Cpos Cneg kpos kneg hpos hneg)

theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_of_spectralPolynomialBounds_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedWeightedPrimeSamplingHilbertFrameBesselBound_source f :=
  match
    completedWeightedPrimeSamplingProjectionEnergy_upperBound_of_spectralPolynomialBounds_hilbertFrame_source
      f Cpos Cneg kpos kneg hpos hneg with
  | ⟨C, hC⟩ =>
      ⟨C, hC⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
