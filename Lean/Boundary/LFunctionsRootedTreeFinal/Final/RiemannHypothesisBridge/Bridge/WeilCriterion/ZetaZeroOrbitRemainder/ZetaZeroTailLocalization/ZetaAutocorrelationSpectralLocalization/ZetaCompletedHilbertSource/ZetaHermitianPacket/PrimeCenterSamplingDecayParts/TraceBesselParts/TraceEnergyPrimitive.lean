import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtBessel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime-center trace-energy primitive

This file owns the non-cyclic trace-energy reconstruction input for the
weighted completed prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite prime-center projection energy attached to a finite family of
prime-power sampling coordinates. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- The finite prime-center projection energy unfolds to the corresponding
finite weighted sampling sum. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f =
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
      s f)

/-- The completed prime-center trace-energy scalar for the weighted sampling
stream, owned as the supremum of its finite positive projection energies. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  sSup
    (Set.range
      (fun s : Finset ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f))

/-- Finite prime-center projection energies are nonnegative. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_nonnegative
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f :=
  Finset.sum_nonneg
    (fun index membership =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f)

/-- Finite prime-center projection energies are monotone under enlarging the
finite projection set. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_mono
    {s t : Finset ZetaPrimePowerIndex} (f : ZetaAdmissibleFunction)
    (hst : s ⊆ t) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        t f :=
  Finset.sum_le_sum_of_subset_of_nonneg
    hst
    (fun index tMembership outsideMembership =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f)

/-- The union of two finite prime-center projection sets dominates each
projection energy. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_le_union_left
    (s t : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        (s ∪ t) f :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_mono
    f
    (fun index membership =>
      Finset.mem_union.mpr (Or.inl membership))

/-- The union of two finite prime-center projection sets dominates the right
projection energy. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_le_union_right
    (s t : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        t f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        (s ∪ t) f :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_mono
    f
    (fun index membership =>
      Finset.mem_union.mpr (Or.inr membership))

/-- The positive-kernel remainder after removing a finite prime-center
projection energy from the completed prime-center trace energy. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy f -
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
      s f

/-- The finite projection complement energy unfolds to trace energy minus
finite projection energy. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_eq_traceEnergy_sub_projectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
        s f =
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy f -
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f :=
  Eq.refl
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
      s f)

/-- Nonnegativity of the finite projection complement is exactly the Bessel
domination of that finite projection by the completed trace energy. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_le_traceEnergy_of_projectionComplement_nonnegative
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hnonnegative :
      0 ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
          s f) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f :=
  let hsub :
      0 ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy f -
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_eq_traceEnergy_sub_projectionEnergy
        s f)
      hnonnegative
  sub_nonneg.mp hsub

/-- A scalar is an upper bound for all finite weighted prime-center projection
energies. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
      s f ≤ C

/-- A named finite-projection upper bound gives boundedness above of the
finite weighted prime-center projection-energy range. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_range_bddAbove_of_upperBound
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
        f C) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f)) :=
  let hupper :
      ∀ value : ℝ,
        value ∈
          Set.range
            (fun s : Finset ZetaPrimePowerIndex =>
              completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
                s f) →
        value ≤ C :=
    fun value hvalue =>
    match hvalue with
    | ⟨s, hvalue_eq⟩ =>
        Eq.subst
          (motive := fun projectionValue : ℝ => projectionValue ≤ C)
          hvalue_eq
          (hC s)
  Exists.intro C hupper

/-- A diagonal-debt real-coordinate owner `HasSum` gives the finite projection
upper-bound package for weighted completed prime-center sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
      f C :=
  fun s =>
  let hfinite :
      (∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) ≤ C :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum s
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
      s f).symm
    hfinite

/-- A diagonal-debt real-coordinate owner `HasSum` gives boundedness above of
the finite weighted prime-center projection-energy range. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_bddAbove_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f)) :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_range_bddAbove_of_upperBound
    f C
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum)

/-- The scalar is the least upper bound of all finite weighted prime-center
projection energies. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyLeastUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
      f C ∧
    ∀ B : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
        f B →
      C ≤ B

/-- Source uniform Bessel boundedness for the finite weighted prime-center
projection energies.  This is the analytic source theorem behind the
trace-energy supremum package. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
        f C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_owner_source
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      let hprojection :
          CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
            f C :=
        fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
            s f).symm
          (hC s)
      Exists.intro C hprojection

/-- Source Bessel boundedness for the finite weighted prime-center projection
energies, derived from the named uniform finite-projection source theorem. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_bddAbove_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f)) :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_source
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_range_bddAbove_of_upperBound
        f C hC

/-- The finite weighted prime-center projection-energy range is nonempty. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_range_nonempty
    (f : ZetaAdmissibleFunction) :
    (Set.range
      (fun s : Finset ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f)).Nonempty :=
  Set.range_nonempty
    (fun s : Finset ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f)

/-- The source Bessel bound makes the trace-energy supremum the least upper
bound of the finite weighted prime-center projection energies. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    IsLUB
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f))
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) :=
  isLUB_csSup
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_range_nonempty
      f)
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_bddAbove_source
      f C₀ k hbound)

/-- Source finite-projection exhaustion of the completed prime-center
trace-energy scalar. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_tendsto_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    Tendsto
      (fun s : Finset ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f)
      atTop
      (𝓝
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f)) :=
  let hmono :
      Monotone
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f) :=
    fun s t hst =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_mono
        f hst
  tendsto_atTop_isLUB
    hmono
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_source
      f C₀ k hbound)

/-- Finite-projection exhaustion identifies the trace-energy scalar as the
least upper bound of finite projection energies. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLeastUpperBound_projectionEnergy_of_tendsto
    (f : ZetaAdmissibleFunction)
    (htendsto :
      Tendsto
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f)
        atTop
        (𝓝
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f))) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyLeastUpperBound
      f
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) :=
  let projection :
      Finset ZetaPrimePowerIndex → ℝ :=
    fun s : Finset ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f
  let hmono : Monotone projection :=
    fun s t hst =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_mono
        f hst
  let htendstoProjection :
      Tendsto projection atTop
        (𝓝
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f)) :=
    htendsto
  let hIsLUB :
      IsLUB (Set.range projection)
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    isLUB_of_tendsto_atTop hmono htendstoProjection
  let hupper :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
        f
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    fun s =>
      hIsLUB.1 (Set.mem_range_self s)
  let hleast :
      ∀ B : ℝ,
        CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
          f B →
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f ≤ B :=
    fun B hB =>
    let hB_range :
        ∀ value : ℝ, value ∈ Set.range projection → value ≤ B :=
      fun value hvalue =>
      match hvalue with
      | ⟨s, hs⟩ =>
          Eq.subst
            (motive := fun x : ℝ => x ≤ B)
            hs
            (hB s)
    hIsLUB.2 hB_range
  And.intro hupper hleast

/-- Source supremum reconstruction for the completed prime-center trace-energy
scalar from its finite projection energies. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLeastUpperBound_projectionEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyLeastUpperBound
      f
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) :=
  let hIsLUB :
      IsLUB
        (Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
              s f))
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_source
      f C₀ k hbound
  let hupper :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
        f
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    fun s =>
      hIsLUB.1 (Set.mem_range_self s)
  let hleast :
      ∀ B : ℝ,
        CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
          f B →
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f ≤ B :=
    fun B hB =>
    let hB_range :
        ∀ value : ℝ,
          value ∈
            Set.range
              (fun s : Finset ZetaPrimePowerIndex =>
                completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
                  s f) →
          value ≤ B :=
      fun value hvalue =>
      match hvalue with
      | ⟨s, hs⟩ =>
          Eq.subst
            (motive := fun x : ℝ => x ≤ B)
            hs
            (hB s)
    hIsLUB.2 hB_range
  And.intro hupper hleast

/-- The source supremum reconstruction gives the upper-bound half used by
Bessel domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_upperBound_projectionEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound
      f
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) :=
  (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLeastUpperBound_projectionEnergy_source
    f C₀ k hbound).left

/-- Source trace-energy upper-bound theorem for every finite prime-center
projection. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_le_traceEnergy_source
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_upperBound_projectionEnergy_source
    f C₀ k hbound s

/-- Domination of a finite prime-center projection by trace energy gives
nonnegativity of the corresponding positive-kernel complement. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_nonnegative_of_projectionEnergy_le_traceEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hbound :
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :
    0 ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
        s f :=
  let hsub :
      0 ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy f -
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
            s f :=
    sub_nonneg.mpr hbound
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_eq_traceEnergy_sub_projectionEnergy
      s f).symm
    hsub

/-- Source positive-kernel nonnegativity for every finite prime-center
projection complement. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_nonnegative_source
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    0 ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy
        s f :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionComplementEnergy_nonnegative_of_projectionEnergy_le_traceEnergy
    s f
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_le_traceEnergy_source
      s f C₀ k hbound)

/-- Bessel domination for the weighted completed prime-center sampling stream:
all finite positive sampling shadows are bounded by one scalar. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
    (f : ZetaAdmissibleFunction) :
    Prop :=
  ∃ C : ℝ,
    ∀ s : Finset ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
        s f ≤ C

/-- A diagonal-debt real-coordinate owner `HasSum` gives Bessel domination for
the weighted completed prime-center sampling projection stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
      f :=
  Exists.intro C
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum)

/-- Source Bessel domination for the weighted completed prime-center sampling
stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_primitive
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
      f :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_source
    f C₀ k hbound

/-- Source finite-subtrace Bessel domination for the weighted completed
prime-center sampling stream.

This is the analytic owner primitive: every finite positive sampling shadow is
uniformly bounded by one trace-energy constant, independently of the window,
box, and finite-subtrace wrappers that consume it. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_primitive
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_primitive
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      let hsum :
          ∀ s : Finset ZetaPrimePowerIndex,
            ∑ index in s,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ C :=
        fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
            s f)
          (hC s)
      Exists.intro C hsum

/-- A diagonal-debt real-coordinate owner `HasSum` gives finite-subtrace
Bessel domination for the weighted completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_source_primitive
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ B :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum with
  | ⟨B, hB⟩ =>
      let hsum :
          ∀ s : Finset ZetaPrimePowerIndex,
            ∑ index in s,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ B :=
        fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ B)
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
            s f)
          (hB s)
      Exists.intro B hsum

/-- Finite-subtrace Bessel domination gives summability of the weighted
completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source_primitive
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    fun index =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_primitive
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      summable_of_sum_le hnonnegative hC

/-- Source trace-energy `HasSum` reconstruction for the weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) :=
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    fun index =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  let hIsLUBProjection :
      IsLUB
        (Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
              s f))
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_isLUB_projectionEnergy_source
      f C₀ k hbound
  let hprojection_eq_sum :
      (fun s : Finset ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy
          s f) =
      (fun s : Finset ZetaPrimePowerIndex =>
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f) :=
    funext
      (fun s =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum
          s f)
  let hIsLUBFiniteSum :
      IsLUB
        (Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            ∑ index in s,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f))
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    Eq.subst
      (motive :=
        fun projection : Finset ZetaPrimePowerIndex → ℝ =>
          IsLUB
            (Set.range projection)
            (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
              f))
      hprojection_eq_sum
      hIsLUBProjection
  hasSum_of_isLUB_of_nonneg
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
      f)
    hnonnegative
    hIsLUBFiniteSum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
