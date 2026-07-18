import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.Prelude

namespace Boundary
namespace LFunctions
noncomputable section

open Real Complex

/-- A nontrivial centered zeta zero that is off the critical centered line. -/
structure OffCriticalCenteredZetaZero where
  point : ℂ
  zeta_zero : riemannZeta (1 / 2 + point) = 0
  nontrivial : ¬ ∃ n : ℕ, 1 / 2 + point = -2 * (n + 1)
  not_pole : (1 / 2 + point) ≠ 1
  offCritical : point.re ≠ 0

/-- The point carried by an off-critical centered zero is off the centered critical line. -/
theorem OffCriticalCenteredZetaZero.point_re_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    z.point.re ≠ 0 :=
  z.offCritical

/-- The point carried by an off-critical centered zero is a nontrivial centered zero. -/
theorem OffCriticalCenteredZetaZero.point_zeta_zero
    (z : OffCriticalCenteredZetaZero) :
    riemannZeta (1 / 2 + z.point) = 0 :=
  z.zeta_zero

/-! The tail-smallness premise is shared by every off-critical separation
theorem below. Naming it here keeps the public signatures focused on the
zero-orbit data while preserving the full Runge/fiber hypothesis. -/
def ZeroTailSmallValuesOwnerRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉
            ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈
          ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
            S P f₀ ∧
          r < ε

/-- The shifted coordinate of an off-critical centered zero avoids the completed
normalization singularity. -/
theorem offCriticalCenteredZero_shift_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    (1 / 2 : ℂ) + z.point ≠ 0 := by
  intro hzero
  have hzeta_at_zero : riemannZeta (0 : ℂ) = 0 := by
    calc
      riemannZeta (0 : ℂ) =
          riemannZeta ((1 / 2 : ℂ) + z.point) := by
        exact congrArg riemannZeta hzero.symm
      _ = 0 := z.zeta_zero
  exact riemannZeta_zero_ne_zero hzeta_at_zero

/-- Casting a natural successor into the complex field as `↑n + 1`, explicitly. -/
theorem complex_natCast_add_one_eq_natCast_add_one (n : ℕ) :
    (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
  have hone : (((1 : ℕ) : ℂ)) = 1 :=
    Nat.cast_one
  have hadd : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + ((1 : ℕ) : ℂ) :=
    Nat.cast_add n 1
  exact hadd.trans (congrArg (fun x : ℂ => (n : ℂ) + x) hone)

/-- The completed Gamma factor is nonzero at a nontrivial centered zeta zero. -/
theorem offCriticalCenteredZero_gamma_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    Complex.Gammaℝ ((1 / 2 : ℂ) + z.point) ≠ 0 := by
  have hnot_negative_even :
      ¬ ∃ n : ℕ,
        (1 / 2 : ℂ) + z.point = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
    intro hnegative
    exact
      match hnegative with
      | ⟨n, hn⟩ =>
          z.nontrivial
            ⟨n,
              hn.trans
                (congrArg
                  (fun x : ℂ => (-2 : ℂ) * x)
                  (complex_natCast_add_one_eq_natCast_add_one n))⟩
  exact Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    (offCriticalCenteredZero_shift_ne_zero z)
    hnot_negative_even

/-- An off-critical centered ordinary zeta zero is a centered completed-zeta zero. -/
theorem offCriticalCenteredZero_completedZero
    (z : OffCriticalCenteredZetaZero) :
    ZetaCompletedZero z.point := by
  exact zetaCompletedZero_mk
    (fun hpoint =>
      offCriticalCenteredZero_shift_ne_zero z
      (by
        calc
          (1 / 2 : ℂ) + z.point =
              (1 / 2 : ℂ) + (-(1 / 2 : ℂ)) := by
            exact congrArg (fun w : ℂ => (1 / 2 : ℂ) + w) hpoint
          _ = 0 := add_neg_cancel (1 / 2 : ℂ)))
    (fun hpoint =>
      z.not_pole
      (by
        calc
          (1 / 2 : ℂ) + z.point =
              (1 / 2 : ℂ) + (1 / 2 : ℂ) := by
            exact congrArg (fun w : ℂ => (1 / 2 : ℂ) + w) hpoint
          _ = 1 := by
            exact add_halves (1 : ℂ)))
    ((centeredCompletedRiemannZetaFunction_eq z.point).trans
      (centeredCompletedRiemannZeta_eq_zero_of_riemannZeta_eq_zero
        (offCriticalCenteredZero_shift_ne_zero z)
        (offCriticalCenteredZero_gamma_ne_zero z)
        z.zeta_zero))

/-- The centered reflection orbit of an off-critical centered zero lies in the centered
completed-zero locus. -/
theorem offCriticalCenteredZero_orbit_completedZero
    (z : OffCriticalCenteredZetaZero) :
    ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η := by
  intro η hη
  have hcompleted : ZetaCompletedZero z.point :=
    offCriticalCenteredZero_completedZero z
  have hfaces : η = z.point ∨ η = -z.point :=
    (zetaZeroOrbitFinset_mem_iff z.point η).1 hη
  exact
    match hfaces with
    | Or.inl hpos =>
        Eq.subst (motive := fun w : ℂ => ZetaCompletedZero w) hpos.symm hcompleted
    | Or.inr hneg =>
        have hnegzero : ZetaCompletedZero (-z.point) :=
          zetaCompletedZero_neg hcompleted
        Eq.subst (motive := fun w : ℂ => ZetaCompletedZero w) hneg.symm hnegzero

/-- An off-critical centered Riemann-zeta zero is a centered completed-zeta zero, and its
functional-equation orbit remains in the centered completed zero locus. -/
theorem offCriticalCenteredZero_completedZero_and_orbit
    (z : OffCriticalCenteredZetaZero) :
    ZetaCompletedZero z.point ∧
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η := by
  exact ⟨offCriticalCenteredZero_completedZero z,
    offCriticalCenteredZero_orbit_completedZero z⟩

/-- Zero-side separation for an off-critical centered zeta zero.

This is the real analytic separation step in Weil's criterion: an off-critical centered
zero produces an admissible autocorrelation seed whose zero-side quadratic form is negative. -/
theorem exists_negative_zeroSide_autocorrelation_of_offCriticalCenteredZero
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (z : OffCriticalCenteredZetaZero) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  exact
    exists_negative_completedZeroSide_autocorrelation_of_daggerClosedOrbitWindow
      hZeroTailSmallValuesOwnerRunge
      hbranch
      hpartialOneTwo
      hcompactOneTwo
      hfinite
      hpartialLeft
      hcompactBoundary
      z.point
      (offCriticalCenteredZero_completedZero z)

/-- The zero-detecting direction of Weil's criterion.

An off-critical nontrivial centered zero can be separated by an admissible
autocorrelation seed whose completed Weil quadratic form is strictly negative.
This theorem is now only the Weil-form transport of the zero-side separation theorem above. -/
theorem exists_negative_autocorrelation_quadraticForm_of_offCriticalCenteredZero
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (z : OffCriticalCenteredZetaZero) :
    ∃ f : ZetaAdmissibleFunction,
      zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  exact
    match exists_negative_zeroSide_autocorrelation_of_offCriticalCenteredZero
        hZeroTailSmallValuesOwnerRunge
        hbranch
        hpartialOneTwo hcompactOneTwo
        hfinite
        hpartialLeft hcompactBoundary z with
    | ⟨f, hf⟩ =>
        ⟨f,
          calc
            zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
                zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
              exact zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f
            _ < 0 := hf⟩

/-- Parameter-facing wrapper for the zero-detecting direction of Weil's criterion. -/
theorem exists_negative_autocorrelation_quadraticForm_of_offCritical_centeredZero
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (s : ℂ)
    (hz : riemannZeta (1 / 2 + s) = 0)
    (htriv : ¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1))
    (hpole : (1 / 2 + s) ≠ 1)
    (hoff : s.re ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  exact exists_negative_autocorrelation_quadraticForm_of_offCriticalCenteredZero
    hZeroTailSmallValuesOwnerRunge
    hbranch
    hpartialOneTwo hcompactOneTwo
    hfinite
    hpartialLeft hcompactBoundary
    ⟨s, hz, htriv, hpole, hoff⟩

/-- Quadratic Weil positivity excludes off-critical nontrivial centered zeros. -/
theorem not_offCritical_centeredZero_of_zetaWeilQuadraticPositivity
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (h : ZetaWeilQuadraticPositivity)
    (s : ℂ)
    (hz : riemannZeta (1 / 2 + s) = 0)
    (htriv : ¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1))
    (hpole : (1 / 2 + s) ≠ 1) :
    ¬ s.re ≠ 0 := by
  intro hoff
  exact
    match exists_negative_autocorrelation_quadraticForm_of_offCritical_centeredZero
        hZeroTailSmallValuesOwnerRunge
        hbranch
        hpartialOneTwo hcompactOneTwo
        hfinite
        hpartialLeft hcompactBoundary
        s hz htriv hpole hoff with
    | ⟨f, hfneg⟩ =>
        (not_lt_of_ge (h f)) hfneg

/-- Real trichotomy turns exclusion of the off-critical condition into equality with the
centered critical line, without using double-negation elimination. -/
theorem real_eq_zero_of_not_ne_zero
    (x : ℝ) (hnot : ¬ x ≠ 0) :
    x = 0 := by
  exact
    match lt_trichotomy x 0 with
    | Or.inl hxlt =>
        False.elim (hnot (ne_of_lt hxlt))
    | Or.inr (Or.inl hxeq) =>
        hxeq
    | Or.inr (Or.inr hxgt) =>
        False.elim (hnot (Ne.symm (ne_of_lt hxgt)))

/-- Quadratic Weil positivity gives the centered zero criterion.

This is the standard Weil-criterion formalization point: once the completed Weil quadratic
form is nonnegative on all autocorrelation seeds, every nontrivial centered zero lies on the
critical line. -/
theorem centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (h : ZetaWeilQuadraticPositivity) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 := by
  intro s hz htriv hpole
  exact real_eq_zero_of_not_ne_zero s.re
    (not_offCritical_centeredZero_of_zetaWeilQuadraticPositivity
      hZeroTailSmallValuesOwnerRunge
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary
      h s hz htriv hpole)

/-- The standard Weil criterion in the quadratic/autocorrelation form. -/
theorem boundaryRiemannHypothesis_of_zetaWeilQuadraticPositivity
    (hZeroTailSmallValuesOwnerRunge : ZeroTailSmallValuesOwnerRunge)
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (h : ZetaWeilQuadraticPositivity) :
    boundaryRiemannHypothesis := by
  exact boundaryRiemannHypothesis_of_centeredZeroCriterion
    (centeredZeroCriterion_of_zetaWeilQuadraticPositivity
      hZeroTailSmallValuesOwnerRunge
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary h)

end
end LFunctions
end Boundary
