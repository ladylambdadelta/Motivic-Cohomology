import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.ZetaExplicitFormulaGeometry
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaPuncturedPlane.ZetaExplicitFormulaPuncturedPlane
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.ZetaAdmissibleTransformRegularity
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.ZetaCompletedLogDerivativeControl
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.OrderClosed

/-!
# Boundary explicit-formula analytic package data

This file owns the combined analytic package records used by the completed-zeta
explicit-formula contour argument.  The records are data, not propositions:
they package transform control, completed-log-derivative control, and contour
geometry for downstream theorem wrappers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed-zeta singular predicate relevant to the finite-rectangle residue theorem:
the poles at `0` and `1`, the Gamma-normalization zeros used by the completed and
archimedean channels, and the zeros of the completed zeta factor away from those poles. -/
def explicitFormulaContourSingularPoint (z : ℂ) : Prop :=
  z = 0 ∨ z = 1 ∨ Gammaℝ z = 0 ∨ Gammaℝ (z / 2) = 0 ∨
    (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)

/-- The boundary of the rectangle at height `T` for a contour family. -/
def explicitFormulaContourFamilyBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) : Set ℂ :=
  {z : ℂ |
    (∃ t : ℝ,
        t ∈ Set.Icc (-T) T ∧
          z = zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) ∨
      (∃ t : ℝ,
        t ∈ Set.Icc (-T) T ∧
          z = zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) ∨
      (∃ x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z = zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) ∨
      (∃ x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z = zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)}

/-- The vertical sides of a contour family avoid completed-zeta singularities at height `T`. -/
def explicitFormulaContourFamilyVerticalAvoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) : Prop :=
  ∀ z : ℂ,
    explicitFormulaContourSingularPoint z →
      ((∃ t : ℝ,
        t ∈ Set.Icc (-T) T ∧
          z = zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) ∨
       (∃ t : ℝ,
        t ∈ Set.Icc (-T) T ∧
          z = zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)) →
        False

/-- The horizontal sides of a contour family avoid completed-zeta singularities at height
`T`. -/
def explicitFormulaContourFamilyHorizontalAvoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) : Prop :=
  ∀ z : ℂ,
    explicitFormulaContourSingularPoint z →
      ((∃ x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z = zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) ∨
       (∃ x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z = zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) →
        False

/-- A height avoids all completed-zeta singularities on the rectangle boundary. -/
def explicitFormulaContourFamilyAvoidsSingularBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) : Prop :=
  ∀ z : ℂ,
    explicitFormulaContourSingularPoint z →
      z ∈ explicitFormulaContourFamilyBoundary F T →
        False

/-- Full boundary avoidance is vertical avoidance plus horizontal avoidance. -/
theorem explicitFormulaContourFamilyAvoidsSingularBoundary_of_vertical_horizontal
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hvertical : explicitFormulaContourFamilyVerticalAvoidsSingularBoundary F T)
    (hhorizontal : explicitFormulaContourFamilyHorizontalAvoidsSingularBoundary F T) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F T := by
  intro z hz hboundary
  rcases hboundary with hright | hleft | htop | hbottom
  · exact hvertical z hz (Or.inl hright)
  · exact hvertical z hz (Or.inr hleft)
  · exact hhorizontal z hz (Or.inl htop)
  · exact hhorizontal z hz (Or.inr hbottom)

/-- The completed `Gammaℝ` zero locus is countable. -/
theorem Gammaℝ_zeroSet_countable :
    ({z : ℂ | Gammaℝ z = 0} : Set ℂ).Countable := by
  have hsubset :
      ({z : ℂ | Gammaℝ z = 0} : Set ℂ) ⊆
        Set.range (fun n : ℕ => (-(2 * n : ℕ) : ℂ)) := by
    intro z hz
    rcases Complex.Gammaℝ_eq_zero_iff.mp hz with ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  exact (Set.countable_range (fun n : ℕ => (-(2 * n : ℕ) : ℂ))).mono hsubset

/-- Division by two is injective on complex numbers. -/
theorem complex_div_two_injective : Function.Injective (fun z : ℂ => z / 2) := by
  intro z w hzw
  have hmul : z / 2 * 2 = w / 2 * 2 := by
    exact congrArg (fun u : ℂ => u * 2) hzw
  calc
    z = z / 2 * 2 := by
      exact (div_mul_cancel₀ z (two_ne_zero : (2 : ℂ) ≠ 0)).symm
    _ = w / 2 * 2 := hmul
    _ = w := by
      exact div_mul_cancel₀ w (two_ne_zero : (2 : ℂ) ≠ 0)

/-- The `z ↦ Gammaℝ (z / 2)` zero locus is countable. -/
theorem Gammaℝ_half_zeroSet_countable :
    ({z : ℂ | Gammaℝ (z / 2) = 0} : Set ℂ).Countable := by
  exact Gammaℝ_zeroSet_countable.preimage complex_div_two_injective

/-- The completed-zeta contour singular set is countable. -/
theorem explicitFormulaContourSingularPoint_countable :
    ({z : ℂ | explicitFormulaContourSingularPoint z} : Set ℂ).Countable := by
  have h0 : ({z : ℂ | z = 0} : Set ℂ).Countable :=
    Set.countable_singleton (0 : ℂ)
  have h1 : ({z : ℂ | z = 1} : Set ℂ).Countable :=
    Set.countable_singleton (1 : ℂ)
  have hGamma : ({z : ℂ | Gammaℝ z = 0} : Set ℂ).Countable :=
    Gammaℝ_zeroSet_countable
  have hGammaHalf : ({z : ℂ | Gammaℝ (z / 2) = 0} : Set ℂ).Countable :=
    Gammaℝ_half_zeroSet_countable
  have hzeta :
      ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} :
        Set ℂ).Countable :=
    completedRiemannZeta_nontrivialZeroSet_countable
  have hunion :
      (({z : ℂ | z = 0} : Set ℂ) ∪
        (({z : ℂ | z = 1} : Set ℂ) ∪
          (({z : ℂ | Gammaℝ z = 0} : Set ℂ) ∪
            (({z : ℂ | Gammaℝ (z / 2) = 0} : Set ℂ) ∪
              ({z : ℂ | z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0} :
                Set ℂ))))).Countable :=
    h0.union (h1.union (hGamma.union (hGammaHalf.union hzeta)))
  exact hunion.mono
    (fun z hz =>
      match hz with
      | Or.inl hz0 => Or.inl hz0
      | Or.inr (Or.inl hz1) => Or.inr (Or.inl hz1)
      | Or.inr (Or.inr (Or.inl hΓ)) => Or.inr (Or.inr (Or.inl hΓ))
      | Or.inr (Or.inr (Or.inr (Or.inl hΓhalf))) =>
          Or.inr (Or.inr (Or.inr (Or.inl hΓhalf)))
      | Or.inr (Or.inr (Or.inr (Or.inr hzeta))) =>
          Or.inr (Or.inr (Or.inr (Or.inr hzeta))))

/-- A horizontal over-approximation of bad heights: top hits have height `z.im` and bottom
hits have height `-z.im`. -/
def explicitFormulaContourHorizontalBadHeightSet
    (_F : ExplicitFormulaContourFamily) : Set ℝ :=
  (fun z : ℂ => z.im) '' ({z : ℂ | explicitFormulaContourSingularPoint z} : Set ℂ) ∪
    (fun z : ℂ => -z.im) ''
      ({z : ℂ | explicitFormulaContourSingularPoint z} : Set ℂ)

/-- The horizontal bad-height set is countable. -/
theorem explicitFormulaContourHorizontalBadHeightSet_countable
    (F : ExplicitFormulaContourFamily) :
    (explicitFormulaContourHorizontalBadHeightSet F).Countable := by
  exact
    (explicitFormulaContourSingularPoint_countable.image (fun z : ℂ => z.im)).union
      (explicitFormulaContourSingularPoint_countable.image (fun z : ℂ => -z.im))

/-- Avoiding the horizontal bad-height set gives horizontal boundary avoidance. -/
theorem explicitFormulaContourFamilyHorizontalAvoidsSingularBoundary_of_not_mem_horizontalBadHeightSet
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hT : T ∉ explicitFormulaContourHorizontalBadHeightSet F) :
    explicitFormulaContourFamilyHorizontalAvoidsSingularBoundary F T := by
  intro z hz hhit
  rcases hhit with htop | hbottom
  · rcases htop with ⟨x, _hx, hzpath⟩
    have him : T = z.im := by
      calc
        T = (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im := by
          exact (zetaCompletedExplicitFormulaTopPath_im (F.rectangle T) x).symm
        _ = z.im := by
          exact congrArg Complex.im hzpath.symm
    exact hT (Or.inl ⟨z, hz, him.symm⟩)
  · rcases hbottom with ⟨x, _hx, hzpath⟩
    have him : T = -z.im := by
      calc
        T = -((zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im) := by
          exact
            (congrArg Neg.neg
              (zetaCompletedExplicitFormulaBottomPath_im (F.rectangle T) x)).trans
              (neg_neg T)
        _ = -z.im := by
          exact congrArg Neg.neg (congrArg Complex.im hzpath.symm)
    exact hT (Or.inr ⟨z, hz, him.symm⟩)

/-- A contour family with vertical singularities already excluded. -/
structure ExplicitFormulaVerticallyRegularContourFamily where
  toContourFamily : ExplicitFormulaContourFamily
  vertical_avoids :
    ∀ T : ℝ,
      explicitFormulaContourFamilyVerticalAvoidsSingularBoundary toContourFamily T

/-- A countable set of real heights misses every interval `(u, u + 1)`. -/
theorem exists_height_between_not_mem_countable
    (s : Set ℝ) (hs : s.Countable) (u : ℝ) :
    ∃ T : ℝ, u < T ∧ T < u + 1 ∧ T ∉ s := by
  have hdense : Dense sᶜ :=
    hs.dense_compl ℝ
  have hu : u < u + 1 :=
    lt_add_of_pos_right u zero_lt_one
  obtain ⟨T, hTcompl, hTinterval⟩ := hdense.exists_between hu
  exact ⟨T, hTinterval.1, hTinterval.2, hTcompl⟩

/-- The bad heights for a contour family are exactly the heights whose rectangle boundary
meets a completed-zeta singular point. -/
def explicitFormulaContourBadHeightSet
    (F : ExplicitFormulaContourFamily) : Set ℝ :=
  {T : ℝ | ¬ explicitFormulaContourFamilyAvoidsSingularBoundary F T}

/-- A height outside the bad-height set avoids all completed-zeta singularities on the
rectangle boundary. -/
theorem explicitFormulaContourFamilyAvoidsSingularBoundary_of_not_mem_badHeightSet
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hT : T ∉ explicitFormulaContourBadHeightSet F) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F T :=
  not_not.mp
    (show ¬ ¬ explicitFormulaContourFamilyAvoidsSingularBoundary F T from hT)

/-- A cofinal height schedule whose rectangles avoid zero/pole hits on the boundary. -/
structure ExplicitFormulaCofinalHeightSchedule
    (F : ExplicitFormulaContourFamily) where
  height : ℝ → ℝ
  cofinal : Tendsto height atTop atTop
  avoids_boundary :
    ∀ u : ℝ, explicitFormulaContourFamilyAvoidsSingularBoundary F (height u)

/-- A supplied cofinal height function avoiding horizontal bad heights gives a schedule for
a vertically regular contour family. -/
def explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingHeight
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (havoid : ∀ u : ℝ,
      height u ∉ explicitFormulaContourHorizontalBadHeightSet F.toContourFamily) :
    ExplicitFormulaCofinalHeightSchedule F.toContourFamily :=
  { height := height
    cofinal := hcofinal
    avoids_boundary :=
      fun u =>
        explicitFormulaContourFamilyAvoidsSingularBoundary_of_vertical_horizontal
          F.toContourFamily
          (height u)
          (F.vertical_avoids (height u))
          (explicitFormulaContourFamilyHorizontalAvoidsSingularBoundary_of_not_mem_horizontalBadHeightSet
            F.toContourFamily (height u) (havoid u)) }

/-- Owner-level analytic package for a single explicit-formula contour rectangle. -/
structure ExplicitFormulaAnalyticPackage (f : ZetaAdmissibleFunction) where
  phi_control : ZetaPhiAnalyticControl f
  logderiv_control : CompletedZetaNegLogDerivControl f
  contour_data : ExplicitFormulaContourData

/-- Owner-level analytic package for a contour family. -/
structure ExplicitFormulaFamilyAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) where
  phi_control : ZetaPhiAnalyticControl f
  logderiv_control : CompletedZetaNegLogDerivControl f
  height_schedule : ExplicitFormulaCofinalHeightSchedule F

/-- A family package has the same transform-control field as its record projection. -/
theorem ExplicitFormulaFamilyAnalyticPackage.phi_control_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    h.phi_control = h.phi_control :=
  rfl

/-- A family package has the same log-derivative-control field as its record projection. -/
theorem ExplicitFormulaFamilyAnalyticPackage.logderiv_control_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    h.logderiv_control = h.logderiv_control :=
  rfl

/-- The admissible source has completed log-derivative strip control. -/
noncomputable def completedZetaNegLogDerivControl_of_admissible
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivControl f :=
  { zero_excised_polynomial_growth :=
      fun a b E =>
        completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth a b E
    zero_excised_polynomial_strip_bound :=
      fun a b E N =>
        completedZetaNegLogDeriv_zeroExcisedPolynomialStripBound a b E N }

/-- The admissible source has the family analytic package for every vertically regular
contour family. -/
noncomputable def explicitFormulaFamilyAnalyticPackage_of_admissible
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily :=
  { phi_control := zetaPhiAnalyticControl_of_admissible f
    logderiv_control := completedZetaNegLogDerivControl_of_admissible f
    height_schedule := hSchedule }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
