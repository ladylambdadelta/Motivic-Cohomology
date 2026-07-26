import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaPuncturedPlane.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
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

open Complex Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed-zeta singular predicate relevant to the finite-rectangle residue theorem:
the poles at `0` and `1`, the Gamma-normalization zeros used by the completed and
archimedean channels, and the zeros of the completed zeta factor away from those poles. -/
def explicitFormulaContourSingularPoint (z : ℂ) : Prop :=
  z = 0 ∨ z = 1 ∨ Gammaℝ z = 0 ∨ Gammaℝ (z / 2) = 0 ∨
    (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)

/-- A nonsingular contour point is not the completed-zeta pole at `0`. -/
theorem explicitFormulaContourSingularPoint.ne_zero_of_not
    {z : ℂ} (hz : ¬ explicitFormulaContourSingularPoint z) :
    z ≠ 0 := by
  intro hz0
  exact hz (Or.inl hz0)

/-- A nonsingular contour point is not the completed-zeta pole at `1`. -/
theorem explicitFormulaContourSingularPoint.ne_one_of_not
    {z : ℂ} (hz : ¬ explicitFormulaContourSingularPoint z) :
    z ≠ 1 := by
  intro hz1
  exact hz (Or.inr (Or.inl hz1))

/-- A nonsingular contour point is away from the `Gammaℝ z` zero locus. -/
theorem explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
    {z : ℂ} (hz : ¬ explicitFormulaContourSingularPoint z) :
    Gammaℝ z ≠ 0 := by
  intro hgamma
  exact hz (Or.inr (Or.inr (Or.inl hgamma)))

/-- A nonsingular contour point is away from the half-argument Gamma zero locus. -/
theorem explicitFormulaContourSingularPoint.gamma_half_ne_zero_of_not
    {z : ℂ} (hz : ¬ explicitFormulaContourSingularPoint z) :
    Gammaℝ (z / 2) ≠ 0 := by
  intro hgamma
  exact hz (Or.inr (Or.inr (Or.inr (Or.inl hgamma))))

/-- A nonsingular contour point away from `0` and `1` is not a completed-zeta zero. -/
theorem explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
    {z : ℂ} (hz : ¬ explicitFormulaContourSingularPoint z) :
    completedRiemannZeta z ≠ 0 := by
  intro hzeta
  exact hz
    (Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            ⟨explicitFormulaContourSingularPoint.ne_zero_of_not hz,
              explicitFormulaContourSingularPoint.ne_one_of_not hz,
              hzeta⟩))))

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
  match hboundary with
  | Or.inl hright => exact hvertical z hz (Or.inl hright)
  | Or.inr (Or.inl hleft) => exact hvertical z hz (Or.inr hleft)
  | Or.inr (Or.inr (Or.inl htop)) => exact hhorizontal z hz (Or.inl htop)
  | Or.inr (Or.inr (Or.inr hbottom)) => exact hhorizontal z hz (Or.inr hbottom)

/-- The completed `Gammaℝ` zero locus is countable. -/
theorem Gammaℝ_zeroSet_countable :
    ({z : ℂ | Gammaℝ z = 0} : Set ℂ).Countable := by
  have hsubset :
      ({z : ℂ | Gammaℝ z = 0} : Set ℂ) ⊆
        Set.range (fun n : ℕ => (-(2 * (n : ℂ)) : ℂ)) := by
    intro z hz
    match Complex.Gammaℝ_eq_zero_iff.mp hz with
    | ⟨n, hn⟩ => exact ⟨n, hn.symm⟩
  exact (Set.countable_range (fun n : ℕ => (-(2 * (n : ℂ)) : ℂ))).mono hsubset

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
  match hhit with
  | Or.inl ⟨x, _hx, hzpath⟩ =>
      have him : T = z.im := by
        calc
          T = (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im := by
            exact (zetaCompletedExplicitFormulaTopPath_im (F.rectangle T) x).symm
          _ = z.im := by
            exact congrArg Complex.im hzpath.symm
      exact hT (Or.inl ⟨z, hz, him.symm⟩)
  | Or.inr ⟨x, _hx, hzpath⟩ =>
      have him : T = -z.im := by
        calc
          T = -((zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im) := by
            exact
              ((congrArg Neg.neg
                (zetaCompletedExplicitFormulaBottomPath_im (F.rectangle T) x)).trans
                (neg_neg T)).symm
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
  match hdense.exists_between hu with
  | ⟨T, hTcompl, hTinterval⟩ =>
      exact ⟨T, hTinterval.1, hTinterval.2, hTcompl⟩

/-- A supplied cofinal real-height schedule avoiding a fixed bad-height set.

This is the constructive owner object: the contour construction supplies the height
function, and the record carries its cofinality and avoidance facts. -/
structure CountableAvoidingCofinalHeightSchedule (s : Set ℝ) where
  bad_countable : s.Countable
  height : ℝ → ℝ
  cofinal : Tendsto height atTop atTop
  avoids : ∀ u : ℝ, height u ∉ s

/-- Package a supplied cofinal height function avoiding a countable bad-height set. -/
def CountableAvoidingCofinalHeightSchedule.of_height
    (s : Set ℝ) (hs : s.Countable)
    (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (havoid : ∀ u : ℝ, height u ∉ s) :
    CountableAvoidingCofinalHeightSchedule s :=
  { bad_countable := hs
    height := height
    cofinal := hcofinal
    avoids := havoid }

/- A countable bad-height set itself supplies a canonical cofinal avoiding
height function: choose one point in each interval (u,u+1) outside the bad
set. -/
noncomputable def CountableAvoidingCofinalHeightSchedule.of_countable_bad_set
    (s : Set ℝ) (hs : s.Countable) :
    CountableAvoidingCofinalHeightSchedule s := by
  let height : ℝ → ℝ := fun u =>
    Classical.choose (exists_height_between_not_mem_countable s hs u)
  have hheight : ∀ u : ℝ,
      u < height u ∧ height u < u + 1 ∧ height u ∉ s := by
    intro u
    exact Classical.choose_spec (exists_height_between_not_mem_countable s hs u)
  refine
    { bad_countable := hs
      height := height
      cofinal := ?_
      avoids := ?_ }
  · refine tendsto_atTop.2 (fun a => ?_)
    exact
      (eventually_ge_atTop a).mono
        (fun u hu => le_trans hu (le_of_lt (hheight u).1))
  · intro u
    exact (hheight u).2.2

/-- A countable avoiding schedule remembers the intervalwise existence theorem for its
bad-height set. -/
theorem CountableAvoidingCofinalHeightSchedule.exists_height_between_not_mem
    {s : Set ℝ} (schedule : CountableAvoidingCofinalHeightSchedule s) (u : ℝ) :
    ∃ T : ℝ, u < T ∧ T < u + 1 ∧ T ∉ s :=
  exists_height_between_not_mem_countable s schedule.bad_countable u

/-- A real height avoiding a finite list of bad heights has a positive separation from
that whole finite list. -/
theorem height_list_positive_separation_of_forall_ne
    (bad : List ℝ) (T : ℝ)
    (hT : ∀ y : ℝ, y ∈ bad → T ≠ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ∈ bad → δ ≤ ‖T - y‖ :=
  List.rec
    (motive := fun bad =>
      (∀ y : ℝ, y ∈ bad → T ≠ y) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ∈ bad → δ ≤ ‖T - y‖)
    (fun _ =>
      ⟨1, zero_lt_one,
        fun y hy =>
          False.elim (List.not_mem_nil y hy)⟩)
    (fun y ys ih hT =>
      have hTail : ∀ z : ℝ, z ∈ ys → T ≠ z :=
        fun z hz =>
          hT z (List.mem_cons_of_mem y hz)
      match ih hTail with
      | ⟨δ, hδ_pos, hδ_sep⟩ =>
          have hT_y : T ≠ y :=
            hT y (List.mem_cons_self y ys)
          have hsub_ne : T - y ≠ 0 :=
            fun hsub =>
              hT_y (sub_eq_zero.mp hsub)
          have hhead_pos : 0 < ‖T - y‖ :=
            norm_pos_iff.mpr hsub_ne
          ⟨min δ ‖T - y‖, lt_min hδ_pos hhead_pos,
            fun z hz =>
              match List.mem_cons.mp hz with
              | Or.inl hzy =>
                  Eq.subst
                    (motive := fun w : ℝ => min δ ‖T - y‖ ≤ ‖T - w‖)
                    hzy.symm
                    (min_le_right δ ‖T - y‖)
              | Or.inr hzTail =>
                  (min_le_left δ ‖T - y‖).trans
                    (hδ_sep z hzTail)⟩)
    bad hT

/- A finite carrier has the same positive separation statement.  This is the
owner-level bridge used by finite contour carriers; keeping it here avoids
repeating list-conversion arguments in residue and Cauchy consumers. -/
theorem height_finset_positive_separation_of_forall_ne
    (bad : Finset ℝ) (T : ℝ)
    (hT : ∀ y : ℝ, y ∈ bad → T ≠ y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ∈ bad → δ ≤ ‖T - y‖ := by
  let badList : List ℝ := bad.toList
  have hTList : ∀ y : ℝ, y ∈ badList → T ≠ y := by
    intro y hy
    exact hT y (Finset.mem_toList.mp hy)
  obtain ⟨δ, hδ, hδsep⟩ :=
    height_list_positive_separation_of_forall_ne badList T hTList
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  exact hδsep y (Finset.mem_toList.mpr hy)

theorem exists_height_between_not_mem_list_with_positive_separation
    (bad : List ℝ) (u : ℝ) :
    ∃ T : ℝ, ∃ δ : ℝ,
      u < T ∧ T < u + 1 ∧ 0 < δ ∧
        ∀ y : ℝ, y ∈ bad → δ ≤ ‖T - y‖ := by
  classical
  let badFinset : Finset ℝ := bad.toFinset
  obtain ⟨T, hT_lower, hT_upper, hT_avoid⟩ :=
    exists_height_between_not_mem_countable
      (badFinset : Set ℝ)
      badFinset.countable_toSet
      u
  have hT_ne : ∀ y : ℝ, y ∈ bad → T ≠ y := by
    intro y hy hEq
    apply hT_avoid
    have hyFinset : y ∈ badFinset := Finset.mem_toFinset.mpr hy
    exact hEq ▸ hyFinset
  obtain ⟨δ, hδ, hδsep⟩ :=
    height_list_positive_separation_of_forall_ne bad T hT_ne
  exact ⟨T, δ, hT_lower, hT_upper, hδ, hδsep⟩

/-- A countable avoiding schedule is positively separated from every supplied finite
sublist of its avoided bad-height set, at each scheduled height. -/
theorem CountableAvoidingCofinalHeightSchedule.height_list_positive_separation
    {s : Set ℝ} (schedule : CountableAvoidingCofinalHeightSchedule s)
    (bad : List ℝ) (hbad : ∀ y : ℝ, y ∈ bad → y ∈ s) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ∈ bad → δ ≤ ‖schedule.height u - y‖ :=
  height_list_positive_separation_of_forall_ne
    bad
    (schedule.height u)
    (fun y hy hEq =>
      schedule.avoids u
        (Eq.subst
          (motive := fun w : ℝ => w ∈ s)
          hEq.symm
          (hbad y hy)))

theorem CountableAvoidingCofinalHeightSchedule.height_finset_positive_separation
    {s : Set ℝ} (schedule : CountableAvoidingCofinalHeightSchedule s)
    (bad : Finset ℝ) (hbad : ∀ y : ℝ, y ∈ bad → y ∈ s) (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ∈ bad → δ ≤ ‖schedule.height u - y‖ := by
  let badList : List ℝ := bad.toList
  have hbadList : ∀ y : ℝ, y ∈ badList → y ∈ s := by
    intro y hy
    exact hbad y (Finset.mem_toList.mp hy)
  obtain ⟨δ, hδ, hδsep⟩ :=
    schedule.height_list_positive_separation badList hbadList u
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  exact hδsep y (Finset.mem_toList.mpr hy)

/-- The finite list of horizontal bad heights generated by a finite list of singular
points: top hits occur at `z.im`, bottom hits at `-z.im`. -/
def explicitFormulaContourSingularHeightList
    (points : List ℂ) : List ℝ :=
  points.map (fun z : ℂ => z.im) ++
    points.map (fun z : ℂ => -z.im)

/-- Heights extracted from a finite singular-point list lie in the horizontal bad-height
set. -/
theorem explicitFormulaContourSingularHeightList_subset_horizontalBadHeightSet
    (F : ExplicitFormulaContourFamily) (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z) :
    ∀ y : ℝ,
      y ∈ explicitFormulaContourSingularHeightList points →
        y ∈ explicitFormulaContourHorizontalBadHeightSet F := by
  intro y hy
  match List.mem_append.mp hy with
  | Or.inl htop =>
      match List.mem_map.mp htop with
      | ⟨z, hz_points, hzy⟩ =>
          exact Or.inl ⟨z, hpoints z hz_points, hzy⟩
  | Or.inr hbottom =>
      match List.mem_map.mp hbottom with
      | ⟨z, hz_points, hzy⟩ =>
          exact Or.inr ⟨z, hpoints z hz_points, hzy⟩

/-- A horizontal avoiding schedule has positive separation from the finite set of
horizontal bad heights generated by any finite singular-point list. -/
theorem CountableAvoidingCofinalHeightSchedule.singular_height_list_positive_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : CountableAvoidingCofinalHeightSchedule
      (explicitFormulaContourHorizontalBadHeightSet F))
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ,
        y ∈ explicitFormulaContourSingularHeightList points →
          δ ≤ ‖schedule.height u - y‖ :=
  CountableAvoidingCofinalHeightSchedule.height_list_positive_separation
    schedule
    (explicitFormulaContourSingularHeightList points)
    (explicitFormulaContourSingularHeightList_subset_horizontalBadHeightSet
      F points hpoints)
    u

/-- A horizontal avoiding schedule has one positive separation constant for the top and
bottom bad heights generated by each singular point in a finite list. -/
theorem CountableAvoidingCofinalHeightSchedule.singular_points_top_bottom_positive_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : CountableAvoidingCofinalHeightSchedule
      (explicitFormulaContourHorizontalBadHeightSet F))
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖schedule.height u - z.im‖ ∧
          δ ≤ ‖schedule.height u - (-z.im)‖ := by
  match schedule.singular_height_list_positive_separation points hpoints u with
  | ⟨δ, hδ_pos, hδ⟩ =>
      exact
        ⟨δ, hδ_pos,
          fun z hz =>
            And.intro
              (hδ z.im
                (List.mem_append.mpr
                  (Or.inl
                    (List.mem_map.mpr ⟨z, hz, rfl⟩))))
              (hδ (-z.im)
                (List.mem_append.mpr
                  (Or.inr
                    (List.mem_map.mpr ⟨z, hz, rfl⟩))))⟩

theorem CountableAvoidingCofinalHeightSchedule.singular_finset_top_bottom_positive_separation
    {F : ExplicitFormulaContourFamily}
    (schedule : CountableAvoidingCofinalHeightSchedule
      (explicitFormulaContourHorizontalBadHeightSet F))
    (points : Finset ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖schedule.height u - z.im‖ ∧
          δ ≤ ‖schedule.height u - (-z.im)‖ := by
  let pointList : List ℂ := points.toList
  have hpointList : ∀ z : ℂ, z ∈ pointList → explicitFormulaContourSingularPoint z := by
    intro z hz
    exact hpoints z (Finset.mem_toList.mp hz)
  obtain ⟨δ, hδ, hδsep⟩ :=
    schedule.singular_points_top_bottom_positive_separation
      pointList hpointList u
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  exact hδsep z (Finset.mem_toList.mpr hz)

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

/-- A top horizontal boundary point of an avoided rectangle is not a completed-zeta
contour singular point. -/
theorem explicitFormulaContourFamily_topPath_not_singular_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) := by
  intro hsingular
  exact havoid
    (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
    hsingular
    (Or.inr
      (Or.inr
        (Or.inl
          ⟨x, hx, rfl⟩)))

/-- A bottom horizontal boundary point of an avoided rectangle is not a completed-zeta
contour singular point. -/
theorem explicitFormulaContourFamily_bottomPath_not_singular_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) := by
  intro hsingular
  exact havoid
    (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
    hsingular
    (Or.inr
      (Or.inr
        (Or.inr
          ⟨x, hx, rfl⟩)))

/-- A cofinal height schedule whose rectangles avoid zero/pole hits on the boundary. -/
structure ExplicitFormulaCofinalHeightSchedule
    (F : ExplicitFormulaContourFamily) where
  height : ℝ → ℝ
  cofinal : Tendsto height atTop atTop
  avoids_boundary :
    ∀ u : ℝ, explicitFormulaContourFamilyAvoidsSingularBoundary F (height u)

/-- A cofinal height schedule is eventually above any fixed lower bound. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_height_gt
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (a : ℝ) :
    ∀ᶠ u in atTop, a < schedule.height u :=
  schedule.cofinal.eventually (eventually_gt_atTop a)

/-- A cofinal height schedule is eventually positive. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_height_pos
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop, 0 < schedule.height u :=
  schedule.eventually_height_gt 0

/-- A cofinal height schedule eventually has rectangle height norm at least any
fixed lower bound. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_rectangle_height_norm_ge
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (a : ℝ) :
    ∀ᶠ u in atTop, a ≤ ‖(F.rectangle (schedule.height u)).T‖ :=
  (schedule.eventually_height_gt a).mono
    (fun u hu =>
      have hle_height : a ≤ schedule.height u :=
        le_of_lt hu
      have hheight_le_norm :
          schedule.height u ≤ ‖schedule.height u‖ := by
        calc
          schedule.height u ≤ |schedule.height u| := by
            exact le_abs_self (schedule.height u)
          _ = ‖schedule.height u‖ := by
            exact (Real.norm_eq_abs (schedule.height u)).symm
      le_trans hle_height hheight_le_norm)

/-- A cofinal height schedule eventually has rectangle height norm at least
one. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_one_le_rectangle_height_norm
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop, 1 ≤ ‖(F.rectangle (schedule.height u)).T‖ :=
  schedule.eventually_rectangle_height_norm_ge 1

/-- If an avoided rectangle had height zero, the pole `1` would lie on its top
horizontal edge. -/
theorem explicitFormulaContourFamilyAvoidsSingularBoundary.height_ne_zero
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    T ≠ 0 := by
  intro hT
  have hsingular : explicitFormulaContourSingularPoint (1 : ℂ) :=
    Or.inr (Or.inl rfl)
  have hx_lower : min F.c (1 - F.c) ≤ (1 : ℝ) := by
    have hmin : min F.c (1 - F.c) ≤ 1 - F.c :=
      min_le_right F.c (1 - F.c)
    have hleft : 1 - F.c ≤ (1 : ℝ) := by
      exact sub_le_self (1 : ℝ) (le_of_lt F.c_pos)
    exact le_trans hmin hleft
  have hx_upper : (1 : ℝ) ≤ max F.c (1 - F.c) := by
    have hone_c : (1 : ℝ) ≤ F.c :=
      le_of_lt F.c_gt_one
    have hc_max : F.c ≤ max F.c (1 - F.c) :=
      le_max_left F.c (1 - F.c)
    exact le_trans hone_c hc_max
  have hx : (1 : ℝ) ∈ Set.uIcc F.c (1 - F.c) :=
    ⟨hx_lower, hx_upper⟩
  have htop_eq : (1 : ℂ) =
      zetaCompletedExplicitFormulaTopPath (F.rectangle T) 1 := by
    apply Complex.ext
    · calc
        (1 : ℂ).re = (1 : ℝ) := by
          exact Complex.one_re
        _ = (zetaCompletedExplicitFormulaTopPath (F.rectangle T) 1).re := by
          exact (zetaCompletedExplicitFormulaTopPath_re_eq (F.rectangle T) 1).symm
    · calc
        (1 : ℂ).im = (0 : ℝ) := by
          exact Complex.one_im
        _ = T := by
          exact hT.symm
        _ = (zetaCompletedExplicitFormulaTopPath (F.rectangle T) 1).im := by
          exact (zetaCompletedExplicitFormulaTopPath_im (F.rectangle T) 1).symm
  have hboundary :
      (1 : ℂ) ∈ explicitFormulaContourFamilyBoundary F T :=
    Or.inr
      (Or.inr
        (Or.inl
          ⟨1, hx, htop_eq⟩))
  exact havoid (1 : ℂ) hsingular hboundary

/-- Every height in a boundary-avoiding cofinal schedule is nonzero. -/
theorem ExplicitFormulaCofinalHeightSchedule.height_ne_zero
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) :
    schedule.height u ≠ 0 :=
  explicitFormulaContourFamilyAvoidsSingularBoundary.height_ne_zero
    F (schedule.height u) (schedule.avoids_boundary u)

/-- Along a cofinal schedule, the pole `0` is eventually inside the finite
contour-family rectangle. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_zero_mem_interior
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (schedule.height u) :=
  schedule.eventually_height_pos.mono
    (fun u hu =>
      explicitFormulaContourFamilyInterior_zero_mem F (schedule.height u) hu)

/-- Along a cofinal schedule, the pole `1` is eventually inside the finite
contour-family rectangle. -/
theorem ExplicitFormulaCofinalHeightSchedule.eventually_one_mem_interior
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (schedule.height u) :=
  schedule.eventually_height_pos.mono
    (fun u hu =>
      explicitFormulaContourFamilyInterior_one_mem F (schedule.height u) hu)

/-- Along a cofinal schedule, the pole `0` is eventually inside the finite
contour-family rectangle. -/
theorem explicitFormulaContourFamilyInterior_zero_mem_eventually
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (schedule.height u) :=
  schedule.eventually_zero_mem_interior

/-- Along a cofinal schedule, the pole `1` is eventually inside the finite
contour-family rectangle. -/
theorem explicitFormulaContourFamilyInterior_one_mem_eventually
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaCofinalHeightSchedule F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (schedule.height u) :=
  schedule.eventually_one_mem_interior

/-- A contour family together with the cofinal boundary-avoiding schedule supplied by its
construction.  This is the owner object used when downstream arguments need an actual
deterministic schedule rather than an existence theorem. -/
structure ExplicitFormulaScheduledContourFamily where
  toContourFamily : ExplicitFormulaContourFamily
  height_schedule : ExplicitFormulaCofinalHeightSchedule toContourFamily

/-- The contour-family projection of a scheduled contour family is its stored family. -/
theorem ExplicitFormulaScheduledContourFamily.toContourFamily_eq
    (F : ExplicitFormulaScheduledContourFamily) :
    F.toContourFamily = F.toContourFamily :=
  rfl

/-- The schedule projection of a scheduled contour family is its stored schedule. -/
theorem ExplicitFormulaScheduledContourFamily.height_schedule_eq
    (F : ExplicitFormulaScheduledContourFamily) :
    F.height_schedule = F.height_schedule :=
  rfl

/-- A supplied cofinal schedule avoiding the horizontal bad-height set of a contour
family. -/
abbrev ExplicitFormulaHorizontalAvoidingHeightSchedule
    (F : ExplicitFormulaContourFamily) :=
  CountableAvoidingCofinalHeightSchedule
    (explicitFormulaContourHorizontalBadHeightSet F)

/- The countability owner now constructs the canonical horizontal-avoiding
schedule directly; callers no longer need to supply a hidden height function. -/
noncomputable def explicitFormulaHorizontalAvoidingHeightSchedule_canonical
    (F : ExplicitFormulaContourFamily) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule F :=
  CountableAvoidingCofinalHeightSchedule.of_countable_bad_set
    (explicitFormulaContourHorizontalBadHeightSet F)
    (explicitFormulaContourHorizontalBadHeightSet_countable F)

theorem explicitFormulaHorizontalAvoidingHeightSchedule_canonical_height_avoids
    (F : ExplicitFormulaContourFamily) (u : ℝ) :
    (explicitFormulaHorizontalAvoidingHeightSchedule_canonical F).height u ∉
      explicitFormulaContourHorizontalBadHeightSet F :=
  (explicitFormulaHorizontalAvoidingHeightSchedule_canonical F).avoids u

/-- Package a supplied cofinal height function avoiding the completed-zeta horizontal
bad-height set. -/
def explicitFormulaHorizontalAvoidingHeightSchedule_of_height
    (F : ExplicitFormulaContourFamily)
    (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (havoid : ∀ u : ℝ,
      height u ∉ explicitFormulaContourHorizontalBadHeightSet F) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule F :=
  { bad_countable := explicitFormulaContourHorizontalBadHeightSet_countable F
    height := height
    cofinal := hcofinal
    avoids := havoid }

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

/- A vertically regular contour family therefore has a canonical boundary-
avoiding cofinal schedule, obtained from the canonical horizontal schedule. -/
noncomputable def explicitFormulaCofinalHeightSchedule_canonical
    (F : ExplicitFormulaVerticallyRegularContourFamily) :
    ExplicitFormulaCofinalHeightSchedule F.toContourFamily :=
  explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingHeight
    F
    (explicitFormulaHorizontalAvoidingHeightSchedule_canonical F.toContourFamily).height
    (explicitFormulaHorizontalAvoidingHeightSchedule_canonical F.toContourFamily).cofinal
    (explicitFormulaHorizontalAvoidingHeightSchedule_canonical_height_avoids
      F.toContourFamily)

/-- A supplied horizontal avoiding schedule gives a boundary-avoiding cofinal schedule for
a vertically regular contour family. -/
def explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily) :
    ExplicitFormulaCofinalHeightSchedule F.toContourFamily :=
  explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingHeight
    F schedule.height schedule.cofinal schedule.avoids

/-- Package a vertically regular contour family with a supplied horizontal avoiding
schedule as a scheduled contour family. -/
def explicitFormulaScheduledContourFamily_of_horizontalAvoidingSchedule
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily) :
    ExplicitFormulaScheduledContourFamily :=
  { toContourFamily := F.toContourFamily
    height_schedule :=
      explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule F schedule }

/- Canonical scheduled contour-family owner: vertical regularity plus the
countable horizontal singular set is sufficient to construct the schedule. -/
noncomputable def explicitFormulaScheduledContourFamily_canonical
    (F : ExplicitFormulaVerticallyRegularContourFamily) :
    ExplicitFormulaScheduledContourFamily :=
  { toContourFamily := F.toContourFamily
    height_schedule := explicitFormulaCofinalHeightSchedule_canonical F }

/-- The scheduled family built from a horizontal avoiding schedule has the original
contour-family projection. -/
theorem explicitFormulaScheduledContourFamily_of_horizontalAvoidingSchedule_toContourFamily
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily) :
    (explicitFormulaScheduledContourFamily_of_horizontalAvoidingSchedule
      F schedule).toContourFamily =
      F.toContourFamily := by
  rfl

/-- The scheduled family built from a horizontal avoiding schedule carries the induced
boundary-avoiding cofinal schedule. -/
theorem explicitFormulaScheduledContourFamily_of_horizontalAvoidingSchedule_height_schedule
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily) :
    (explicitFormulaScheduledContourFamily_of_horizontalAvoidingSchedule
      F schedule).height_schedule =
      explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule F schedule := by
  rfl

/-- The cofinal schedule induced from a horizontal-avoiding schedule has the same height
function as the original horizontal schedule. -/
theorem explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_height
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily) :
    (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
      F schedule).height = schedule.height := by
  rfl

/-- A supplied horizontal avoiding schedule also carries the countability fact for the
completed-zeta horizontal bad-height set. -/
theorem ExplicitFormulaHorizontalAvoidingHeightSchedule.exists_height_between_not_mem
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaHorizontalAvoidingHeightSchedule F) (u : ℝ) :
    ∃ T : ℝ,
      u < T ∧ T < u + 1 ∧
        T ∉ explicitFormulaContourHorizontalBadHeightSet F :=
  CountableAvoidingCofinalHeightSchedule.exists_height_between_not_mem
    schedule u

/-- A horizontal avoiding schedule is positively separated from every finite list of
horizontal bad heights, at each scheduled height. -/
theorem ExplicitFormulaHorizontalAvoidingHeightSchedule.height_list_positive_separation
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaHorizontalAvoidingHeightSchedule F)
    (bad : List ℝ)
    (hbad : ∀ y : ℝ, y ∈ bad → y ∈ explicitFormulaContourHorizontalBadHeightSet F)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ∈ bad → δ ≤ ‖schedule.height u - y‖ :=
  CountableAvoidingCofinalHeightSchedule.height_list_positive_separation
    schedule bad hbad u

/-- A horizontal avoiding schedule is positively separated from the finite horizontal
bad-height list generated by any finite list of singular points. -/
theorem ExplicitFormulaHorizontalAvoidingHeightSchedule.singular_height_list_positive_separation
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaHorizontalAvoidingHeightSchedule F)
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ,
        y ∈ explicitFormulaContourSingularHeightList points →
          δ ≤ ‖schedule.height u - y‖ :=
  CountableAvoidingCofinalHeightSchedule.singular_height_list_positive_separation
    schedule points hpoints u

/-- A horizontal avoiding schedule has one positive separation constant for top and bottom
heights of each singular point in a finite list. -/
theorem ExplicitFormulaHorizontalAvoidingHeightSchedule.singular_points_top_bottom_positive_separation
    (F : ExplicitFormulaContourFamily)
    (schedule : ExplicitFormulaHorizontalAvoidingHeightSchedule F)
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖schedule.height u - z.im‖ ∧
          δ ≤ ‖schedule.height u - (-z.im)‖ :=
  CountableAvoidingCofinalHeightSchedule.singular_points_top_bottom_positive_separation
    schedule points hpoints u

/-- The boundary-avoiding cofinal schedule induced from a horizontal-avoiding schedule
inherits finite-list horizontal singular-height separation. -/
theorem explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_singular_height_list_positive_separation
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily)
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ,
        y ∈ explicitFormulaContourSingularHeightList points →
          δ ≤ ‖
            (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
              F schedule).height u - y‖ :=
  Eq.subst
    (motive := fun height : ℝ → ℝ =>
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ,
          y ∈ explicitFormulaContourSingularHeightList points →
            δ ≤ ‖height u - y‖)
    (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_height
      F schedule).symm
    (ExplicitFormulaHorizontalAvoidingHeightSchedule.singular_height_list_positive_separation
      F.toContourFamily schedule points hpoints u)

/-- The boundary-avoiding cofinal schedule induced from a horizontal-avoiding schedule
inherits one finite-window separation constant for both top and bottom singular heights. -/
theorem explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_singular_points_top_bottom_positive_separation
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily)
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖
          (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
            F schedule).height u - z.im‖ ∧
          δ ≤ ‖
            (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
              F schedule).height u - (-z.im)‖ :=
  Eq.subst
    (motive := fun height : ℝ → ℝ =>
      ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℂ, z ∈ points →
          δ ≤ ‖height u - z.im‖ ∧
            δ ≤ ‖height u - (-z.im)‖)
    (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_height
      F schedule).symm
    (ExplicitFormulaHorizontalAvoidingHeightSchedule.singular_points_top_bottom_positive_separation
      F.toContourFamily schedule points hpoints u)

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

/-- The height schedule stored in a family analytic package is eventually positive. -/
theorem ExplicitFormulaFamilyAnalyticPackage.eventually_height_pos
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop, 0 < h.height_schedule.height u :=
  h.height_schedule.eventually_height_pos

/-- Along a family analytic package, the pole `0` is eventually inside the
scheduled finite contour-family rectangle. -/
theorem ExplicitFormulaFamilyAnalyticPackage.eventually_zero_mem_interior
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.height_schedule.eventually_zero_mem_interior

/-- Along a family analytic package, the pole `1` is eventually inside the
scheduled finite contour-family rectangle. -/
theorem ExplicitFormulaFamilyAnalyticPackage.eventually_one_mem_interior
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.height_schedule.eventually_one_mem_interior

/-- Along a family analytic package, the pole `0` is eventually inside the
scheduled finite contour-family rectangle. -/
theorem explicitFormulaFamilyAnalyticPackage_zero_mem_interior_eventually
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_zero_mem_interior

/-- Along a family analytic package, the pole `1` is eventually inside the
scheduled finite contour-family rectangle. -/
theorem explicitFormulaFamilyAnalyticPackage_one_mem_interior_eventually
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_one_mem_interior

/-- Construct a family analytic package from a vertically regular family and a horizontal
bad-height-avoiding schedule. -/
def ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
    {f : ZetaAdmissibleFunction}
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily)
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f) :
    ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily :=
  { phi_control := hPhi
    logderiv_control := hLog
    height_schedule :=
      explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
        F schedule }

/-- The analytic package built from a horizontal-avoiding schedule stores the induced
cofinal height schedule. -/
theorem ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule_height_schedule
    {f : ZetaAdmissibleFunction}
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily)
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f) :
    (ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
      F schedule hPhi hLog).height_schedule =
      explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule
        F schedule := by
  rfl

/-- A family analytic package built from a horizontal-avoiding schedule has finite-list
horizontal singular-height separation along its stored schedule. -/
theorem ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule_singular_points_top_bottom_positive_separation
    {f : ZetaAdmissibleFunction}
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule F.toContourFamily)
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (points : List ℂ)
    (hpoints : ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖
          (ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
            F schedule hPhi hLog).height_schedule.height u - z.im‖ ∧
          δ ≤ ‖
            (ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
              F schedule hPhi hLog).height_schedule.height u - (-z.im)‖ :=
  Eq.subst
    (motive := fun h :
      ExplicitFormulaCofinalHeightSchedule F.toContourFamily =>
      ∃ δ : ℝ, 0 < δ ∧
        ∀ z : ℂ, z ∈ points →
          δ ≤ ‖h.height u - z.im‖ ∧
            δ ≤ ‖h.height u - (-z.im)‖)
    (ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule_height_schedule
      F schedule hPhi hLog).symm
    (explicitFormulaCofinalHeightSchedule_of_horizontalAvoidingSchedule_singular_points_top_bottom_positive_separation
      F schedule points hpoints u)

/-- Along the package schedule, every top horizontal boundary point avoids the
completed-zeta contour singular set. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_not_singular
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) :=
  explicitFormulaContourFamily_topPath_not_singular_of_avoidsBoundary
    F
    (h.height_schedule.height u)
    x
    (h.height_schedule.avoids_boundary u)
    hx

/-- Along the package schedule, every bottom horizontal boundary point avoids the
completed-zeta contour singular set. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_not_singular
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ¬ explicitFormulaContourSingularPoint
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) :=
  explicitFormulaContourFamily_bottomPath_not_singular_of_avoidsBoundary
    F
    (h.height_schedule.height u)
    x
    (h.height_schedule.avoids_boundary u)
    hx

/-- Along the package schedule, the top horizontal boundary point is not a
completed-zeta zero. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_completedRiemannZeta_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
    (h.scheduled_topPath_not_singular u x hx)

/-- Along the package schedule, the bottom horizontal boundary point is not a
completed-zeta zero. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_completedRiemannZeta_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
    (h.scheduled_bottomPath_not_singular u x hx)

/-- Along the package schedule, the top horizontal boundary point is away from
the completed Gamma zero locus. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_Gammaℝ_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
    (h.scheduled_topPath_not_singular u x hx)

/-- Along the package schedule, the bottom horizontal boundary point is away from
the completed Gamma zero locus. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_Gammaℝ_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
    (h.scheduled_bottomPath_not_singular u x hx)

/-- Along the package schedule, the top horizontal boundary point is not the
completed-zeta pole at `0`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 :=
  explicitFormulaContourSingularPoint.ne_zero_of_not
    (h.scheduled_topPath_not_singular u x hx)

/-- Along the package schedule, the bottom horizontal boundary point is not the
completed-zeta pole at `0`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 :=
  explicitFormulaContourSingularPoint.ne_zero_of_not
    (h.scheduled_bottomPath_not_singular u x hx)

/-- Along the package schedule, the top horizontal boundary point is not the
completed-zeta pole at `1`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_ne_one
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 :=
  explicitFormulaContourSingularPoint.ne_one_of_not
    (h.scheduled_topPath_not_singular u x hx)

/-- Along the package schedule, the bottom horizontal boundary point is not the
completed-zeta pole at `1`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_ne_one
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 :=
  explicitFormulaContourSingularPoint.ne_one_of_not
    (h.scheduled_bottomPath_not_singular u x hx)

/-- Along the package schedule, the top horizontal boundary point is away from
the half-argument completed Gamma zero locus. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_Gammaℝ_half_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_half_ne_zero_of_not
    (h.scheduled_topPath_not_singular u x hx)

/-- Along the package schedule, the bottom horizontal boundary point is away from
the half-argument completed Gamma zero locus. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_Gammaℝ_half_ne_zero
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  explicitFormulaContourSingularPoint.gamma_half_ne_zero_of_not
    (h.scheduled_bottomPath_not_singular u x hx)

/-- Scheduled top horizontal points satisfy the pointwise zero-excised strip
conditions supplied by boundary avoidance.  The strip carrier is geometric; analytic
polynomial bounds remain owned by `CompletedZetaNegLogDerivControl`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_zeroExcisedPointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
  Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  And.intro
    (And.intro
      (Eq.subst
        (motive := fun y : ℝ => min F.c (1 - F.c) ≤ y)
        (zetaCompletedExplicitFormulaTopPath_re_eq
          (F.rectangle (h.height_schedule.height u)) x).symm
        hx.1)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ max F.c (1 - F.c))
        (zetaCompletedExplicitFormulaTopPath_re_eq
          (F.rectangle (h.height_schedule.height u)) x).symm
        hx.2))
    (And.intro
      (h.scheduled_topPath_ne_zero u x hx)
      (And.intro
        (h.scheduled_topPath_ne_one u x hx)
        (And.intro
          (h.scheduled_topPath_completedRiemannZeta_ne_zero u x hx)
          (And.intro
            (h.scheduled_topPath_Gammaℝ_ne_zero u x hx)
            (h.scheduled_topPath_Gammaℝ_half_ne_zero u x hx)))))

/-- Scheduled bottom horizontal points satisfy the pointwise zero-excised strip
conditions supplied by boundary avoidance.  The strip carrier is geometric; analytic
polynomial bounds remain owned by `CompletedZetaNegLogDerivControl`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_zeroExcisedPointwise
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    (min F.c (1 - F.c) ≤
        (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x).re ∧
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x).re ≤
        max F.c (1 - F.c)) ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 0 ∧
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x ≠ 1 ∧
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
    Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x) ≠ 0 ∧
  Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x / 2) ≠ 0 :=
  And.intro
    (And.intro
      (Eq.subst
        (motive := fun y : ℝ => min F.c (1 - F.c) ≤ y)
        (zetaCompletedExplicitFormulaBottomPath_re_eq
          (F.rectangle (h.height_schedule.height u)) x).symm
        hx.1)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ max F.c (1 - F.c))
        (zetaCompletedExplicitFormulaBottomPath_re_eq
          (F.rectangle (h.height_schedule.height u)) x).symm
        hx.2))
    (And.intro
      (h.scheduled_bottomPath_ne_zero u x hx)
      (And.intro
        (h.scheduled_bottomPath_ne_one u x hx)
        (And.intro
          (h.scheduled_bottomPath_completedRiemannZeta_ne_zero u x hx)
          (And.intro
            (h.scheduled_bottomPath_Gammaℝ_ne_zero u x hx)
            (h.scheduled_bottomPath_Gammaℝ_half_ne_zero u x hx)))))

/-- The full scheduled horizontal edge family has a shared geometric zero-excised carrier.

The carrier is the union of all top and bottom horizontal points along the stored schedule.
Analytic polynomial log-derivative bounds for this geometric carrier are supplied by
`CompletedZetaNegLogDerivControl`, not by the carrier itself. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) ∧
      (∀ u x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) := by
  let topCarrier : Set ℂ :=
    {z : ℂ |
      ∃ u x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z =
            zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height u)) x}
  let bottomCarrier : Set ℂ :=
    {z : ℂ |
      ∃ u x : ℝ,
        x ∈ Set.uIcc F.c (1 - F.c) ∧
          z =
            zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height u)) x}
  let E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
    { carrier := topCarrier ∪ bottomCarrier
      in_strip :=
        fun z hz =>
          match (Set.mem_union z topCarrier bottomCarrier).mp hz with
          | Or.inl hztop =>
              match hztop with
              | ⟨u, x, hx, hz_eq⟩ =>
                  have hpoint :
                      (min F.c (1 - F.c) ≤
                          (zetaCompletedExplicitFormulaTopPath
                            (F.rectangle (h.height_schedule.height u)) x).re ∧
                        (zetaCompletedExplicitFormulaTopPath
                            (F.rectangle (h.height_schedule.height u)) x).re ≤
                          max F.c (1 - F.c)) :=
                    (h.scheduled_topPath_zeroExcisedPointwise u x hx).1
                  Eq.subst
                    (motive := fun w : ℂ =>
                      min F.c (1 - F.c) ≤ w.re ∧
                        w.re ≤ max F.c (1 - F.c))
                    hz_eq.symm
                    hpoint
          | Or.inr hzbottom =>
              match hzbottom with
              | ⟨u, x, hx, hz_eq⟩ =>
                  have hpoint :
                      (min F.c (1 - F.c) ≤
                          (zetaCompletedExplicitFormulaBottomPath
                            (F.rectangle (h.height_schedule.height u)) x).re ∧
                        (zetaCompletedExplicitFormulaBottomPath
                            (F.rectangle (h.height_schedule.height u)) x).re ≤
                          max F.c (1 - F.c)) :=
                    (h.scheduled_bottomPath_zeroExcisedPointwise u x hx).1
                  Eq.subst
                    (motive := fun w : ℂ =>
                      min F.c (1 - F.c) ≤ w.re ∧
                        w.re ≤ max F.c (1 - F.c))
                    hz_eq.symm
                    hpoint
      ne_zero :=
        fun z hz =>
          match (Set.mem_union z topCarrier bottomCarrier).mp hz with
          | Or.inl hztop =>
              match hztop with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_topPath_ne_zero u x hx)
          | Or.inr hzbottom =>
              match hzbottom with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_bottomPath_ne_zero u x hx)
      ne_one :=
        fun z hz =>
          match (Set.mem_union z topCarrier bottomCarrier).mp hz with
          | Or.inl hztop =>
              match hztop with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => w ≠ 1)
                    hz_eq.symm
                    (h.scheduled_topPath_ne_one u x hx)
          | Or.inr hzbottom =>
              match hzbottom with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => w ≠ 1)
                    hz_eq.symm
                    (h.scheduled_bottomPath_ne_one u x hx)
      zeta_ne_zero :=
        fun z hz =>
          match (Set.mem_union z topCarrier bottomCarrier).mp hz with
          | Or.inl hztop =>
              match hztop with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_topPath_completedRiemannZeta_ne_zero u x hx)
          | Or.inr hzbottom =>
              match hzbottom with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_bottomPath_completedRiemannZeta_ne_zero u x hx)
      gamma_ne_zero :=
        fun z hz =>
          match (Set.mem_union z topCarrier bottomCarrier).mp hz with
          | Or.inl hztop =>
              match hztop with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => Gammaℝ w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_topPath_Gammaℝ_ne_zero u x hx)
          | Or.inr hzbottom =>
              match hzbottom with
              | ⟨u, x, hx, hz_eq⟩ =>
                  Eq.subst
                    (motive := fun w : ℂ => Gammaℝ w ≠ 0)
                    hz_eq.symm
                    (h.scheduled_bottomPath_Gammaℝ_ne_zero u x hx) }
  exact
    ⟨E,
      And.intro
        (fun u x hx =>
          Set.mem_union_left bottomCarrier ⟨u, x, hx, rfl⟩)
        (fun u x hx =>
          Set.mem_union_right topCarrier ⟨u, x, hx, rfl⟩)⟩

/-- A scheduled top horizontal point determines its own singleton zero-excised strip. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_topPath_singletonZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  match h.scheduled_topPath_zeroExcisedPointwise u x hx with
  | ⟨hstrip, hz0, hz1, hzeta, hgamma, _hgamma_half⟩ =>
      exact
        ⟨CompletedZetaZeroExcisedStrip.singleton z hstrip hz0 hz1 hzeta hgamma,
          CompletedZetaZeroExcisedStrip.mem_singleton z hstrip hz0 hz1 hzeta hgamma⟩

/-- A scheduled bottom horizontal point determines its own singleton zero-excised strip. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_bottomPath_singletonZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier := by
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  match h.scheduled_bottomPath_zeroExcisedPointwise u x hx with
  | ⟨hstrip, hz0, hz1, hzeta, hgamma, _hgamma_half⟩ =>
      exact
        ⟨CompletedZetaZeroExcisedStrip.singleton z hstrip hz0 hz1 hzeta hgamma,
          CompletedZetaZeroExcisedStrip.mem_singleton z hstrip hz0 hz1 hzeta hgamma⟩

/-- A scheduled top/bottom horizontal pair at one parameter value has a shared finite
zero-excised strip carrier. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalPairZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      zetaCompletedExplicitFormulaTopPath
        (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier := by
  let ztop : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      (F.rectangle (h.height_schedule.height u)) x
  let zbottom : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (h.height_schedule.height u)) x
  match h.scheduled_topPath_zeroExcisedPointwise u x hx with
  | ⟨htop_strip, htop_zero, htop_one, htop_zeta, htop_gamma, _htop_gamma_half⟩ =>
      match h.scheduled_bottomPath_zeroExcisedPointwise u x hx with
      | ⟨hbottom_strip, hbottom_zero, hbottom_one, hbottom_zeta,
          hbottom_gamma, _hbottom_gamma_half⟩ =>
          let Etop : CompletedZetaZeroExcisedStrip
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.singleton
              ztop htop_strip htop_zero htop_one htop_zeta htop_gamma
          let Ebottom : CompletedZetaZeroExcisedStrip
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.singleton
              zbottom hbottom_strip hbottom_zero hbottom_one hbottom_zeta hbottom_gamma
          exact
            ⟨CompletedZetaZeroExcisedStrip.union Etop Ebottom,
              And.intro
                (CompletedZetaZeroExcisedStrip.mem_union_left Etop Ebottom
                  (CompletedZetaZeroExcisedStrip.mem_singleton
                    ztop htop_strip htop_zero htop_one htop_zeta htop_gamma))
                (CompletedZetaZeroExcisedStrip.mem_union_right Etop Ebottom
                  (CompletedZetaZeroExcisedStrip.mem_singleton
                    zbottom hbottom_strip hbottom_zero hbottom_one hbottom_zeta
                      hbottom_gamma))⟩

/-- A finite scheduled horizontal window has a shared zero-excised strip carrier for all
top and bottom points indexed by the window. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteWindowZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (xs : List ℝ)
    (hxs : ∀ x : ℝ, x ∈ xs → x ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) ∧
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :=
  List.rec
    (motive := fun xs =>
      (∀ x : ℝ, x ∈ xs → x ∈ Set.uIcc F.c (1 - F.c)) →
        ∃ E : CompletedZetaZeroExcisedStrip
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          (∀ x : ℝ, x ∈ xs →
            zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) ∧
          (∀ x : ℝ, x ∈ xs →
            zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier))
    (fun _ =>
      ⟨CompletedZetaZeroExcisedStrip.empty
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        And.intro
          (fun x hx => False.elim (List.not_mem_nil x hx))
          (fun x hx => False.elim (List.not_mem_nil x hx))⟩)
    (fun x xs ih hxs =>
      have htail : ∀ y : ℝ, y ∈ xs → y ∈ Set.uIcc F.c (1 - F.c) :=
        fun y hy =>
          hxs y (List.mem_cons_of_mem x hy)
      match h.scheduled_horizontalPairZeroExcisedStrip
          u x (hxs x (List.mem_cons_self x xs)), ih htail with
      | ⟨Ehead, hhead_top, hhead_bottom⟩, ⟨Etail, htail_top, htail_bottom⟩ =>
          let E : CompletedZetaZeroExcisedStrip
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.union Ehead Etail
          ⟨E,
            And.intro
              (fun y hy =>
                match List.mem_cons.mp hy with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                          (F.rectangle (h.height_schedule.height u)) w ∈ E.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.mem_union_left Ehead Etail
                        hhead_top)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.mem_union_right Ehead Etail
                      (htail_top y hytail))
              (fun y hy =>
                match List.mem_cons.mp hy with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                          (F.rectangle (h.height_schedule.height u)) w ∈ E.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.mem_union_left Ehead Etail
                        hhead_bottom)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.mem_union_right Ehead Etail
                      (htail_bottom y hytail))⟩)
    xs hxs

/-- Any finite scheduled horizontal sample has a shared zero-excised strip carrier for
all sampled top and bottom points.  The sample records both the schedule parameter and
the horizontal edge parameter. -/
theorem ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFiniteSampleZeroExcisedStrip
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (samples : List (ℝ × ℝ))
    (hsamples :
      ∀ p : ℝ × ℝ, p ∈ samples → p.2 ∈ Set.uIcc F.c (1 - F.c)) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height p.1)) p.2 ∈ E.carrier) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height p.1)) p.2 ∈ E.carrier) :=
  List.rec
    (motive := fun samples =>
      (∀ p : ℝ × ℝ, p ∈ samples → p.2 ∈ Set.uIcc F.c (1 - F.c)) →
        ∃ E : CompletedZetaZeroExcisedStrip
            (min F.c (1 - F.c)) (max F.c (1 - F.c)),
          (∀ p : ℝ × ℝ, p ∈ samples →
            zetaCompletedExplicitFormulaTopPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈ E.carrier) ∧
          (∀ p : ℝ × ℝ, p ∈ samples →
            zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (h.height_schedule.height p.1)) p.2 ∈ E.carrier))
    (fun _ =>
      ⟨CompletedZetaZeroExcisedStrip.empty
          (min F.c (1 - F.c)) (max F.c (1 - F.c)),
        And.intro
          (fun p hp => False.elim (List.not_mem_nil p hp))
          (fun p hp => False.elim (List.not_mem_nil p hp))⟩)
    (fun p samples ih hsamples =>
      have htail :
          ∀ q : ℝ × ℝ, q ∈ samples → q.2 ∈ Set.uIcc F.c (1 - F.c) :=
        fun q hq =>
          hsamples q (List.mem_cons_of_mem p hq)
      match h.scheduled_horizontalPairZeroExcisedStrip
          p.1 p.2 (hsamples p (List.mem_cons_self p samples)), ih htail with
      | ⟨Ehead, hhead_top, hhead_bottom⟩, ⟨Etail, htail_top, htail_bottom⟩ =>
          let E : CompletedZetaZeroExcisedStrip
              (min F.c (1 - F.c)) (max F.c (1 - F.c)) :=
            CompletedZetaZeroExcisedStrip.union Ehead Etail
          ⟨E,
            And.intro
              (fun q hq =>
                match List.mem_cons.mp hq with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                          (F.rectangle (h.height_schedule.height r.1)) r.2 ∈ E.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.mem_union_left Ehead Etail
                        hhead_top)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.mem_union_right Ehead Etail
                      (htail_top q hqtail))
              (fun q hq =>
                match List.mem_cons.mp hq with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                          (F.rectangle (h.height_schedule.height r.1)) r.2 ∈ E.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.mem_union_left Ehead Etail
                        hhead_bottom)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.mem_union_right Ehead Etail
                      (htail_bottom q hqtail))⟩)
    samples hsamples

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

/-- Build completed log-derivative strip control from supplied concrete strip constants. -/
def completedZetaNegLogDerivControl_of_suppliedConstants
    (f : ZetaAdmissibleFunction)
    (C : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < C a b E N)
    (hCbound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
        (z : ℂ),
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤ C a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivControl f :=
  CompletedZetaNegLogDerivControl.ofSuppliedConstants f C hCpos hCbound

/-- Supplied transform and log-derivative controls give the family analytic package for
every vertically regular contour family. -/
def explicitFormulaFamilyAnalyticPackage_of_controls
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily :=
  { phi_control := hPhi
    logderiv_control := hLog
    height_schedule := hSchedule }

/-- Supplied transform and log-derivative controls give the family analytic package for
any scheduled contour family. -/
def explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaScheduledContourFamily) :
    ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily :=
  { phi_control := hPhi
    logderiv_control := hLog
    height_schedule := F.height_schedule }

/-- The analytic package built from a scheduled contour family uses the stored schedule. -/
theorem explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily_height_schedule
    {f : ZetaAdmissibleFunction}
    (hPhi : ZetaPhiAnalyticControl f)
    (hLog : CompletedZetaNegLogDerivControl f)
    (F : ExplicitFormulaScheduledContourFamily) :
    (explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily hPhi hLog F).height_schedule =
      F.height_schedule := by
  rfl

/-- The fixed right edge used for the autocorrelation explicit-formula contour family. -/
def zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge
    (_f : ZetaAdmissibleFunction) : ℝ :=
  (1 / 2 : ℝ) + 1

/-- The autocorrelation contour right edge lies strictly to the right of the critical line. -/
theorem zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_half
    (f : ZetaAdmissibleFunction) :
    (1 / 2 : ℝ) <
      zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge f := by
  exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one

/-- The contour family used by the completed explicit formula on an autocorrelation probe. -/
def zetaCompletedExplicitFormula_autocorrelation_contourFamily
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaContourFamily :=
  { c := zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge f
    c_gt_one := by
      have hhalf_pos : (0 : ℝ) < 1 / 2 :=
        real_half_pos_for_contourGeometry
      have hadd :
          (0 : ℝ) + 1 < (1 / 2 : ℝ) + 1 :=
        add_lt_add_right hhalf_pos 1
      exact Eq.subst
        (motive := fun x : ℝ => x < (1 / 2 : ℝ) + 1)
        (zero_add (1 : ℝ))
        hadd
    c_gt_half :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily_rightEdge_gt_half f
    c_ne_one := by
      intro h
      have hhalf_zero : (1 / 2 : ℝ) = 0 := by
        have hone : (1 / 2 : ℝ) + 1 = 0 + 1 := by
          exact h.trans (zero_add (1 : ℝ)).symm
        exact add_right_cancel hone
      exact (ne_of_gt real_half_pos_for_contourGeometry) hhalf_zero }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
