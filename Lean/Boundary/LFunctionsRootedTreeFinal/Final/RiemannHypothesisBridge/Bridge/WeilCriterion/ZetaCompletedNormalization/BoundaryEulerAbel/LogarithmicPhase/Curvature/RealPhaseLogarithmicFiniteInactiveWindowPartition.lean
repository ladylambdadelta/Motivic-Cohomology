import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactivePrincipalEndpoint
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUniversalEndpointPacket

/-!
# Balanced-window partition of finite inactive modes

A finite inactive stationary center lies outside `[a,b]`.  It is called near
when its balanced window reaches the nearest principal endpoint, and far when
the entire window misses the principal interval.  Near modes use the universal
clipped stationary estimate; far modes use monotone reciprocal-gap decay.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftNearEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonLeftInactiveModes t a b).filter
    (fun m : ℤ =>
      (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowRight t m)

def Complex.logarithmicPhaseFiniteLeftFarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonLeftInactiveModes t a b).filter
    (fun m : ℤ =>
      Complex.logarithmicPhaseBProcessWindowRight t m < (a : ℝ))

def Complex.logarithmicPhaseFiniteRightNearEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonRightInactiveModes t a b).filter
    (fun m : ℤ =>
      Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (b : ℝ))

def Complex.logarithmicPhaseFiniteRightFarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonRightInactiveModes t a b).filter
    (fun m : ℤ =>
      (b : ℝ) < Complex.logarithmicPhaseBProcessWindowLeft t m)

theorem Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∧
        (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowRight t m := by
  unfold Complex.logarithmicPhaseFiniteLeftNearEndpointModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∧
        Complex.logarithmicPhaseBProcessWindowRight t m < (a : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteLeftFarModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b ∧
        Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (b : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteRightNearEndpointModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b ∧
        (b : ℝ) < Complex.logarithmicPhaseBProcessWindowLeft t m := by
  unfold Complex.logarithmicPhaseFiniteRightFarModes
  exact Finset.mem_filter

theorem Complex.logarithmicPhaseFiniteLeftFarModes_subset_leftInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFarModes t a b ⊆
      Complex.logarithmicPhasePoissonLeftInactiveModes t a b := by
  intro m hm
  exact ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
    t a b m).mp hm).1

theorem Complex.logarithmicPhaseFiniteRightFarModes_subset_rightInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteRightFarModes t a b ⊆
      Complex.logarithmicPhasePoissonRightInactiveModes t a b := by
  intro m hm
  exact ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
    t a b m).mp hm).1

theorem Complex.logarithmicPhaseFiniteLeftFarModes_card_le_leftInactive
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhaseFiniteLeftFarModes t a b).card ≤
      (Complex.logarithmicPhasePoissonLeftInactiveModes t a b).card := by
  exact Finset.card_le_card
    (Complex.logarithmicPhaseFiniteLeftFarModes_subset_leftInactive t a b)

theorem Complex.logarithmicPhaseFiniteRightFarModes_card_le_rightInactive
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhaseFiniteRightFarModes t a b).card ≤
      (Complex.logarithmicPhasePoissonRightInactiveModes t a b).card := by
  exact Finset.card_le_card
    (Complex.logarithmicPhaseFiniteRightFarModes_subset_rightInactive t a b)

theorem Complex.logarithmicPhaseFiniteLeftNear_union_far
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b ∪
        Complex.logarithmicPhaseFiniteLeftFarModes t a b =
      Complex.logarithmicPhasePoissonLeftInactiveModes t a b := by
  ext m
  constructor
  · intro hm
    have hcases := Finset.mem_union.mp hm
    match hcases with
    | Or.inl hnear =>
        exact
          ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
            t a b m).mp hnear).1
    | Or.inr hfar =>
        exact
          ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
            t a b m).mp hfar).1
  · intro hm
    have horder := le_total (a : ℝ)
      (Complex.logarithmicPhaseBProcessWindowRight t m)
    match horder with
    | Or.inl hnear =>
        exact Finset.mem_union_left _
          ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
            t a b m).mpr (And.intro hm hnear))
    | Or.inr hreverse =>
        match eq_or_lt_of_le hreverse with
        | Or.inl heq =>
            exact Finset.mem_union_left _
              ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
                t a b m).mpr (And.intro hm heq.symm.le))
        | Or.inr hfar =>
            exact Finset.mem_union_right _
              ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
                t a b m).mpr (And.intro hm hfar))

theorem Complex.logarithmicPhaseFiniteRightNear_union_far
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b ∪
        Complex.logarithmicPhaseFiniteRightFarModes t a b =
      Complex.logarithmicPhasePoissonRightInactiveModes t a b := by
  ext m
  constructor
  · intro hm
    have hcases := Finset.mem_union.mp hm
    match hcases with
    | Or.inl hnear =>
        exact
          ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
            t a b m).mp hnear).1
    | Or.inr hfar =>
        exact
          ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
            t a b m).mp hfar).1
  · intro hm
    have horder := le_total
      (Complex.logarithmicPhaseBProcessWindowLeft t m) (b : ℝ)
    match horder with
    | Or.inl hnear =>
        exact Finset.mem_union_left _
          ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
            t a b m).mpr (And.intro hm hnear))
    | Or.inr hreverse =>
        match eq_or_lt_of_le hreverse with
        | Or.inl heq =>
            exact Finset.mem_union_left _
              ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
                t a b m).mpr (And.intro hm heq.symm.le))
        | Or.inr hfar =>
            exact Finset.mem_union_right _
              ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
                t a b m).mpr (And.intro hm hfar))

theorem Complex.logarithmicPhaseFiniteLeftNear_clippedWindow_order
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    Complex.logarithmicPhaseBProcessClippedWindowLeft t a m ≤
      Complex.logarithmicPhaseBProcessClippedWindowRight t b m := by
  have hdata :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      t a b m).mp hm
  have hcenter :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hdata.1).2.2
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hdata.1).2.1
  have hleftWindow :
      Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (a : ℝ) := by
    unfold Complex.logarithmicPhaseBProcessWindowLeft
    have hradiusNonneg :=
      Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg
    exact le_trans (sub_le_self _ hradiusNonneg) hcenter.le
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  unfold Complex.logarithmicPhaseBProcessClippedWindowLeft
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  unfold Complex.logarithmicPhaseBProcessClippedWindowRight
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  have hmax : max (a : ℝ)
      (Complex.logarithmicPhaseBProcessWindowLeft t m) = (a : ℝ) :=
    max_eq_left hleftWindow
  have hminLower : (a : ℝ) ≤ min (b : ℝ)
      (Complex.logarithmicPhaseBProcessWindowRight t m) :=
    le_min habReal hdata.2
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hmax.symm hminLower

theorem Complex.logarithmicPhaseFiniteRightNear_clippedWindow_order
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    Complex.logarithmicPhaseBProcessClippedWindowLeft t a m ≤
      Complex.logarithmicPhaseBProcessClippedWindowRight t b m := by
  have hdata :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      t a b m).mp hm
  have hcenter :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hdata.1).2.2
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hdata.1).2.1
  have hrightWindow : (b : ℝ) ≤
      Complex.logarithmicPhaseBProcessWindowRight t m := by
    unfold Complex.logarithmicPhaseBProcessWindowRight
    exact le_trans hcenter.le
      (le_add_of_nonneg_right
        (Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg))
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  unfold Complex.logarithmicPhaseBProcessClippedWindowLeft
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  unfold Complex.logarithmicPhaseBProcessClippedWindowRight
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  have hmin : min (b : ℝ)
      (Complex.logarithmicPhaseBProcessWindowRight t m) = (b : ℝ) :=
    min_eq_left hrightWindow
  have hmaxUpper : max (a : ℝ)
      (Complex.logarithmicPhaseBProcessWindowLeft t m) ≤ (b : ℝ) :=
    max_le habReal hdata.2
  exact Eq.subst (motive := fun value : ℝ => _ ≤ value)
    hmin.symm hmaxUpper

end

end LFunctions
end Boundary
