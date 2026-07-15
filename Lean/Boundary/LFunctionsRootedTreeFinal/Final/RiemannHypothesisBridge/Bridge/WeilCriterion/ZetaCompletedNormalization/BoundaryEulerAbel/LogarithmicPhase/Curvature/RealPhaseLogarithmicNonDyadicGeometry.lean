import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUnconditionalLong

/-!
# Non-dyadic logarithmic long geometry

The all-interval curvature interface has the five analytic long hypotheses but
does not have dyadic endpoint comparability.  This owner records exactly that
weaker geometry and develops the frequency/endpoint regime split needed to
control mixed packet terms without introducing a comparability witness.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseGeneralLongGeometry
    (t : ℝ) (a b : ℕ) : Prop :=
  1 ≤ a ∧
    a ≤ b ∧
      a < b ∧
        Real.sqrt (1 + ‖t‖) <
          (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
        (((b + 1 : ℕ) : ℝ) / ‖t‖) <
          (((b + 1 : ℕ) : ℝ) - (a : ℝ))

def Real.logarithmicPhaseGeneralBlockLength
    (a b : ℕ) : ℝ :=
  (((b + 1 : ℕ) : ℝ) - (a : ℝ))

def Real.logarithmicPhaseGeneralEndpointRatio
    (t : ℝ) (b : ℕ) : ℝ :=
  ((b + 1 : ℕ) : ℝ) / ‖t‖

def Real.logarithmicPhaseGeneralRootScale
    (t : ℝ) : ℝ :=
  Real.sqrt (1 + ‖t‖)

def Real.logarithmicPhaseMixedEndpointScale
    (t : ℝ) (b : ℕ) : ℝ :=
  (b : ℝ) * Real.logarithmicPhaseGeneralRootScale t / ‖t‖

theorem Real.logarithmicPhaseGeneralBlockLength_eq_endpoint_difference
    (a b : ℕ) :
    Real.logarithmicPhaseGeneralBlockLength a b =
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  rfl

theorem Real.logarithmicPhaseGeneralEndpointRatio_eq_scaled_endpoint
    (t : ℝ) (b : ℕ) :
    Real.logarithmicPhaseGeneralEndpointRatio t b =
      (((b + 1 : ℕ) : ℝ) / ‖t‖) := by
  rfl

theorem Real.logarithmicPhaseGeneralRootScale_eq_phase_root
    (t : ℝ) :
    Real.logarithmicPhaseGeneralRootScale t = Real.sqrt (1 + ‖t‖) := by
  rfl

theorem Real.logarithmicPhaseMixedEndpointScale_eq_explicit
    (t : ℝ) (b : ℕ) :
    Real.logarithmicPhaseMixedEndpointScale t b =
      (b : ℝ) * Real.sqrt (1 + ‖t‖) / ‖t‖ := by
  unfold Real.logarithmicPhaseMixedEndpointScale
  exact congrArg
    (fun value : ℝ => (b : ℝ) * value / ‖t‖)
    (Real.logarithmicPhaseGeneralRootScale_eq_phase_root t)

theorem Real.logarithmicPhaseGeneralLongGeometry_root_explicit
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have hroot := h.2.2.2.1
  exact Eq.subst
    (motive := fun value : ℝ => value <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (Real.logarithmicPhaseGeneralRootScale_eq_phase_root t)
    hroot

theorem Real.logarithmicPhaseGeneralLongGeometry_endpoint_explicit
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have hendpoint := h.2.2.2.2
  exact Eq.subst
    (motive := fun value : ℝ => value <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (Real.logarithmicPhaseGeneralEndpointRatio_eq_scaled_endpoint t b)
    hendpoint

theorem Real.logarithmicPhaseGeneralLongGeometry_first
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    1 ≤ a :=
  h.1

theorem Real.logarithmicPhaseGeneralLongGeometry_order
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    a ≤ b :=
  h.2.1

theorem Real.logarithmicPhaseGeneralLongGeometry_strict
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    a < b :=
  h.2.2.1

theorem Real.logarithmicPhaseGeneralLongGeometry_root
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.logarithmicPhaseGeneralRootScale t <
      Real.logarithmicPhaseGeneralBlockLength a b :=
  h.2.2.2.1

theorem Real.logarithmicPhaseGeneralLongGeometry_endpoint
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.logarithmicPhaseGeneralEndpointRatio t b <
      Real.logarithmicPhaseGeneralBlockLength a b :=
  h.2.2.2.2

theorem Real.logarithmicPhaseGeneralLongGeometry_to_explicit_endpoint_hypotheses
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    1 ≤ a ∧
      a ≤ b ∧
        a < b ∧
          Real.sqrt (1 + ‖t‖) <
            (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
          (((b + 1 : ℕ) : ℝ) / ‖t‖) <
            (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have hfirst := Real.logarithmicPhaseGeneralLongGeometry_first h
  have horder := Real.logarithmicPhaseGeneralLongGeometry_order h
  have hstrict := Real.logarithmicPhaseGeneralLongGeometry_strict h
  have hroot := Real.logarithmicPhaseGeneralLongGeometry_root h
  have hendpoint := Real.logarithmicPhaseGeneralLongGeometry_endpoint h
  exact ⟨hfirst, horder, hstrict, hroot, hendpoint⟩

theorem Real.logarithmicPhaseGeneralLongGeometry_to_canonical_of_comparable
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b)
    (hcomparable : b + 1 ≤ 2 * a) :
    Real.logarithmicPhaseLongBranchGeometry t a b := by
  exact And.intro h.1
    (And.intro h.2.1
      (And.intro h.2.2.1
        (And.intro h.2.2.2.1
          (And.intro h.2.2.2.2 hcomparable))))

theorem Real.logarithmicPhaseLongBranchGeometry_to_explicit_endpoint_hypotheses
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseLongBranchGeometry t a b) :
    1 ≤ a ∧
      a ≤ b ∧
        a < b ∧
          Real.sqrt (1 + ‖t‖) <
            (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
          (((b + 1 : ℕ) : ℝ) / ‖t‖) <
            (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ∧
        b + 1 ≤ 2 * a := by
  have hfirst : 1 ≤ a := h.1
  have horder : a ≤ b := h.2.1
  have hstrict : a < b := h.2.2.1
  have hroot : Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := h.2.2.2.1
  have hendpoint : (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := h.2.2.2.2.1
  have hcomparable := Real.logarithmicPhaseLongBranchGeometry_comparable h
  exact ⟨hfirst, horder, hstrict, hroot, hendpoint, hcomparable⟩

theorem Real.logarithmicPhaseLongBranchGeometry_to_general
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Real.logarithmicPhaseGeneralLongGeometry t a b :=
  And.intro h.1
    (And.intro h.2.1
      (And.intro h.2.2.1
        (And.intro h.2.2.2.1 h.2.2.2.2.1)))

theorem Real.logarithmicPhaseGeneralLongGeometry_with_comparable
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b)
    (hcomparable : b + 1 ≤ 2 * a) :
    Real.logarithmicPhaseLongBranchGeometry t a b :=
  And.intro h.1
    (And.intro h.2.1
      (And.intro h.2.2.1
        (And.intro h.2.2.2.1
          (And.intro h.2.2.2.2 hcomparable))))

theorem Real.logarithmicPhaseGeneralBlockLength_pos
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    0 < Real.logarithmicPhaseGeneralBlockLength a b :=
  lt_trans
    (Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg t)))
    (Real.logarithmicPhaseGeneralLongGeometry_root h)

theorem Real.logarithmicPhaseGeneralBlockLength_le_succ
    (a b : ℕ) :
    Real.logarithmicPhaseGeneralBlockLength a b ≤ ((b + 1 : ℕ) : ℝ) := by
  unfold Real.logarithmicPhaseGeneralBlockLength
  exact sub_le_self _ (Nat.cast_nonneg a)

theorem Real.logarithmicPhaseGeneralBlockLength_le_b
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.logarithmicPhaseGeneralBlockLength a b ≤ (b : ℝ) := by
  unfold Real.logarithmicPhaseGeneralBlockLength
  have haCast : (1 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr h.1
  have hsub := sub_le_sub_left haCast ((b + 1 : ℕ) : ℝ)
  have hsuccCast : (((b + 1 : ℕ) : ℝ)) = (b : ℝ) + 1 := by
    exact Eq.trans (Nat.cast_add b 1)
      (congrArg (fun value : ℝ => (b : ℝ) + value) Nat.cast_one)
  have hright : (((b + 1 : ℕ) : ℝ)) - 1 = (b : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value - 1) hsuccCast)
      (add_sub_cancel_right (b : ℝ) 1)
  exact le_trans hsub (le_of_eq hright)

theorem Real.logarithmicPhaseGeneralRootScale_lt_b
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.logarithmicPhaseGeneralRootScale t < (b : ℝ) :=
  lt_of_lt_of_le
    (Real.logarithmicPhaseGeneralLongGeometry_root h)
    (Real.logarithmicPhaseGeneralBlockLength_le_b h)

theorem Real.logarithmicPhaseGeneralEndpointRatio_lt_b
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    Real.logarithmicPhaseGeneralEndpointRatio t b < (b : ℝ) :=
  lt_of_lt_of_le
    (Real.logarithmicPhaseGeneralLongGeometry_endpoint h)
    (Real.logarithmicPhaseGeneralBlockLength_le_b h)

theorem Real.logarithmicPhaseGeneralLongGeometry_b_pos
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    0 < (b : ℝ) :=
  lt_of_le_of_lt (Real.sqrt_nonneg _)
    (Real.logarithmicPhaseGeneralRootScale_lt_b h)

theorem Real.logarithmicPhaseGeneralLongGeometry_norm_pos
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (_h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    0 < ‖t‖ :=
  lt_of_lt_of_le zero_lt_one ht

theorem Real.logarithmicPhaseGeneralEndpointRatio_nonneg
    (t : ℝ) (b : ℕ) :
    0 ≤ Real.logarithmicPhaseGeneralEndpointRatio t b := by
  unfold Real.logarithmicPhaseGeneralEndpointRatio
  exact div_nonneg (Nat.cast_nonneg (b + 1)) (norm_nonneg t)

theorem Real.logarithmicPhaseGeneralRootScale_nonneg
    (t : ℝ) :
    0 ≤ Real.logarithmicPhaseGeneralRootScale t :=
  Real.sqrt_nonneg _

theorem Real.logarithmicPhaseGeneralRootScale_one_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    1 ≤ Real.logarithmicPhaseGeneralRootScale t := by
  unfold Real.logarithmicPhaseGeneralRootScale
  exact Real.logarithmicPhase_one_le_sqrt_one_add_norm t ht

theorem Real.logarithmicPhaseGeneralRootScale_sq
    (t : ℝ) :
    Real.logarithmicPhaseGeneralRootScale t ^ 2 = 1 + ‖t‖ := by
  unfold Real.logarithmicPhaseGeneralRootScale
  exact Real.sq_sqrt (add_nonneg zero_le_one (norm_nonneg t))

theorem Real.logarithmicPhaseGeneralRootScale_sq_ge_norm
    (t : ℝ) :
    ‖t‖ ≤ Real.logarithmicPhaseGeneralRootScale t ^ 2 := by
  exact Eq.subst
    (motive := fun value : ℝ => ‖t‖ ≤ value)
    (Real.logarithmicPhaseGeneralRootScale_sq t).symm
    (le_add_of_nonneg_left zero_le_one)

theorem Real.logarithmicPhaseGeneral_frequency_regime
    (t : ℝ) (b : ℕ) :
    ((b : ℝ) ≤ ‖t‖) ∨ (‖t‖ < (b : ℝ)) :=
  le_or_gt (b : ℝ) ‖t‖

theorem Real.logarithmicPhaseGeneral_endpointRatio_le_one_of_highFrequency
    {t : ℝ} {b : ℕ}
    (htPos : 0 < ‖t‖)
    (hhigh : ((b + 1 : ℕ) : ℝ) ≤ ‖t‖) :
    Real.logarithmicPhaseGeneralEndpointRatio t b ≤ 1 := by
  unfold Real.logarithmicPhaseGeneralEndpointRatio
  exact (div_le_one htPos).mpr hhigh

theorem Real.logarithmicPhaseMixedEndpointScale_eq_b_mul_endpointRoot
    (t : ℝ) (b : ℕ) :
    Real.logarithmicPhaseMixedEndpointScale t b =
      ((b : ℝ) / ‖t‖) * Real.logarithmicPhaseGeneralRootScale t := by
  unfold Real.logarithmicPhaseMixedEndpointScale
  exact Eq.trans (mul_div_assoc (b : ℝ)
    (Real.logarithmicPhaseGeneralRootScale t) ‖t‖)
    (Eq.trans
      (congrArg
        (fun value : ℝ => value / ‖t‖)
        (mul_comm (b : ℝ) (Real.logarithmicPhaseGeneralRootScale t)))
      (div_mul_eq_mul_div
        (Real.logarithmicPhaseGeneralRootScale t) (b : ℝ) ‖t‖))

theorem Real.b_div_norm_le_generalEndpointRatio
    (t : ℝ) (b : ℕ) (htPos : 0 < ‖t‖) :
    (b : ℝ) / ‖t‖ ≤
      Real.logarithmicPhaseGeneralEndpointRatio t b := by
  unfold Real.logarithmicPhaseGeneralEndpointRatio
  have hb : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.le_succ b)
  exact div_le_div_of_nonneg_right hb htPos.le

theorem Real.logarithmicPhaseMixedEndpointScale_le_endpoint_mul_root
    (t : ℝ) (b : ℕ) (htPos : 0 < ‖t‖) :
    Real.logarithmicPhaseMixedEndpointScale t b ≤
      Real.logarithmicPhaseGeneralEndpointRatio t b *
        Real.logarithmicPhaseGeneralRootScale t := by
  have hquotient := Real.b_div_norm_le_generalEndpointRatio t b htPos
  have hmul := mul_le_mul_of_nonneg_right hquotient
    (Real.logarithmicPhaseGeneralRootScale_nonneg t)
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ _)
    (Real.logarithmicPhaseMixedEndpointScale_eq_b_mul_endpointRoot t b).symm
    hmul

theorem Real.product_le_add_of_left_le_one
    {x y : ℝ}
    (hx : 0 ≤ x) (hxOne : x ≤ 1) (hy : 0 ≤ y) :
    x * y ≤ x + y := by
  have hxy := mul_le_mul_of_nonneg_right hxOne hy
  have hyLe : x * y ≤ y :=
    Eq.subst (motive := fun value : ℝ => x * y ≤ value)
      (one_mul y).symm hxy
  exact le_trans hyLe (le_add_of_nonneg_left hx)

theorem Real.product_le_add_of_right_le_one
    {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyOne : y ≤ 1) :
    x * y ≤ x + y := by
  have hxy := mul_le_mul_of_nonneg_left hyOne hx
  have hxLe : x * y ≤ x :=
    Eq.subst (motive := fun value : ℝ => x * y ≤ value)
      (mul_one x).symm hxy
  exact le_trans hxLe (le_add_of_nonneg_right hy)

theorem Real.logarithmicPhaseMixedEndpointScale_le_target_of_endpointRatio_le_one
    (t : ℝ) (b : ℕ) (htPos : 0 < ‖t‖)
    (hratio : Real.logarithmicPhaseGeneralEndpointRatio t b ≤ 1) :
    Real.logarithmicPhaseMixedEndpointScale t b ≤
      Real.logarithmicPhaseGeneralEndpointRatio t b +
        Real.logarithmicPhaseGeneralRootScale t := by
  exact le_trans
    (Real.logarithmicPhaseMixedEndpointScale_le_endpoint_mul_root
      t b htPos)
    (Real.product_le_add_of_left_le_one
      (Real.logarithmicPhaseGeneralEndpointRatio_nonneg t b)
      hratio
      (Real.logarithmicPhaseGeneralRootScale_nonneg t))

theorem Real.logarithmicPhaseGeneral_nonDyadic_regime
    (t : ℝ) (b : ℕ) :
    (Real.logarithmicPhaseGeneralEndpointRatio t b ≤ 1) ∨
      (1 < Real.logarithmicPhaseGeneralEndpointRatio t b) :=
  le_or_gt (Real.logarithmicPhaseGeneralEndpointRatio t b) 1

theorem Real.logarithmicPhaseGeneral_target_nonneg
    (t : ℝ) (b : ℕ) :
    0 ≤ Real.logarithmicPhaseGeneralEndpointRatio t b +
      Real.logarithmicPhaseGeneralRootScale t :=
  add_nonneg
    (Real.logarithmicPhaseGeneralEndpointRatio_nonneg t b)
    (Real.logarithmicPhaseGeneralRootScale_nonneg t)

theorem Real.logarithmicPhaseGeneral_target_one_le
    (t : ℝ) (b : ℕ) (ht : 1 ≤ ‖t‖) :
    1 ≤ Real.logarithmicPhaseGeneralEndpointRatio t b +
      Real.logarithmicPhaseGeneralRootScale t :=
  le_trans
    (Real.logarithmicPhaseGeneralRootScale_one_le t ht)
    (le_add_of_nonneg_left
      (Real.logarithmicPhaseGeneralEndpointRatio_nonneg t b))

theorem Real.logarithmicPhaseGeneralGeometry_dyadic_or_wide
    {t : ℝ} {a b : ℕ}
    (_h : Real.logarithmicPhaseGeneralLongGeometry t a b) :
    (b + 1 ≤ 2 * a) ∨ (2 * a < b + 1) :=
  le_or_gt (b + 1) (2 * a)

theorem Real.logarithmicPhaseGeneralGeometry_to_dyadic_in_first_regime
    {t : ℝ} {a b : ℕ}
    (h : Real.logarithmicPhaseGeneralLongGeometry t a b)
    (hdyadic : b + 1 ≤ 2 * a) :
    Real.logarithmicPhaseLongBranchGeometry t a b :=
  Real.logarithmicPhaseGeneralLongGeometry_with_comparable h hdyadic

theorem Complex.logarithmicPhaseRealPhase_generalLongGeometry_dyadic_norm_le_unconditional
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseGeneralLongGeometry t a b)
    (hdyadic : b + 1 ≤ 2 * a) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  have hcanonical :=
    Real.logarithmicPhaseGeneralGeometry_to_dyadic_in_first_regime
      hgeometry hdyadic
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hcanonical
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hcanonical
  have hstrict := Real.logarithmicPhaseLongBranchGeometry_strict hcanonical
  have hsqrt := Real.logarithmicPhaseLongBranchGeometry_sqrt hcanonical
  have hendpoint := Real.logarithmicPhaseLongBranchGeometry_endpoint hcanonical
  have hcomparable :=
    Real.logarithmicPhaseLongBranchGeometry_comparable hcanonical
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_of_explicit_geometry
      t ht_nonneg ht a b ha hab hstrict hsqrt hendpoint hcomparable

end

end LFunctions
end Boundary
