import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.SharpCenterFrequencyWidth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteActiveBudget

/-!
# Two-sided packing of balanced endpoint modes

The four geometric endpoint subclasses form only two frequency layers: one at
the left block endpoint and one at the right.  Outside and clipped modes on a
fixed side occupy adjacent center intervals, so their union is transported
through one sharp center-frequency interval.  This file isolates that packing
structure and reduces the endpoint cardinality to two explicit angular-width
inequalities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ∪
    Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b

def Complex.logarithmicPhasePoissonBProcessRightEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ∪
    Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b

theorem Complex.mem_logarithmicPhasePoissonBProcessLeftEndpointModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ∨
        m ∈ Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b := by
  exact Finset.mem_union

theorem Complex.mem_logarithmicPhasePoissonBProcessRightEndpointModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ∨
        m ∈ Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b := by
  exact Finset.mem_union

theorem Complex.logarithmicPhaseBProcessLeftClipped_a_lt_centerUpper
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a : ℤ} (ha : 1 ≤ a) :
    (a : ℝ) < Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a := by
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hsubPos := Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht
  unfold Complex.logarithmicPhaseBProcessLeftClippedCenterUpper
  have htarget :
      (a : ℝ) * (Complex.logarithmicPhaseBProcessScale t - 1) <
        (a : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact mul_lt_mul_of_pos_left
      (sub_lt_self
        (Complex.logarithmicPhaseBProcessScale t) zero_lt_one)
      haPos
  exact (lt_div_iff₀ hsubPos).mpr htarget

theorem Complex.logarithmicPhaseBProcessRightClipped_centerLower_lt_b
    (t : ℝ) {b : ℤ} (hb : 1 ≤ b) :
    Complex.logarithmicPhaseBProcessRightClippedCenterLower t b < (b : ℝ) := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have haddPos := Complex.logarithmicPhaseBProcessScale_add_one_pos t
  unfold Complex.logarithmicPhaseBProcessRightClippedCenterLower
  have htarget :
      (b : ℝ) * S < (b : ℝ) * (S + 1) :=
    mul_lt_mul_of_pos_left (lt_add_of_pos_right S zero_lt_one) hbPos
  exact (div_lt_iff₀ haddPos).mpr htarget

theorem Complex.logarithmicPhaseBProcessLeftEndpoint_center_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b) :
    Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftEndpointModes_iff
      t a b m).mp hm
  match hclass with
  | Or.inl houtside =>
      have hbounds :=
        Complex.logarithmicPhaseBProcessLeftOutside_center_bounds
          t a b houtside
      have haUpper :=
        (Complex.logarithmicPhaseBProcessLeftClipped_a_lt_centerUpper
          t ht ha).le
      exact And.intro hbounds.1 (le_trans hbounds.2 haUpper)
  | Or.inr hclipped =>
      have hdata :=
        (Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
          t a b m).mp hclipped
      have hmargin :
          Real.integerBlockCutoffSupportLeftEndpoint a ≤ (a : ℝ) := by
        unfold Real.integerBlockCutoffSupportLeftEndpoint
        have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
        have hthreeNonneg : (0 : ℝ) ≤ 3 := Nat.cast_nonneg 3
        exact sub_le_self _
          (div_nonneg htwoNonneg hthreeNonneg)
      have hupper :=
        Complex.logarithmicPhaseBProcessLeftClipped_center_lt_upper
          t ht hdata.2.2.2
      exact And.intro (le_trans hmargin hdata.2.1) hupper.le

theorem Complex.logarithmicPhaseBProcessRightEndpoint_center_bounds
    (t : ℝ) (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b) :
    Complex.logarithmicPhaseBProcessRightClippedCenterLower t b ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m ∧
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightEndpointModes_iff
      t a b m).mp hm
  match hclass with
  | Or.inl houtside =>
      have hbounds :=
        Complex.logarithmicPhaseBProcessRightOutside_center_bounds
          t a b houtside
      have hlowerB :=
        (Complex.logarithmicPhaseBProcessRightClipped_centerLower_lt_b
          t hb).le
      exact And.intro (le_trans hlowerB hbounds.1) hbounds.2
  | Or.inr hclipped =>
      have hdata :=
        (Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
          t a b m).mp hclipped
      have hlower :=
        Complex.logarithmicPhaseBProcessRightClipped_lower_lt_center
          t hdata.2.2.2
      have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
      have hthreeNonneg : (0 : ℝ) ≤ 3 := Nat.cast_nonneg 3
      have hmargin : (b : ℝ) ≤ (b : ℝ) + 2 / 3 :=
        le_add_of_nonneg_right
          (div_nonneg htwoNonneg hthreeNonneg)
      exact And.intro hlower.le (le_trans hdata.2.2.1 hmargin)

theorem Complex.logarithmicPhaseBProcessLeftEndpoint_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t
        (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t a) ≤
        -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseCenterFrequencyCoordinate t
          (Real.integerBlockCutoffSupportLeftEndpoint a) := by
  have hbounds :=
    Complex.logarithmicPhaseBProcessLeftEndpoint_center_bounds
      t ht a b ha hm
  have hleftPos :=
    Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hendpoint :=
    ((Complex.mem_logarithmicPhasePoissonBProcessLeftEndpointModes_iff
      t a b m).mp hm)
  have hmEndpoint :
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
    match hendpoint with
    | Or.inl h =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
          t a b m).mp h).1
    | Or.inr h =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
          t a b m).mp h).1
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hmEndpoint
  exact Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
    t ht hmNeg hleftPos hbounds.1 hbounds.2

theorem Complex.logarithmicPhaseBProcessRightEndpoint_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t ((b : ℝ) + 2 / 3) ≤
        -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseCenterFrequencyCoordinate t
          (Complex.logarithmicPhaseBProcessRightClippedCenterLower t b) := by
  have hbounds :=
    Complex.logarithmicPhaseBProcessRightEndpoint_center_bounds
      t a b hb hm
  have hleftPos :=
    Complex.logarithmicPhaseBProcessRightClipped_lower_pos t hb
  have hendpoint :=
    ((Complex.mem_logarithmicPhasePoissonBProcessRightEndpointModes_iff
      t a b m).mp hm)
  have hmEndpoint :
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
    match hendpoint with
    | Or.inl h =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
          t a b m).mp h).1
    | Or.inr h =>
        exact ((Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
          t a b m).mp h).1
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hmEndpoint
  exact Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
    t ht hmNeg hleftPos hbounds.1 hbounds.2

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_sideUnion
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessEndpointModes t a b ⊆
      Complex.logarithmicPhasePoissonBProcessLeftEndpointModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightEndpointModes t a b := by
  intro m hm
  have hpartition :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_partition
      t a b hm
  match hpartition with
  | Or.inl hleftOutside =>
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ hleftOutside)
  | Or.inr (Or.inl hrightOutside) =>
      exact Finset.mem_union_right _
        (Finset.mem_union_left _ hrightOutside)
  | Or.inr (Or.inr (Or.inl hleftClipped)) =>
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ hleftClipped)
  | Or.inr (Or.inr (Or.inr hrightClipped)) =>
      exact Finset.mem_union_right _
        (Finset.mem_union_right _ hrightClipped)

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two_of_side_widths
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hleftAngular :
      ‖t‖ *
          (Complex.logarithmicPhaseBProcessLeftClippedCenterUpper t (a : ℤ) -
            Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) <
        (2 * Real.pi) *
          (Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ^ 2)
    (hrightAngular :
      ‖t‖ *
          (((b : ℝ) + 2 / 3) -
            Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) <
        (2 * Real.pi) *
          (Complex.logarithmicPhaseBProcessRightClippedCenterLower t (b : ℤ)) ^ 2) :
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 2 := by
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hb : (1 : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry)
  have hleftPos := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hthreeNonneg : (0 : ℝ) ≤ 3 := Nat.cast_nonneg 3
  have hleftOrder := le_trans
    (sub_le_self (a : ℝ)
      (div_nonneg htwoNonneg hthreeNonneg))
    (Complex.logarithmicPhaseBProcessLeftClipped_a_lt_centerUpper
      t ht ha).le
  have hrightPos :=
    Complex.logarithmicPhaseBProcessRightClipped_lower_pos t hb
  have hrightOrder := le_trans
    (Complex.logarithmicPhaseBProcessRightClipped_centerLower_lt_b t hb).le
    (le_add_of_nonneg_right
      (div_nonneg htwoNonneg hthreeNonneg))
  have hleftCard :=
    Complex.integerModeFamily_card_le_one_of_center_bounds
      t (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
        t (a : ℤ) (b : ℤ))
      hleftPos hleftOrder hleftAngular
      (fun m hm =>
        Complex.logarithmicPhaseBProcessLeftEndpoint_negModeCast_bounds
          t ht (a : ℤ) (b : ℤ) ha hm)
  have hrightCard :=
    Complex.integerModeFamily_card_le_one_of_center_bounds
      t (Complex.logarithmicPhasePoissonBProcessRightEndpointModes
        t (a : ℤ) (b : ℤ))
      hrightPos hrightOrder hrightAngular
      (fun m hm =>
        Complex.logarithmicPhaseBProcessRightEndpoint_negModeCast_bounds
          t ht (a : ℤ) (b : ℤ) hb hm)
  have hsubsetCard := Finset.card_le_card
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_sideUnion
      t (a : ℤ) (b : ℤ))
  have hunionCard := Finset.card_union_le
    (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessRightEndpointModes
      t (a : ℤ) (b : ℤ))
  have hadd :
      (Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
          t (a : ℤ) (b : ℤ)).card +
        (Complex.logarithmicPhasePoissonBProcessRightEndpointModes
          t (a : ℤ) (b : ℤ)).card ≤ 1 + 1 :=
    Nat.add_le_add hleftCard hrightCard
  have hsumCard :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).card ≤ 1 + 1 :=
    le_trans hsubsetCard (le_trans hunionCard hadd)
  have honeAddOne : (1 : ℕ) + 1 = 2 := rfl
  exact Eq.subst
    (motive := fun value : ℕ =>
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).card ≤ value)
    honeAddOne hsumCard

end

end LFunctions
end Boundary
