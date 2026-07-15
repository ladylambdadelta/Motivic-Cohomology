import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveHybridBudget

/-!
# Exact decomposition of the finite far-inactive budget

The monotone endpoint estimate has two logically separate pieces.  Each packet
pays the exact quantitative-cutoff crossing charge `2/3`; its principal
oscillatory integral pays twice the reciprocal endpoint derivative gap.  This
owner separates the cardinality and reciprocal-series channels before any
coarse arithmetic is performed.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b, (2 / 3 : ℝ)

def Complex.logarithmicPhaseFiniteRightFarCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ _m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b, (2 / 3 : ℝ)

def Complex.logarithmicPhaseFiniteFarCrossingBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b +
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b

def Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b,
    (Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ))

def Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b,
    (Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ))

def Complex.logarithmicPhaseFiniteFarReciprocalBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b +
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b

def Complex.logarithmicPhaseFiniteFarSeparatedBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteFarCrossingBudget t a b +
    Complex.logarithmicPhaseFiniteFarReciprocalBudget t a b

theorem Complex.logarithmicPhaseFiniteLeftFarPacketBudget_eq_crossing_add_reciprocal
    (t : ℝ) (a m : ℤ) :
    Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m =
      (2 / 3 : ℝ) +
        (Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
          Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)) := by
  unfold Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget
  exact add_assoc _ _ _

theorem Complex.logarithmicPhaseFiniteRightFarPacketBudget_eq_crossing_add_reciprocal
    (t : ℝ) (b m : ℤ) :
    Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m =
      (2 / 3 : ℝ) +
        (Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
          Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)) := by
  unfold Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget
  exact add_assoc _ _ _

theorem Complex.logarithmicPhaseFiniteLeftFarBudget_eq_crossing_add_reciprocal
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFarBudget t a b =
      Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b +
        Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b := by
  let modes := Complex.logarithmicPhaseFiniteLeftFarModes t a b
  let crossing : ℤ → ℝ := fun _m => (2 / 3 : ℝ)
  let reciprocal : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)
  have hpoint : ∀ m ∈ modes,
      Complex.logarithmicPhaseFiniteLeftPrincipalEndpointPacketBudget t a m =
        crossing m + reciprocal m :=
    fun m hm =>
      Complex.logarithmicPhaseFiniteLeftFarPacketBudget_eq_crossing_add_reciprocal
        t a m
  have hcongr := Finset.sum_congr rfl hpoint
  have hsplit := Finset.sum_add_distrib
    (s := modes) (f := crossing) (g := reciprocal)
  unfold Complex.logarithmicPhaseFiniteLeftFarBudget
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Eq.trans hcongr hsplit

theorem Complex.logarithmicPhaseFiniteRightFarBudget_eq_crossing_add_reciprocal
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteRightFarBudget t a b =
      Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b := by
  let modes := Complex.logarithmicPhaseFiniteRightFarModes t a b
  let crossing : ℤ → ℝ := fun _m => (2 / 3 : ℝ)
  let reciprocal : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
      Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)
  have hpoint : ∀ m ∈ modes,
      Complex.logarithmicPhaseFiniteRightPrincipalEndpointPacketBudget t b m =
        crossing m + reciprocal m :=
    fun m hm =>
      Complex.logarithmicPhaseFiniteRightFarPacketBudget_eq_crossing_add_reciprocal
        t b m
  have hcongr := Finset.sum_congr rfl hpoint
  have hsplit := Finset.sum_add_distrib
    (s := modes) (f := crossing) (g := reciprocal)
  unfold Complex.logarithmicPhaseFiniteRightFarBudget
  unfold Complex.logarithmicPhaseFiniteRightFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
  exact Eq.trans hcongr hsplit

theorem Complex.logarithmicPhaseFiniteFarBudgets_eq_separatedBudget
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFarBudget t a b +
        Complex.logarithmicPhaseFiniteRightFarBudget t a b =
      Complex.logarithmicPhaseFiniteFarSeparatedBudget t a b := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftFarBudget_eq_crossing_add_reciprocal
      t a b
  have hright :=
    Complex.logarithmicPhaseFiniteRightFarBudget_eq_crossing_add_reciprocal
      t a b
  unfold Complex.logarithmicPhaseFiniteFarSeparatedBudget
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  exact Eq.trans (congrArg₂ (fun x y : ℝ => x + y) hleft hright)
    (add_add_add_comm _ _ _ _)

theorem Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_eq_card_mul
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b =
      ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) *
        (2 / 3 : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  exact (Finset.sum_const (2 / 3 : ℝ)).trans
    (nsmul_eq_mul
      (Complex.logarithmicPhaseFiniteLeftFarModes t a b).card (2 / 3 : ℝ))

theorem Complex.logarithmicPhaseFiniteRightFarCrossingBudget_eq_card_mul
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b =
      ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) *
        (2 / 3 : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteRightFarCrossingBudget
  exact (Finset.sum_const (2 / 3 : ℝ)).trans
    (nsmul_eq_mul
      (Complex.logarithmicPhaseFiniteRightFarModes t a b).card (2 / 3 : ℝ))

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_eq_card_sum_mul
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget t a b =
      (((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) +
          ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ)) *
        (2 / 3 : ℝ) := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_eq_card_mul t a b
  have hright :=
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget_eq_card_mul t a b
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  exact Eq.trans (congrArg₂ (fun x y : ℝ => x + y) hleft hright)
    (add_mul _ _ _).symm

theorem Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftFarCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  exact Finset.sum_nonneg (fun m hm =>
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))

theorem Complex.logarithmicPhaseFiniteRightFarCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseFiniteRightFarCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteRightFarCrossingBudget
  exact Finset.sum_nonneg (fun m hm =>
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseFiniteFarCrossingBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  exact add_nonneg
    (Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_nonneg t a b)
    (Complex.logarithmicPhaseFiniteRightFarCrossingBudget_nonneg t a b)

theorem Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Finset.sum_nonneg (fun m hm => by
    have hbase :=
      ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff t a b m).mp hm).1
    have hdata :=
      (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
        t a b m).mp hbase
    have haPos : 0 < (a : ℝ) :=
      Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
    have hgap := Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
      t ht m hdata.2.1 haPos hdata.2.2
    have hnonneg :
        0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) :=
      Eq.subst (motive := fun value : ℝ => 0 ≤ value)
        hgap.symm (norm_nonneg _)
    exact add_nonneg hnonneg hnonneg)

theorem Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightFarReciprocalBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
  exact Finset.sum_nonneg (fun m hm => by
    have hbase :=
      ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff t a b m).mp hm).1
    have hdata :=
      (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
        t a b m).mp hbase
    have hb : 1 ≤ b := le_trans ha hab
    have hbPos : 0 < (b : ℝ) :=
      Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
    have hgap := Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
      t ht m hdata.2.1 hbPos hdata.2.2
    have hnonneg :
        0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) :=
      Eq.subst (motive := fun value : ℝ => 0 ≤ value)
        hgap.symm (norm_nonneg _)
    exact add_nonneg hnonneg hnonneg)

theorem Complex.logarithmicPhaseFiniteFarReciprocalBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteFarReciprocalBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  exact add_nonneg
    (Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_nonneg
      t ht a b ha)
    (Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_nonneg
      t ht a b ha hab)

theorem Complex.logarithmicPhaseFiniteFarSeparatedBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteFarSeparatedBudget t a b := by
  unfold Complex.logarithmicPhaseFiniteFarSeparatedBudget
  exact add_nonneg
    (Complex.logarithmicPhaseFiniteFarCrossingBudget_nonneg t a b)
    (Complex.logarithmicPhaseFiniteFarReciprocalBudget_nonneg
      t ht a b ha hab)

end

end LFunctions
end Boundary
