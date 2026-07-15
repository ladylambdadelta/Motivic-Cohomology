import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUniversalEndpointArithmetic

/-!
# Complete single-counted active B-process budget

The active family is the disjoint union of balanced interior modes and the
endpoint remainder.  This owner assigns the stationary majorant on the first
piece and the universal clipped majorant on the second, then proves the exact
finite-sum decomposition and the complete active packet bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  if m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b then
    Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m
  else
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m

def Complex.logarithmicPhaseBProcessCompleteActiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessInteriorBudget t a b +
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget t a b

theorem Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_interior
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessCompleteActivePacketBudget t a b m =
      Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m := by
  unfold Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
  exact if_pos hm

theorem Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_endpoint
    (t : ℝ) (a b m : ℤ)
    (hm : m ∉ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    Complex.logarithmicPhaseBProcessCompleteActivePacketBudget t a b m =
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m := by
  unfold Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
  exact if_neg hm

theorem Complex.logarithmicPhasePoissonActiveMode_mem_interior_or_endpoint
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonActiveModes t a b) :
    m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ∨
      m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b := by
  have hunion :=
    Complex.logarithmicPhasePoissonBProcessInterior_union_endpoint_eq_active
      t ht a b
  have hmUnion :
      m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessEndpointModes t a b :=
    Eq.subst (motive := fun modes : Finset ℤ => m ∈ modes)
      hunion.symm hm
  exact Finset.mem_union.mp hmUnion

theorem Complex.logarithmicPhasePoissonEndpointMode_not_interior
    (t : ℝ) (a b : ℤ) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    m ∉ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b := by
  have hdisjoint :=
    Complex.logarithmicPhasePoissonBProcessInterior_disjoint_endpoint t a b
  exact fun hinterior =>
    Finset.disjoint_left.mp hdisjoint hinterior hm

theorem Complex.norm_activeMode_integerBlockFourierPacket_le_completeBudget
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonActiveModes
      t (a : ℤ) (b : ℤ)) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
        t (a : ℤ) (b : ℤ) m := by
  have hpartition :=
    Complex.logarithmicPhasePoissonActiveMode_mem_interior_or_endpoint
      t ht (a : ℤ) (b : ℤ) hm
  match hpartition with
  | Or.inl hinterior =>
      have ha : (1 : ℤ) ≤ (a : ℤ) :=
        Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
      have hab : (a : ℤ) ≤ (b : ℤ) :=
        Int.ofNat_le.mpr
          (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
      have hpacket :=
        Complex.norm_integerBlockFourierPacket_le_BProcessStationaryMajorant
          t ht ht_nonneg (a : ℤ) (b : ℤ) m ha hab hinterior
      exact hpacket.trans_eq
        (Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_interior
          t (a : ℤ) (b : ℤ) m hinterior).symm
  | Or.inr hendpoint =>
      have hpacket :=
        Complex.norm_endpointMode_integerBlockFourierPacket_le_universalBudget
          ht ht_nonneg hgeometry hendpoint
      have hnotInterior :=
        Complex.logarithmicPhasePoissonEndpointMode_not_interior
          t (a : ℤ) (b : ℤ) hendpoint
      exact hpacket.trans_eq
        (Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_endpoint
          t (a : ℤ) (b : ℤ) m hnotInterior).symm

theorem Complex.sum_completeActivePacketBudget_eq_completeActiveBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    (∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
      Complex.logarithmicPhaseBProcessCompleteActivePacketBudget t a b m) =
      Complex.logarithmicPhaseBProcessCompleteActiveBudget t a b := by
  let interior :=
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b
  let endpoint :=
    Complex.logarithmicPhasePoissonBProcessEndpointModes t a b
  let budget :=
    Complex.logarithmicPhaseBProcessCompleteActivePacketBudget t a b
  have hunion :=
    Complex.logarithmicPhasePoissonBProcessInterior_union_endpoint_eq_active
      t ht a b
  have hdisjoint :=
    Complex.logarithmicPhasePoissonBProcessInterior_disjoint_endpoint t a b
  have hsplit :
      ∑ m ∈ interior ∪ endpoint, budget m =
        (∑ m ∈ interior, budget m) + ∑ m ∈ endpoint, budget m :=
    Finset.sum_union hdisjoint
  have hinteriorPoint :
      ∀ m ∈ interior,
        budget m = Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m :=
    fun m hm =>
      Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_interior
        t a b m hm
  have hendpointPoint :
      ∀ m ∈ endpoint,
        budget m =
          Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget t a b m :=
    fun m hm =>
      Complex.logarithmicPhaseBProcessCompleteActivePacketBudget_eq_endpoint
        t a b m
        (Complex.logarithmicPhasePoissonEndpointMode_not_interior t a b hm)
  have hinteriorSum :
      (∑ m ∈ interior, budget m) =
        Complex.logarithmicPhaseBProcessInteriorBudget t a b := by
    have hpoint := Finset.sum_congr rfl hinteriorPoint
    exact hpoint.trans
      (Complex.sum_logarithmicPhaseBProcessStationaryPacketMajorant_eq_budget
        t a b)
  have hendpointSum :
      (∑ m ∈ endpoint, budget m) =
        Complex.logarithmicPhaseBProcessUniversalEndpointBudget t a b := by
    unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
    exact Finset.sum_congr rfl hendpointPoint
  have hactiveToUnion :
      (∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b, budget m) =
        ∑ m ∈ interior ∪ endpoint, budget m := by
    exact Finset.sum_congr hunion.symm (fun m hm => rfl)
  unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
  exact hactiveToUnion.trans
    (hsplit.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hinteriorSum hendpointSum))

theorem Complex.norm_logarithmicPhaseCompleteActive_packet_tsum_le_budget
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonActiveModes
          t (a : ℤ) (b : ℤ)},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (a : ℤ) (b : ℤ) m‖ ≤
      Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) := by
  have hmajorant :=
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t (a : ℤ) (b : ℤ)
      (Complex.logarithmicPhasePoissonActiveModes
        t (a : ℤ) (b : ℤ))
      (Complex.logarithmicPhaseBProcessCompleteActivePacketBudget
        t (a : ℤ) (b : ℤ))
      (fun m hm =>
        Complex.norm_activeMode_integerBlockFourierPacket_le_completeBudget
          ht ht_nonneg hgeometry hm)
  exact hmajorant.trans_eq
    (Complex.sum_completeActivePacketBudget_eq_completeActiveBudget
      t ht (a : ℤ) (b : ℤ))

theorem Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_interior_add_four_endpoint
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseBProcessInteriorBudget t (a : ℤ) (b : ℤ) +
        4 * Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
          t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessCompleteActiveBudget
  exact add_le_add_left
    (Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_four_perModeMajorant
      ht hgeometry)
    (Complex.logarithmicPhaseBProcessInteriorBudget t (a : ℤ) (b : ℤ))

end

end LFunctions
end Boundary
