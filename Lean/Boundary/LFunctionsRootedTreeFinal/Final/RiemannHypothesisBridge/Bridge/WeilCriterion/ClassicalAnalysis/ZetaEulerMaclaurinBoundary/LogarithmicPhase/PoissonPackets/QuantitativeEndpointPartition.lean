import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeEndpointPackets

/-!
# Exact center-location partition of endpoint-active modes

Support-active endpoint modes separate according to whether their stationary
center lies left of the principal block, inside it, or right of it.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).filter
    (fun m : ℤ =>
      Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ))

def Complex.logarithmicPhaseQuantitativeEndpointInternalModes
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).filter
    (fun m : ℤ =>
      Complex.logarithmicPhaseFourierStationaryPoint t m ∈ Set.Icc (a : ℝ) (b : ℝ))

def Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius).filter
    (fun m : ℤ =>
      (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m)

theorem Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
    (t : ℝ)
    (a b m : ℤ)
    (radius : ℝ) :
    m ∈ Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius ↔
      m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
    (t : ℝ)
    (a b m : ℤ)
    (radius : ℝ) :
    m ∈ Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius ↔
      m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointInternalModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseQuantitativeEndpointRightCollarModes_iff
    (t : ℝ)
    (a b m : ℤ)
    (radius : ℝ) :
    m ∈ Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius ↔
      m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius ∧
        (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes
  exact Finset.mem_filter

theorem Complex.logarithmicPhaseQuantitativeEndpointLocation_union_eq_endpoint
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ)
    (hab : a ≤ b) :
    (Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius ∪
        Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius) ∪
      Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius =
        Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius := by
  exact
    Finset.Subset.antisymm
      (fun m hm =>
        match Finset.mem_union.mp hm with
        | Or.inl hleft_internal =>
            match Finset.mem_union.mp hleft_internal with
            | Or.inl hleft =>
                have hdata :=
                  (Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
                    t a b m radius).mp hleft
                hdata.1
            | Or.inr hinternal =>
                have hdata :=
                  (Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
                    t a b m radius).mp hinternal
                hdata.1
        | Or.inr hright =>
            have hdata :=
              (Complex.mem_logarithmicPhaseQuantitativeEndpointRightCollarModes_iff
                t a b m radius).mp hright
            hdata.1)
      (fun m hm =>
        let center := Complex.logarithmicPhaseFourierStationaryPoint t m
        match lt_or_ge center (a : ℝ) with
        | Or.inl hleft =>
            Finset.mem_union_left _
              (Finset.mem_union_left _
                ((Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
                  t a b m radius).mpr ⟨hm, hleft⟩))
        | Or.inr hnot_left =>
            match lt_or_ge (b : ℝ) center with
            | Or.inl hright =>
                Finset.mem_union_right _
                  ((Complex.mem_logarithmicPhaseQuantitativeEndpointRightCollarModes_iff
                    t a b m radius).mpr ⟨hm, hright⟩)
            | Or.inr hnot_right =>
                have hcenter : center ∈ Set.Icc (a : ℝ) (b : ℝ) :=
                  ⟨hnot_left, hnot_right⟩
                Finset.mem_union_left _
                  (Finset.mem_union_right _
                    ((Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
                      t a b m radius).mpr ⟨hm, hcenter⟩)))

theorem Complex.logarithmicPhaseQuantitativeEndpointLeft_disjoint_internal
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ) :
    Disjoint
      (Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius)
      (Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius) := by
  exact
    Finset.disjoint_left.mpr
      (fun m hleft hinternal =>
        have hleft_data :=
          (Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
            t a b m radius).mp hleft
        have hinternal_data :=
          (Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
            t a b m radius).mp hinternal
        exact
          (not_lt_of_ge hinternal_data.2.1)
            hleft_data.2)

theorem Complex.logarithmicPhaseQuantitativeEndpointLeftInternal_disjoint_right
    (t : ℝ)
    (a b : ℤ)
    (radius : ℝ)
    (hab : a ≤ b) :
    Disjoint
      (Complex.logarithmicPhaseQuantitativeEndpointLeftCollarModes t a b radius ∪
        Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius)
      (Complex.logarithmicPhaseQuantitativeEndpointRightCollarModes t a b radius) := by
  exact
    Finset.disjoint_left.mpr
      (fun m hleft_internal hright =>
        have hright_data :=
          (Complex.mem_logarithmicPhaseQuantitativeEndpointRightCollarModes_iff
            t a b m radius).mp hright
        match Finset.mem_union.mp hleft_internal with
        | Or.inl hleft =>
            have hleft_data :=
              (Complex.mem_logarithmicPhaseQuantitativeEndpointLeftCollarModes_iff
                t a b m radius).mp hleft
            have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
            exact
              (not_lt_of_ge
                (le_trans hleft_data.2.le hab_real))
                hright_data.2
        | Or.inr hinternal =>
            have hinternal_data :=
              (Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
                t a b m radius).mp hinternal
            exact
              (not_lt_of_ge hinternal_data.2.2)
                hright_data.2)

end
end LFunctions
end Boundary
