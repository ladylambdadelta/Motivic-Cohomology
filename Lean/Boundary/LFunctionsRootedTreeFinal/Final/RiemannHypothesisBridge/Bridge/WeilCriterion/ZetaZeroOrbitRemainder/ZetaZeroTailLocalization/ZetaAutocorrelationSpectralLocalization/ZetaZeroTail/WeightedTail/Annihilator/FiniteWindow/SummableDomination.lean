import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Core

/-!
# Finite domination for summable distributions

An absolutely convergent nonzero series has a finite partial sum that strictly
dominates its complementary tail.  The finite set may be required to contain
any prescribed coordinate.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open Filter
open scoped ENNReal
open scoped Topology

theorem finite_norm_dominates_tail_of_tail_lt_half_total
    (total : ℂ)
    (finite : ℂ)
    (tail : ℂ)
    (htailSmall : norm tail < norm total / 2)
    (hsplit : finite + tail = total) :
    norm tail < norm finite :=
  not_le.mp
    (fun hfiniteLeTail =>
      let htotalNormLe :
          norm total ≤ norm finite + norm tail :=
        let hnormAdd :
            norm (finite + tail) ≤ norm finite + norm tail :=
          norm_add_le finite tail
        Eq.subst
          (motive := fun value : ℂ =>
            norm value ≤ norm finite + norm tail)
          hsplit
          hnormAdd
      let hfinitePlusTailLeDoubleTail :
          norm finite + norm tail ≤ norm tail + norm tail :=
        add_le_add_right hfiniteLeTail (norm tail)
      let hdoubleTailLtTotal :
          norm tail + norm tail < norm total :=
        let hdoubleTailLtHalves :
            norm tail + norm tail < norm total / 2 + norm total / 2 :=
          add_lt_add htailSmall htailSmall
        lt_of_lt_of_eq hdoubleTailLtHalves (add_halves (norm total))
      let htotalNormLt : norm total < norm total :=
        lt_of_le_of_lt
          (le_trans htotalNormLe hfinitePlusTailLeDoubleTail)
          hdoubleTailLtTotal
      (lt_irrefl (norm total)) htotalNormLt)

theorem exists_finite_sum_dominates_complementary_tsum
    {alpha : Type*}
    [DecidableEq alpha]
    (g : alpha → ℂ)
    (hg : Summable g)
    (rho : alpha)
    (htotal : tsum g ≠ 0) :
    ∃ U : Finset alpha,
      rho ∈ U ∧
        norm (tsum (fun eta : {eta : alpha // eta ∉ U} => g eta)) <
          norm (∑ eta in U, g eta) := by
  have htotalNormPositive : 0 < norm (tsum g) :=
    norm_pos_iff.mpr htotal
  have hhalfPositive : 0 < norm (tsum g) / 2 :=
    div_pos htotalNormPositive zero_lt_two
  have hnormSummable : Summable (fun eta : alpha => norm (g eta)) :=
    hg.norm
  have htailNormTendsToZero :
      Tendsto
        (fun U : Finset alpha =>
          tsum (fun eta : {eta : alpha // eta ∉ U} => norm (g eta)))
        atTop
        (nhds 0) :=
    tendsto_tsum_compl_atTop_zero (fun eta : alpha => norm (g eta))
  have htailEventually :
      ∀ᶠ U in atTop,
        tsum (fun eta : {eta : alpha // eta ∉ U} => norm (g eta)) <
          norm (tsum g) / 2 :=
    ((tendsto_order.1 htailNormTendsToZero).2
      (norm (tsum g) / 2) hhalfPositive)
  obtain ⟨Ubase, hUbase⟩ := Filter.eventually_atTop.1 htailEventually
  let U : Finset alpha := insert rho Ubase
  have hbaseSubset : Ubase ⊆ U :=
    Finset.subset_insert rho Ubase
  have htailNormSumSmall :
      tsum (fun eta : {eta : alpha // eta ∉ U} => norm (g eta)) <
        norm (tsum g) / 2 :=
    hUbase U hbaseSubset
  have hcomplementSummable :
      Summable (fun eta : {eta : alpha // eta ∉ U} => g eta) :=
    hg.subtype (fun eta : alpha => eta ∉ U)
  have htailNormBound :
      norm (tsum (fun eta : {eta : alpha // eta ∉ U} => g eta)) ≤
        tsum (fun eta : {eta : alpha // eta ∉ U} => norm (g eta)) :=
    norm_tsum_le_tsum_norm
      (hnormSummable.subtype (fun eta : alpha => eta ∉ U))
  have htailSmall :
      norm (tsum (fun eta : {eta : alpha // eta ∉ U} => g eta)) <
        norm (tsum g) / 2 :=
    lt_of_le_of_lt htailNormBound htailNormSumSmall
  have hseriesSplit :
      (∑ eta in U, g eta) +
          tsum (fun eta : {eta : alpha // eta ∉ U} => g eta) =
        tsum g :=
    sum_add_tsum_subtype_compl hg U
  have hfiniteDominates :
      norm (tsum (fun eta : {eta : alpha // eta ∉ U} => g eta)) <
        norm (∑ eta in U, g eta) := by
    exact
      finite_norm_dominates_tail_of_tail_lt_half_total
        (tsum g)
        (∑ eta in U, g eta)
        (tsum (fun eta : {eta : alpha // eta ∉ U} => g eta))
        htailSmall
        hseriesSplit
  exact ⟨U, Finset.mem_insert_self rho Ubase, hfiniteDominates⟩

def completedZeroCoordinateValueEmbedding : ZetaCompletedZeroCoordinate ↪ ℂ where
  toFun := fun rho : ZetaCompletedZeroCoordinate => (rho : ℂ)
  inj' := Subtype.val_injective

def completedZeroCoordinateValueFinset
    (U : Finset ZetaCompletedZeroCoordinate) : Finset ℂ :=
  U.map completedZeroCoordinateValueEmbedding

theorem completedZeroCoordinateValueFinset_mem
    (U : Finset ZetaCompletedZeroCoordinate)
    (rho : ZetaCompletedZeroCoordinate) :
    (rho : ℂ) ∈ completedZeroCoordinateValueFinset U ↔ rho ∈ U := by
  exact Iff.intro
    (fun hvalue =>
      match Finset.mem_map.mp hvalue with
      | ⟨eta, heta, hetaValue⟩ =>
          have hetaRho : eta = rho :=
            completedZeroCoordinateValueEmbedding.injective hetaValue
          Eq.subst
            (motive := fun coordinate : ZetaCompletedZeroCoordinate => coordinate ∈ U)
            hetaRho
            heta)
    (fun hrho =>
      Finset.mem_map.mpr ⟨rho, hrho, Eq.refl (rho : ℂ)⟩)

theorem completedZeroCoordinateValueFinset_completedZero
    (U : Finset ZetaCompletedZeroCoordinate) :
    ∀ eta : ℂ,
      eta ∈ completedZeroCoordinateValueFinset U → ZetaCompletedZero eta := by
  intro eta heta
  match Finset.mem_map.mp heta with
  | ⟨rho, hrho, hvalue⟩ =>
      exact Eq.subst
        (motive := fun value : ℂ => ZetaCompletedZero value)
        hvalue
        rho.property

def completedZeroCoordinateComplementEquiv
    (U : Finset ZetaCompletedZeroCoordinate) :
    {rho : ZetaCompletedZeroCoordinate // rho ∉ U} ≃
      {eta : ℂ //
        ZetaCompletedZero eta ∧ eta ∉ completedZeroCoordinateValueFinset U} where
  toFun := fun rho =>
    ⟨(rho : ℂ), rho.1.property,
      fun hvalue =>
        rho.2
          ((completedZeroCoordinateValueFinset_mem U rho.1).mp hvalue)⟩
  invFun := fun eta =>
    ⟨⟨(eta : ℂ), eta.2.1⟩,
      fun hrho =>
        eta.2.2
          ((completedZeroCoordinateValueFinset_mem U
            ⟨(eta : ℂ), eta.2.1⟩).mpr hrho)⟩
  left_inv := fun rho => Subtype.ext (Subtype.ext (Eq.refl (rho : ℂ)))
  right_inv := fun eta => Subtype.ext (Eq.refl (eta : ℂ))

theorem completedZeroCoordinateComplement_tsum_eq_valueComplement_tsum
    (U : Finset ZetaCompletedZeroCoordinate)
    (g : ZetaCompletedZeroCoordinate → ℂ) :
    tsum (fun rho : {rho : ZetaCompletedZeroCoordinate // rho ∉ U} => g rho) =
      tsum (fun eta : {
        eta : ℂ // ZetaCompletedZero eta ∧
          eta ∉ completedZeroCoordinateValueFinset U} =>
        g ⟨(eta : ℂ), eta.2.1⟩) := by
  let e :
      {rho : ZetaCompletedZeroCoordinate // rho ∉ U} ≃
        {eta : ℂ //
          ZetaCompletedZero eta ∧ eta ∉ completedZeroCoordinateValueFinset U} :=
    completedZeroCoordinateComplementEquiv U
  have hcoordinate :
      tsum (fun rho : {rho : ZetaCompletedZeroCoordinate // rho ∉ U} => g rho) =
        tsum (fun rho : {rho : ZetaCompletedZeroCoordinate // rho ∉ U} =>
          g ⟨((e rho : {eta : ℂ //
            ZetaCompletedZero eta ∧ eta ∉ completedZeroCoordinateValueFinset U}) : ℂ),
            (e rho).2.1⟩) := by
    exact tsum_congr
      (fun rho =>
        congrArg g
          (Subtype.ext
            (Eq.refl (rho.1 : ℂ))).symm)
  have htransport :=
    e.tsum_eq
      (fun eta : {
        eta : ℂ // ZetaCompletedZero eta ∧
          eta ∉ completedZeroCoordinateValueFinset U} =>
        g ⟨(eta : ℂ), eta.2.1⟩)
  exact Eq.trans hcoordinate htransport

theorem exists_finiteWindow_dominates_complementaryTail_of_annihilator_ne_zero
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate)
    (hannihilator :
      zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
  let g : ZetaCompletedZeroCoordinate → ℂ :=
    fun eta : ZetaCompletedZeroCoordinate =>
      b eta * zetaZeroSideContribution (eta : ℂ) f
  have hg : Summable g :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have htotalIdentity :
      zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
        tsum g :=
    zetaCompletedZeroSideAnnihilator_eq_tsum
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f
  have htotalNonzero : tsum g ≠ 0 :=
    fun hzero => hannihilator (Eq.trans htotalIdentity hzero)
  obtain ⟨U, hrhoU, hdominatesU⟩ :=
    exists_finite_sum_dominates_complementary_tsum g hg rho htotalNonzero
  let S : Finset ℂ := completedZeroCoordinateValueFinset U
  let hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta :=
    completedZeroCoordinateValueFinset_completedZero U
  have hrhoS : (rho : ℂ) ∈ S :=
    (completedZeroCoordinateValueFinset_mem U rho).mpr hrhoU
  have htailIdentity :
      tsum (fun eta : {eta : ZetaCompletedZeroCoordinate // eta ∉ U} => g eta) =
        zetaCompletedZeroSideAnnihilatorComplementaryTail b S f := by
    exact completedZeroCoordinateComplement_tsum_eq_valueComplement_tsum U g
  have hcoordinateSplit :
      (∑ eta in U, g eta) +
          tsum (fun eta : {eta : ZetaCompletedZeroCoordinate // eta ∉ U} => g eta) =
        tsum g :=
    sum_add_tsum_subtype_compl hg U
  have hannihilatorSplit :
      zetaCompletedZeroSideAnnihilator
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f =
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
          zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
    zetaCompletedZeroSideAnnihilator_eq_finiteWindow_add_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S hS f
  have hsumEquality :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
          zetaCompletedZeroSideAnnihilatorComplementaryTail b S f =
        (∑ eta in U, g eta) +
          tsum (fun eta : {eta : ZetaCompletedZeroCoordinate // eta ∉ U} => g eta) :=
    Eq.trans hannihilatorSplit.symm
      (Eq.trans htotalIdentity hcoordinateSplit.symm)
  have hfiniteIdentity :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        ∑ eta in U, g eta := by
    have hsameTailEquality :
        zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f +
            zetaCompletedZeroSideAnnihilatorComplementaryTail b S f =
          (∑ eta in U, g eta) +
            zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
      Eq.trans hsumEquality
        (congrArg
          (fun value : ℂ => (∑ eta in U, g eta) + value)
          htailIdentity)
    exact add_right_cancel hsameTailEquality
  have htailNormIdentity :
      norm (tsum (fun eta : {eta : ZetaCompletedZeroCoordinate // eta ∉ U} => g eta)) =
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) :=
    congrArg norm htailIdentity
  have hfiniteNormIdentity :
      norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) =
        norm (∑ eta in U, g eta) :=
    congrArg norm hfiniteIdentity
  have hdominatesS :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
    Eq.subst
      (motive := fun tailNorm : ℝ =>
        tailNorm < norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f))
      htailNormIdentity
      (Eq.subst
        (motive := fun finiteNorm : ℝ =>
          norm (tsum
            (fun eta : {eta : ZetaCompletedZeroCoordinate // eta ∉ U} => g eta)) <
              finiteNorm)
        hfiniteNormIdentity.symm
        hdominatesU)
  exact ⟨S, hS, hrhoS, hdominatesS⟩

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
