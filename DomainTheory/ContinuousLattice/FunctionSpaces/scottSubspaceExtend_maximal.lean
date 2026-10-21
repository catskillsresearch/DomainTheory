/-ai
If D is a continuous lattice, e embeds X into Y, and a Scott map f' on Y extends f along e, then at each point of Y the value of f' is at most the subspace extension of f.

The value of f' is the supremum of the infima of its images on Scott-open neighborhoods. For each such neighborhood U, the infimum of f' on U is at most the infimum of f' on the intersection of the image of e with U, and that restricted infimum equals the subspace-extension infimum of f on U, which belongs to the family defining the extension.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
import all Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.sInf_image_le_sInf_image_of_subset
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMap_eq_sSup_openInfs
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_eq_of_comp

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]


/-- **Scott 1972, Proposition 3.8 (subspace variant).** `f̄` (with the Scott topology on `Y`) is
the maximal extension along a subspace embedding. The faithful statement (arbitrary topology on
`Y`) is `proposition_3_8` in `Constructions.lean`. -/
theorem scottSubspaceExtend_maximal (hD : IsContinuousLattice D) (e : X → Y) (_he : IsEmbedding e)
    (f : X → D) (f' : ScottMap Y D) (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    (f' : Y → D) y ≤ scottSubspaceExtend e f y := by
  have hEq := scottMap_eq_sSup_openInfs hD f' y
  have hmain :
      sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
        d = sInf (Set.image (f' : Y → D) U) } ≤ scottSubspaceExtend e f y := by
    unfold scottSubspaceExtend
    apply sSup_le
    intro d hd
    obtain ⟨U, hUopen, hyU, rfl⟩ := hd
    have hmem : scottSubspaceExtendInf e f U ∈
        { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e f U } :=
      ⟨U, hUopen, hyU, rfl⟩
    refine le_trans ?_ (le_sSup hmem)
    have hrestrict :
        sInf (Set.image (f' : Y → D) U) ≤
          sInf (Set.image (f' : Y → D) (Set.image e Set.univ ∩ U)) :=
      sInf_image_le_sInf_image_of_subset
        (show Set.image e Set.univ ∩ U ⊆ U from inter_subset_right)
    refine le_trans hrestrict (le_of_eq (scottSubspaceExtendInf_eq_of_comp (f' := f') h_ext).symm)
  exact le_trans (le_of_eq hEq) hmain

end SubspaceExtension
end DomainTheory.ContinuousLattice
