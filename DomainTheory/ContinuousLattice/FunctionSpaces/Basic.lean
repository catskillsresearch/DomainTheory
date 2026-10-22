/-ai
This module gathers and re-exports the basic constructions of Scott's function spaces: Scott maps and their composition, order, and complete-lattice structure, constant, identity, step, and lambda maps, the pointwise and induced topologies, currying, retractions and projections, subspace extension, and the fixed-point operator. Locally, Scott's notation [X → Y] is the type of continuous maps with the pointwise product topology, and ScottC is the type of continuous maps between complete lattices with Scott topologies on both sides.

A Scott map is continuous for the Scott topologies on its domain and codomain.

The continuity witness is the second component of the map.

The set of elements way below a given element is directed.

The join of two elements way below it is again way below it, and that join lies above each of them.

The underlying value of the fixed-point map at a Scott endomorphism equals the fixed-point operator applied to that endomorphism.

The equality is definitional.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionEvalSubbasis
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.continuousMapInducedPiTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.const
public import DomainTheory.ContinuousLattice.FunctionSpaces.bot
public import DomainTheory.ContinuousLattice.FunctionSpaces.le
public import DomainTheory.ContinuousLattice.FunctionSpaces.sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSupMaps
public import DomainTheory.ContinuousLattice.FunctionSpaces.lt
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseSubbasis
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambdaAt
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda
public import DomainTheory.ContinuousLattice.FunctionSpaces.ambientSSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_7_retraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_7_projection
public import DomainTheory.ContinuousLattice.FunctionSpaces.finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.con_
public import DomainTheory.ContinuousLattice.FunctionSpaces.min
public import DomainTheory.ContinuousLattice.FunctionSpaces.projection
public import DomainTheory.ContinuousLattice.FunctionSpaces.toOrderHom
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
public import DomainTheory.ContinuousLattice.FunctionSpaces.fixMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwise_sup_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwise_sSup_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSupMaps_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_refl'
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_trans'
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_antisymm'
public import DomainTheory.ContinuousLattice.FunctionSpaces.lt_iff_le_not_ge'
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.isLUB_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.sup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.bot_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_not_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_prod_mk_left
public import DomainTheory.ContinuousLattice.FunctionSpaces.curry_right_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_prod_mk_right
public import DomainTheory.ContinuousLattice.FunctionSpaces.curry_left_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.lambda_outer_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.mem_finsetSupOf_of_mem
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_sSup_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_le_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.directedOn_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_mono
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_sup_of_preservesSSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_mono_of_preservesSSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_of_incl_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_converseRetr_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_incl
public import DomainTheory.ContinuousLattice.FunctionSpaces.converseRetr_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_iff
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_bot
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_finsetSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_directedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.Projections
public import DomainTheory.ContinuousLattice.FunctionSpaces.instSupSet
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic.isLUB_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.instCompleteLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.con_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.min_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_eq
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_le
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_mono
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_preservesDirectedSup

@[expose] public section

/-!
# Function spaces on continuous lattices (Scott 1972, §3)

Scott's §3 studies spaces of continuous maps `[X → Y]` with the topology of pointwise
convergence (subbasic sets `{f | f x ∈ U}`), the pointwise specialization order (3.2),
and the fact that `[D → D']` is a continuous lattice when `D → D']` is (3.3).

## March 1972 correction (Milner)

Scott's remark before Proposition 2.5 was mistaken: a `T₀`-topology on a complete lattice
need not have every open set Scott-open. The two extreme `T₀`-topologies inducing the same
order are generated by `{x | x ⋢ y}` (lower) and `{x | y ⊑ x}` (principal up-sets).
The corrected proofs of 2.9, 2.10, and 3.3 assume the given topology is *coarser* than
the Scott (lattice) topology (`scottTopologicalSpace ≤ τ` in mathlib). We revisit that
hypothesis when formalizing those results.

In the March 1972 correction (p. 135), Scott writes `⊔S′` (prime on the index, not on the
join): for `S ⊆ D` a subspace of ambient `D′`, `⊔S′` is the supremum of `S` computed in `D′`,
while `⊔S` is the supremum in the subspace `D`; the retraction identity is `j(⊔S′) = ⊔S`.
-/

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-! ### Definition 3.1 -/


/-- Scott's notation `[X → Y]`: continuous maps with the pointwise (product) topology. -/
abbrev ScottFunctionSpace (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  C(X, Y)

/-! ### Proposition 3.2 -/

/-! ### §3 on continuous lattices: pointwise lattice structure -/

/-- Continuous maps `D → D'` with Scott topologies on domain and codomain. -/
abbrev ScottC (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :=
  @ContinuousMap D D' scottTopologicalSpace scottTopologicalSpace


namespace ScottMap

theorem continuous (f : ScottMap D D') :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f :=
  f.2


/-! ### The complete lattice `[D → D']` (Theorem 3.3, order content)

The pointwise order makes `ScottMap D D'` a partial order; `sSupMaps` gives suprema (pointwise,
since directed *and* arbitrary suprema of Scott maps are computed pointwise — Theorem 3.3). By
`completeLatticeOfSup` this is a complete lattice. Note infima are *not* pointwise (Scott's
warning); `completeLatticeOfSup` derives them as `sSup` of lower bounds. -/


end ScottMap

/-! ### Theorem 3.3 (core) -/


/-! ### Theorem 3.3 (`[D → D']` is a continuous lattice)

Scott's *step functions* `ē[e, e']` are the building blocks: `ē[e,e'](x) = e'` if `e ≪ x`, else
`⊥`. We encode the conditional value as `⨆ _ : e ≪ x, e'` (which is `e'` when `e ≪ x` and `⊥`
otherwise), avoiding any decidability assumption. Each step function is Scott-continuous (the
way-above set `{x | e ≪ x}` is Scott-open), is way below `f` whenever `e' ≪ f e`, and `f` is the
supremum of the step functions below it — whence `[D → D']` is a continuous lattice. -/


/-! ### Theorem 3.3(b): the lattice topology = the topology of pointwise convergence

The Scott topology of the continuous lattice `[D → D']` coincides with the product (pointwise
convergence) topology, whose subbasis is `{f | f x ∈ U}` (`U` Scott-open in `D'`). One inclusion
(pointwise ⊆ Scott) is immediate: each subbasic set is Scott-open in the lattice (joins are
pointwise). The other (Scott ⊆ pointwise) is Scott's argument via the `↟φ` basis of a continuous
lattice: `φ ≪ g` forces `φ ≤ ⊔ᵢ ē[eᵢ,eᵢ']` for finitely many pairs with `eᵢ' ≪ g eᵢ`, and the
finite intersection `⋂ᵢ {h | eᵢ' ≪ h eᵢ}` is a pointwise-open neighbourhood of `g` inside `↟φ`. -/


/-! ### Corollary 3.4 -/

/-! ### Proposition 3.5 (currying) -/


/-! ### Definition 3.6 -/


namespace IsContinuousLatticeRetraction


end IsContinuousLatticeRetraction

/-! ### Proposition 2.10: a retract of a continuous lattice is a continuous lattice -/

/-! ### Proposition 3.7 -/


/-! ### Proposition 3.10 -/

section Proposition310

open Finset

namespace IsContinuousLatticeProjection


theorem directedOn_wayBelow (a : D) : DirectedOn (· ≤ ·) { z | z ≪ a } := by
  intro p hp q hq
  exact ⟨p ⊔ q, WayBelow.sup hp hq, le_sup_left, le_sup_right⟩

end IsContinuousLatticeProjection

/-! #### Proposition 3.10, converse direction

Given a map `i : D → D'` satisfying (i)–(iii), Scott's formula (iv)
`j(x') = ⊔ { x | i(x) ⊑ x' }` is the unique continuous retraction making `D` a projection of `D'`. -/

variable {i : D → D'}


end Proposition310

/-! ### Proposition 3.8 -/

section SubspaceExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]


end SubspaceExtension

/-! ### Definition 3.11 / Proposition 3.12: the lattice of projections `J_D` -/

section Projections


namespace Projections


end Projections

end Projections

/-! ### Proposition 3.13: `D` is a projection of `[D → D]` -/

namespace Proposition313


end Proposition313

/-! ### Proposition 3.14: the fixed-point operator `fix : [D → D] → D` -/

namespace Proposition314


@[simp] theorem fixMap_apply (f : ScottMap D D) : (fixMap f : D) = fix f := rfl
end Proposition314
end DomainTheory.ContinuousLattice
