module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.supSet
public import DomainTheory.ContinuousLattice.Theorem212.completeLattice
public import DomainTheory.ContinuousLattice.Theorem212.idemFixRetraction
public import DomainTheory.ContinuousLattice.Theorem212.orderIsoScottHomeomorph
public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import DomainTheory.ContinuousLattice.Theorem212.isLUB_sSup
public import DomainTheory.ContinuousLattice.Theorem212.coe_sSup
public import DomainTheory.ContinuousLattice.Theorem212.idemFix_incl_preservesDirectedSup
public import DomainTheory.ContinuousLattice.Theorem212.idemFix_retr_preservesDirectedSup
public import DomainTheory.ContinuousLattice.Theorem212.scottOpen_preimage_orderIso

@[expose] public section

/-!
# Theorem 2.12: injective spaces are exactly the continuous lattices

Scott's Theorem 2.12 states that a `T₀`-space is injective iff it is a continuous lattice under
its Scott topology. The forward direction (continuous lattice ⟹ injective) is
`theorem_2_12_forward` (= Proposition 2.11) in `Constructions.lean`.

This file supplies the **backward** direction. The argument (Scott 1972, §2) is:

* an injective space is a retract of a power of the Sierpiński space `𝕆 = Prop` (Corollary 1.6);
* a power of `𝕆` is a continuous lattice whose Scott topology is its product topology
  (`sierpinskiPower_isContinuousLattice`, `scottTopology_sierpinskiPower`);
* a retract of a continuous lattice is a continuous lattice (Proposition 2.10).

The retraction `r : 𝕆^I → D` with section `s : D → 𝕆^I` makes `e := s ∘ r` a Scott-continuous
idempotent on `𝕆^I`, whose fixed-point set is a continuous lattice (Proposition 2.10) and is
homeomorphic to `D`. Hence every injective space is homeomorphic to a continuous lattice under
its Scott topology.

The order-theoretic core is the construction `IdemFix`: the fixed points of a Scott-continuous
idempotent on a complete lattice form a complete lattice (`IdemFix.completeLattice`).
-/

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]


namespace IdemFix

variable {e : L → L}





end IdemFix

/-! ### The fixed-point set of a Scott-continuous idempotent is a continuous lattice -/

variable {e : L → L}




end FixedPoints

/-! ### Theorem 2.12, backward direction -/

universe u

/-! ### Theorem 2.12 on a pre-existing complete lattice

The backward direction above initially supplies a homeomorphic continuous lattice.  When the
specialization order of the given topology is already a specified complete-lattice order, the
homeomorphism is automatically an order isomorphism.  The following transport lemmas recover that
exact lattice structure and its Scott topology. -/

section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]



end Theorem212Transfer

/-! ### Lemma 3.9: compatibility of maximal extensions with a projection on the range -/

section Lemma39

variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']
end Lemma39
end DomainTheory.ContinuousLattice
