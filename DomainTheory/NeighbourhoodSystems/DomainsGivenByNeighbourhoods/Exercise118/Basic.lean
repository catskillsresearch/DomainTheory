/-ai
This file gathers and re-exports concatenation of finite sequences, finite consistency, the intersection of a nonempty family of filters, the least filter containing a consistent set, the three-point neighbourhood system together with the sets A, B, and Cc, the three-member family, and the triple, membership of entries of a concatenation, containment of a running intersection in the master neighbourhood, and the two identities for running intersections along a concatenation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.appendSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.FinitelyConsistent
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.sInf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.leastFilter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.triSys
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.A
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.B
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Cc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.family
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.triple
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.appendSeq_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.interUpTo_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.interUpTo_appendSeq_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.interUpTo_appendSeq

@[expose] public section

/-!
# Exercise 1.18 (Scott 1981, PRG-19, §1) — consistent subsets and filter intersections

Scott calls a subset `C ⊆ 𝒟` *consistent* iff every finite subset of `C` is consistent in `𝒟`.
This file formalizes (representing finite subsets as finite sequences drawn from `C`):

* `FinitelyConsistent C` — every finite sequence from `C` is `Consistent`;
* a concrete `C = {A, B, Cc}` (over `Δ = {0,1,2}`, all-non-empty-subsets system) with three
  members, pairwise consistent (`family_pairwise_nonempty`) but **not** consistent
  (`not_finitelyConsistent`) — `A ∩ B ∩ Cc = ∅`;
* `sInf F hF` — the intersection of a non-empty family `F` of filters is a filter, the greatest
  lower bound (`sInf_le`, `le_sInf`);
* `leastFilter C hCsub hC` — the **least** filter containing a consistent `C`, with
  `subset_leastFilter` (`C ⊆` it) and `leastFilter_le` (it is least). The intersection law uses
  the *append* of two finite sequences (`interUpTo_appendSeq`).

Constructive (`[propext, Quot.sound]`) except the counterexample's finite case-analysis.
-/

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-! ### Finite consistency. -/


/-! ### Intersection of a non-empty family of filters (Scott's last claim). -/


/-! ### The least filter containing a consistent `C`. -/


end NeighborhoodSystem

/-! ### A 3-element pairwise-consistent but not consistent set. -/


namespace triSys


end triSys
end DomainTheory.NeighbourhoodSystems
