module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branch
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_prefix_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq_mono

@[expose] public section

/-!
# Exercise 1.13 (Scott 1981, PRG-19, §1) — the infinite binary system `B`, revisited

Scott: "Verify all the assertions made about the system `B` … Draw a picture … which includes nodes
for all `σ ∈ Σ*` … and where the total elements lie. (The picture … has to have limit nodes all
along the top.)"

The "assertions about `B`" are exactly the content of `ExampleB.lean`:

* `ExampleB.B` is a neighbourhood system (`ExampleB.nestedOrDisjoint`);
* `ExampleB.sigmaElt`/`sigmaElt_bot` realize Scott's `σx` and `σ⊥` with `σx ∈ |B|`;
* `ExampleB.sigmaBot_le_iff` is "`σ₀⊥ ⊑ σ₁⊥ ⟺ σ₀` initial segment of `σ₁`";
* `ExampleB.mem_iff_exists_sigmaBot` is "`x = ⋃ₙ σₙ⊥`".

This file supplies the **limit nodes**: for an infinite path `p : ℕ → Bool` we build the element
`branch p ∈ |B|` as the ascending union (Theorem 1.11(ii)) of the finite approximations
`σₙ⊥ = (p↾n)⊥`, show every finite approximation approximates it (`branchSeq_le_branch`), and prove it
is a **total** (maximal) element (`branch_isTotal`). These are the nodes "along the top".

Constructive except `branch_isTotal`'s use of `B`'s structure (still `[propext, Quot.sound]`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB







end DomainTheory.NeighbourhoodSystems.Exercise113
