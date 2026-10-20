module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flatMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stemMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.singleton_disjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flatNOD
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stemNOD

@[expose] public section

/-!
# Exercise 1.15 (Scott 1981, PRG-19, §1) — non-isomorphic "finite-only" domains

"Construct non-isomorphic infinite domains where all elements are finite but where there are no
infinite chains `⟨xₙ⟩` of elements with `xₙ ⊏ xₙ₊₁` for all `n`."

We give two neighbourhood systems over `Δ = ℕ`:

* **`flat`** — `𝒟 = {ℕ} ∪ {{n} ∣ n ∈ ℕ}` (the *flat* domain). Its elements are exactly `⊥` and the
  pairwise-incomparable atoms `↑{n}` (`flat_classify`), so **all elements are finite/principal**
  (`flat_all_finite`), every atom is **maximal** (`flat_atom_maximal`), there is **no 3-chain**
  (`flat_no_three_chain`) and hence **no infinite ascending chain** (`flat_no_infinite_chain`). It is
  infinite (`flat_infinite`).

* **`stem`** — `𝒟 = {ℕ, {0,1}} ∪ {{n} ∣ n ∈ ℕ}` (a flat domain with one length-3 "stem"). It
  contains a strict **3-chain** `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` (`stem_three_chain`). It too has only finite
  elements and no infinite ascending chain (same flat-with-stem classification; the formally decisive
  difference from `flat` is the 3-chain).

Since an order-isomorphism transports strict chains, the 3-chain in `stem` would force a 3-chain in
`flat`, which has none: hence `¬ (flat ≅ᴰ stem)` (`not_isomorphic`). Two infinite, finite-element,
chain-bounded domains that are *not* isomorphic.

The classification results are *classical* (they decide whether an element contains some atom); the
constructions and the non-isomorphism argument are otherwise elementary.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-! ## The flat domain `flat`. -/






/-! ## The "stem" domain `stem`. -/




@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

/-! ## Non-isomorphism. -/
end DomainTheory.NeighbourhoodSystems.Exercise115
