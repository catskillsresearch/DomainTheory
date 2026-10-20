/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB
variable {β : Type*} {n : ℕ}
variable {n : ℕ}

/-- **Scott's domain `A`** as the *least* family of subsets of `Σ* = {0,1}*` containing (i) the master
`Σ*` and (ii) every tag-`i` tuple `i ⋃_{j<n} 1ʲ0 X_j` built from components `X j` already in `A`:

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A }`. -/
inductive MemA (n : ℕ) : Set Str → Prop
  | univ : MemA n Set.univ
  | tuple (i : Bool) {X : Fin n → Set Str} : (∀ j, MemA n (X j)) → MemA n (embTuple i X)

end Example62A
end DomainTheory.NeighbourhoodSystems
