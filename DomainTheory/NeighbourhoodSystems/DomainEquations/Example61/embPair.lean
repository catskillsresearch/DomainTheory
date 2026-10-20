/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embR

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `1P ∪ 2Q`: the product-style neighbourhood of `D^§`. -/
def embPair (P Q : Set (List Bool × α)) : Set (List Bool × α) := embL P ∪ embR Q

end Example61
end DomainTheory.NeighbourhoodSystems
