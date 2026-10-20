/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.isFinitary_of_projectionPair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}




section ProdCase

variable (a b : ApproximableMap U U)





/-- **Proposition 8.10(b), `×`-case.** `a, b` finitary projections `⟹` `a × b` is finitary, with
witnessing domain `D_a × D_b`. -/
theorem finitary_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (prodComb a b) :=
  isFinitary_of_projectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

end ProdCase
end DomainTheory.NeighbourhoodSystems
