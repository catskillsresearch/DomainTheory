module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




theorem sumComb_eq (a b : ApproximableMap U U) :
    sumComb a b = (cond U).comp
      ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
          (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                  (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
        jPlus) := rfl

end DomainTheory.NeighbourhoodSystems
