
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_isGraph (f g : Pomega) :
    sumMed f g = graph (fun u => funOf (sumMed f g) u) := by
  apply graph_ext
  intro u
  exact (sumMed_app f g u).symm

end DomainTheory.DataTypesAsLattices
