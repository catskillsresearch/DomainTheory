module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid77.ihom_obj_eq_exp

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys
open CategoryTheory

theorem theorem_77 :
    ∀ (A B : InfoSysObj), (ihom A).obj B = InfoSysObj.exp A B :=
  @ihom_obj_eq_exp

end DomainTheory.InformationSystems.InfoSys
