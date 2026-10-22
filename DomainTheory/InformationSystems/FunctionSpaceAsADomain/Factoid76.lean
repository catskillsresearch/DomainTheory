module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp_toElement

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_76.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
  (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
  (C : @DomainTheory.InformationSystems.InfoSys γ inst_2)
  (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap β γ inst_1 inst_2 B C)
  (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap α β inst inst_1 A B),
  @Eq
    (@DomainTheory.InformationSystems.InfoSys.Element
      (@DomainTheory.InformationSystems.InfoSys.FunToken α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.functionSystem α γ inst inst_2 A C))
    (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.toElement
      (@DomainTheory.InformationSystems.InfoSys.ProdToken
        (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
      (@DomainTheory.InformationSystems.InfoSys.FunToken α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
        (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.productSystem
        (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B))
      (@DomainTheory.InformationSystems.InfoSys.functionSystem α γ inst inst_2 A C)
      (@DomainTheory.InformationSystems.InfoSys.compOp α β γ inst inst_1 inst_2 A B C)
      (@DomainTheory.InformationSystems.InfoSys.pairElements
        (@DomainTheory.InformationSystems.InfoSys.FunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.FunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqFunToken α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem β γ inst_1 inst_2 B C)
        (@DomainTheory.InformationSystems.InfoSys.functionSystem α β inst inst_1 A B)
        (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement β γ inst_1 inst_2 B C g)
        (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α β inst inst_1 A B f)))
    (@DomainTheory.InformationSystems.InfoSys.approxMap_toElement α γ inst inst_2 A C
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp α β γ inst inst_1 inst_2 A B C g f)) :=
  @DomainTheory.InformationSystems.InfoSys.compOp_toElement

end DomainTheory.InformationSystems.InfoSys
