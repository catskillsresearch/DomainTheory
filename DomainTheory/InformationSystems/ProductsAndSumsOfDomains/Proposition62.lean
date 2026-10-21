/-ai
An approximable map h from C to the product of A and B that satisfies the two projection equations, first projection composed with h equal to f and second projection composed with h equal to g, equals the pairing of f and g. This is the uniqueness clause of Scott's Proposition 6.2.

The numbered name theorem_62 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.pairMap_unique

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_62.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ]
  (A : @DomainTheory.InformationSystems.InfoSys α inst) (B : @DomainTheory.InformationSystems.InfoSys β inst_1)
  {C : @DomainTheory.InformationSystems.InfoSys γ inst_2}
  (f : @DomainTheory.InformationSystems.InfoSys.ApproximableMap γ α inst_2 inst C A)
  (g : @DomainTheory.InformationSystems.InfoSys.ApproximableMap γ β inst_2 inst_1 C B)
  (h :
    @DomainTheory.InformationSystems.InfoSys.ApproximableMap γ
      (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) inst_2
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) C
      (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B)),
  @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap γ α inst_2 inst C A)
      (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp γ
        (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) α inst_2
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst C
        (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) A
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.fstMap α β inst inst_1 A B) h)
      f →
    @Eq (@DomainTheory.InformationSystems.InfoSys.ApproximableMap γ β inst_2 inst_1 C B)
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.comp γ
          (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) β inst_2
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) inst_1 C
          (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B) B
          (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.sndMap α β inst inst_1 A B) h)
        g →
      @Eq
        (@DomainTheory.InformationSystems.InfoSys.ApproximableMap γ
          (@DomainTheory.InformationSystems.InfoSys.ProdToken α β inst inst_1 A B) inst_2
          (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken α β inst inst_1 A B) C
          (@DomainTheory.InformationSystems.InfoSys.productSystem α β inst inst_1 A B))
        h (@DomainTheory.InformationSystems.InfoSys.ApproximableMap.pairMap α β γ inst inst_1 inst_2 A B C f g) :=
  @DomainTheory.InformationSystems.InfoSys.ApproximableMap.pairMap_unique

end DomainTheory.InformationSystems.InfoSys.ApproximableMap
