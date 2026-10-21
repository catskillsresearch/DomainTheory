/-ai
The right-hand side of the tree domain equation equals the sum of A with the product of the tree system of A with itself.

The numbered name theorem_81 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeRhs_eq_sum_product

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

set_option linter.unusedVariables false

theorem theorem_81.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (A : @DomainTheory.InformationSystems.InfoSys α inst),
  @Eq
    (@DomainTheory.InformationSystems.InfoSys
      (DomainTheory.InformationSystems.InfoSys.SumToken α
        (@DomainTheory.InformationSystems.InfoSys.ProdToken (DomainTheory.InformationSystems.InfoSys.TreeToken α)
          (DomainTheory.InformationSystems.InfoSys.TreeToken α)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)))
      fun
        (a b :
          DomainTheory.InformationSystems.InfoSys.SumToken α
            (@DomainTheory.InformationSystems.InfoSys.ProdToken (DomainTheory.InformationSystems.InfoSys.TreeToken α)
              (DomainTheory.InformationSystems.InfoSys.TreeToken α)
              (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
                @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
              (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
                @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
              (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
              (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))) =>
      @DomainTheory.InformationSystems.InfoSys.instDecidableEqSumToken α
        (@DomainTheory.InformationSystems.InfoSys.ProdToken (DomainTheory.InformationSystems.InfoSys.TreeToken α)
          (DomainTheory.InformationSystems.InfoSys.TreeToken α)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))
        inst
        (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
          (DomainTheory.InformationSystems.InfoSys.TreeToken α) (DomainTheory.InformationSystems.InfoSys.TreeToken α)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
            @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
          (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))
        a b)
    (@DomainTheory.InformationSystems.InfoSys.treeRhs α inst A)
    (@DomainTheory.InformationSystems.InfoSys.sumSystem α
      (@DomainTheory.InformationSystems.InfoSys.ProdToken (DomainTheory.InformationSystems.InfoSys.TreeToken α)
        (DomainTheory.InformationSystems.InfoSys.TreeToken α)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))
      inst
      (@DomainTheory.InformationSystems.InfoSys.instDecidableEqProdToken
        (DomainTheory.InformationSystems.InfoSys.TreeToken α) (DomainTheory.InformationSystems.InfoSys.TreeToken α)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))
      A
      (@DomainTheory.InformationSystems.InfoSys.productSystem (DomainTheory.InformationSystems.InfoSys.TreeToken α)
        (DomainTheory.InformationSystems.InfoSys.TreeToken α)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (fun (a b : DomainTheory.InformationSystems.InfoSys.TreeToken α) =>
          @DomainTheory.InformationSystems.InfoSys.instDecidableEqTreeToken α inst a b)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A)
        (@DomainTheory.InformationSystems.InfoSys.treeSystem α inst A))) :=
  @DomainTheory.InformationSystems.InfoSys.treeRhs_eq_sum_product

end DomainTheory.InformationSystems.InfoSys
