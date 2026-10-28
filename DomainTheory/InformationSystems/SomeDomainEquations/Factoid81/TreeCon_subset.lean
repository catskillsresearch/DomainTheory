module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_mono
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_mono

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_subset {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    ∀ {v}, v ⊆ u → TreeCon A v := by
  induction hu with
  | left u hA hL hR =>
    intro v hv
    refine TreeCon.left v (A.con_subset hA (atomFinset_mono hv)) ?_ ?_
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairLFinset u := pairLFinset_mono hv ht
          rw [hL] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairRFinset u := pairRFinset_mono hv ht
          rw [hR] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
  | right u hA hL hR ihL ihR =>
    intro v hv
    refine TreeCon.right v
      (Finset.Subset.antisymm
        (fun x hx => by
          have : x ∈ atomFinset u := atomFinset_mono hv hx
          rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
        (Finset.empty_subset _))
      (ihL (pairLFinset_mono hv)) (ihR (pairRFinset_mono hv))

end InfoSys

end DomainTheory.InformationSystems
