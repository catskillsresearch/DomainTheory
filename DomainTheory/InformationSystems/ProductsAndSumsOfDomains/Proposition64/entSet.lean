module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

namespace entSet

theorem lft_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    A.EntSet (lftFinset u) (lftFinset u') := fun _ hx =>
  (hEnt _ ((mem_lftFinset).1 hx)).2.2

theorem rht_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    B.EntSet (rhtFinset u) (rhtFinset u') := fun _ hy =>
  (hEnt _ ((mem_rhtFinset).1 hy)).2.2

theorem lft_eq_empty {u u' : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    lftFinset u' = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((hEnt _ ((mem_lftFinset).1 hx)).2.1 hl)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rht_eq_empty {u u' : Finset (SumToken α β)}
    (hr : rhtFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    rhtFinset u' = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim ((hEnt _ ((mem_rhtFinset).1 hy)).2.1 hr)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end entSet

end InfoSys

end DomainTheory.InformationSystems
