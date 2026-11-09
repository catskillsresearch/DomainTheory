module

public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_unfoldFinset

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem lftFinset_image_unfold (u : Finset (TreeToken α)) :
    lftFinset (unfoldFinset A u) = atomFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ unfoldFinset A u := (mem_lftFinset).1 hx
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | atom y =>
      have : y = x := SumToken.left.inj hU
      subst this
      exact mem_atomFinset.2 ht
    | bot | pairL _ | pairR _ => exact nomatch hU
  · intro hx
    exact (mem_lftFinset).2
      ((mem_unfoldFinset A).2 ⟨.atom x, mem_atomFinset.1 hx, rfl⟩)

end DomainTheory.BridgeTheorems
