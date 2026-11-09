module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndMap_pairElements

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem mem_snd_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {b : β}
    (hb : b ∈ sndFinset A B s) : b ∈ y.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : b ∈ ((productSystem.sndMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, B.con_sing b, ?_⟩⟩
    intro c hc
    have : c = b := Finset.mem_singleton.mp hc
    subst this
    exact B.ent_refl hCon.2 hb
  simpa [sndMap_pairElements] using this

end InfoSys
end DomainTheory.InformationSystems
