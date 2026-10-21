/-ai
Extracting the right element of the right image of an element y, using the right bottom token as witness, recovers y.

If a token b lies in the extracted element, its witnessing consistent set of tokens of the image entails the right token of b, and after the right part of the singleton of that token is identified with the singleton of b this is an entailment of b in B, so closure of y puts b in y. Conversely, if b lies in y, the singleton of b consists of tokens of y, and it contributes the right token of b to the image by the right consistency clause, the empty left part, and the entailment of that singleton in B.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.lftFinset_singleton_right
public import DomainTheory.BridgeTheorems.InfoSysConstructions.right_bot_mem_inrMap_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem sumElementRht_inrMap_toElement (y : B.Element) :
    sumElementRht A B ((inrMap A B).toElement y) B.bot
      (right_bot_mem_inrMap_toElement A B y) = y := by
  apply le_antisymm
  · intro b hb
    obtain ⟨w, hw, ⟨hwCon, hSum, hl, hEnt⟩⟩ := hb
    have hEntB : B.Ent w b := by
      have : rhtFinset ({SumToken.right b} : Finset (SumToken α β)) = {b} :=
        rhtFinset_singleton_right b
      simpa [this] using hEnt b (Finset.mem_singleton_self b)
    exact y.closed w b hw hEntB
  · intro b hb
    change SumToken.right b ∈ ((inrMap A B).toElement y).carrier
    refine ⟨{b}, ?_, ?_⟩
    · intro c hc
      have : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst this; exact hb
    · refine ⟨B.con_sing b, Or.inr ⟨lftFinset_singleton_right (α := α) b,
        by rw [rhtFinset_singleton_right]; exact B.con_sing b⟩,
        lftFinset_singleton_right (α := α) b, ?_⟩
      rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing b)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
