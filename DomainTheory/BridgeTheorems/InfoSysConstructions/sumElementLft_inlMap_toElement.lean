/-ai
Extracting the left element of the left image of an element x, using the left bottom token as witness, recovers x.

If a token a lies in the extracted element, its witnessing consistent set of tokens of the image entails the left token of a, and after the left part of the singleton of that token is identified with the singleton of a this is an entailment of a in A, so closure of x puts a in x. Conversely, if a lies in x, the singleton of a consists of tokens of x, and it contributes the left token of a to the image by the left consistency clause, the empty right part, and the entailment of that singleton in A.
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
public import DomainTheory.BridgeTheorems.InfoSysConstructions.rhtFinset_singleton_left
public import DomainTheory.BridgeTheorems.InfoSysConstructions.left_bot_mem_inlMap_toElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem sumElementLft_inlMap_toElement (x : A.Element) :
    sumElementLft A B ((inlMap A B).toElement x) A.bot
      (left_bot_mem_inlMap_toElement A B x) = x := by
  apply le_antisymm
  · intro a ha
    -- ha : left a ∈ inl(x)
    obtain ⟨u, hu, ⟨huCon, hSum, hr, hEnt⟩⟩ := ha
    have hEntA : A.Ent u a := by
      have : lftFinset ({SumToken.left a} : Finset (SumToken α β)) = {a} :=
        lftFinset_singleton_left a
      simpa [this] using hEnt a (Finset.mem_singleton_self a)
    exact x.closed u a hu hEntA
  · intro a ha
    change SumToken.left a ∈ ((inlMap A B).toElement x).carrier
    refine ⟨{a}, ?_, ?_⟩
    · intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this; exact ha
    · refine ⟨A.con_sing a, Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing a,
        rhtFinset_singleton_left (β := β) a⟩, rhtFinset_singleton_left (β := β) a, ?_⟩
      rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing a)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
