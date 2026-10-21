/-ai
Evaluating the conditional map of elements x and y at the Boolean element false yields y.

For the inclusion into y, a token of the image comes from a related Boolean set, and the Boolean trichotomy applies. An empty-entailing set contributes a token of the bottom element, which lies in y. Entailment of true is impossible, because the witnessing token lies under the false element and a Boolean point cannot satisfy both false and true. Entailment of false puts the token in y. For the reverse inclusion, the singleton false token is related to the singleton of the given token of y: that singleton is not empty-entailing, it does not entail true, and its false entailment returns the token.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_fls_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_emptyEntails_singleton_fls

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap












theorem condMap_toElement_boolFalse (x y : A.Element) :
    (condMap A x y).toElement boolFalse = y := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, _, hf⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement_le A y)
        (emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _)))
    · exfalso
      obtain ⟨⟨_, _⟩, hAll⟩ := hTru
      have : boolSat .isFalse .tru := hAll .isFalse fun t ht' =>
        (hu (Finset.mem_coe.2 ht')).2 .isFalse fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial
      simp only [boolSat] at this
    · exact hf hFls (Finset.mem_coe.2 (Finset.mem_singleton_self _))
  · intro Z hZ
    refine ⟨{BoolToken.fls}, ?_, boolSystem.con_sing _, A.con_sing _, ?_, ?_, ?_⟩
    · intro t ht
      have : t = .fls := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact (boolSystem.subset_closure (boolSystem.con_sing _))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exact fun hEmp => False.elim (not_emptyEntails_singleton_fls hEmp)
    · exact fun hTru => False.elim (not_ent_fls_tru hTru)
    · intro _ z hz
      have : z = Z := Finset.mem_singleton.mp (Finset.mem_coe.1 hz)
      subst this; exact hZ

end InfoSys
end DomainTheory.InformationSystems
