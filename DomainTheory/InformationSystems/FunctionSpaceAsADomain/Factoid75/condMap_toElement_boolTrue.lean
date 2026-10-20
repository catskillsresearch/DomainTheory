module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_tru_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_emptyEntails_singleton_tru

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap












theorem condMap_toElement_boolTrue (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, ht, _⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement_le A x)
        (emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _)))
    · exact ht hTru (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exfalso
      obtain ⟨⟨_, _⟩, hAll⟩ := hFls
      have : boolSat .isTrue .fls := hAll .isTrue fun t ht' =>
        (hu (Finset.mem_coe.2 ht')).2 .isTrue fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial
      simp only [boolSat] at this
  · intro Z hZ
    refine ⟨{BoolToken.tru}, ?_, boolSystem.con_sing _, A.con_sing _, ?_, ?_, ?_⟩
    · intro t ht
      have : t = .tru := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact (boolSystem.subset_closure (boolSystem.con_sing _))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exact fun hEmp => False.elim (not_emptyEntails_singleton_tru hEmp)
    · intro _ z hz
      have : z = Z := Finset.mem_singleton.mp (Finset.mem_coe.1 hz)
      subst this; exact hZ
    · exact fun hFls => False.elim (not_ent_tru_fls hFls)

end InfoSys
end DomainTheory.InformationSystems
