module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_empty_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_empty_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolCon_trichotomy
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.subset_of_entSet_mem

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

def condMap (x y : A.Element) : ApproximableMap boolSystem A where
  rel u v :=
    u ∈ boolSystem.Con ∧ v ∈ A.Con ∧
      (EmptyEntails boolSystem u → EmptyEntails A v) ∧
      (boolSystem.Ent u .tru → (↑v : Set α) ⊆ x.carrier) ∧
      (boolSystem.Ent u .fls → (↑v : Set α) ⊆ y.carrier)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := by
    refine ⟨boolSystem.con_empty, A.con_empty, fun _ => emptyEntails_empty A, ?_, ?_⟩
    · exact fun h => False.elim (not_ent_empty_tru h)
    · exact fun h => False.elim (not_ent_empty_fls h)
  union_right := by
    rintro u v v' ⟨hu, hv, hE, ht, hf⟩ ⟨_, hv', hE', ht', hf'⟩
    have hvU : v ∪' v' ∈ A.Con := by
      rcases boolCon_trichotomy hu with hEmp | hTru | hFls
      · have hsub : ↑(v ∪' v') ⊆ A.botElement.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact emptyEntails_mem_botElement A (hE hEmp z hz)
          · exact emptyEntails_mem_botElement A (hE' hEmp z hz)
        exact A.botElement.consistent _ hsub
      · have hsub : ↑(v ∪' v') ⊆ x.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact ht hTru (Finset.mem_coe.2 hz)
          · exact ht' hTru (Finset.mem_coe.2 hz)
        exact x.consistent _ hsub
      · have hsub : ↑(v ∪' v') ⊆ y.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact hf hFls (Finset.mem_coe.2 hz)
          · exact hf' hFls (Finset.mem_coe.2 hz)
        exact y.consistent _ hsub
    refine ⟨hu, hvU, fun hEmp => (emptyEntails_funion A).2 ⟨hE hEmp, hE' hEmp⟩, ?_, ?_⟩
    · intro hTru z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
      · exact ht hTru (Finset.mem_coe.2 hz)
      · exact ht' hTru (Finset.mem_coe.2 hz)
    · intro hFls z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
      · exact hf hFls (Finset.mem_coe.2 hz)
      · exact hf' hFls (Finset.mem_coe.2 hz)
  mono := by
    rintro u u' v v' ⟨hu, hv, hE, ht, hf⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_, ?_, ?_⟩
    · intro hEmp
      have hEmpu : EmptyEntails boolSystem u := fun t ht' =>
        boolSystem.ent_trans boolSystem.con_empty hu' hEmp (hEntu t ht')
      exact fun z hz => A.ent_trans A.con_empty hv (hE hEmpu) (hEntv z hz)
    · intro hTru
      rcases boolCon_trichotomy hu with hEmp | hTruU | hFlsU
      · have hEv' : EmptyEntails A v' := fun z hz =>
          A.ent_trans A.con_empty hv (hE hEmp) (hEntv z hz)
        exact fun z hz =>
          (botElement.le A x) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
      · exact subset_of_entSet_mem A (ht hTruU) hEntv
      · exfalso
        have hFls' : boolSystem.Ent u' .fls :=
          boolSystem.ent_trans hu' hu (fun t ht' => hEntu t ht') hFlsU
        obtain ⟨⟨p, hp⟩, hAllT⟩ := hTru
        obtain ⟨_, hAllF⟩ := hFls'
        have htru : boolSat p .tru := hAllT p hp
        have hfls : boolSat p .fls := hAllF p hp
        cases p <;> simp only [boolSat] at htru hfls
    · intro hFls
      rcases boolCon_trichotomy hu with hEmp | hTruU | hFlsU
      · have hEv' : EmptyEntails A v' := fun z hz =>
          A.ent_trans A.con_empty hv (hE hEmp) (hEntv z hz)
        exact fun z hz =>
          (botElement.le A y) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
      · exfalso
        have hTru' : boolSystem.Ent u' .tru :=
          boolSystem.ent_trans hu' hu (fun t ht' => hEntu t ht') hTruU
        obtain ⟨⟨p, hp⟩, hAllF⟩ := hFls
        obtain ⟨_, hAllT⟩ := hTru'
        have hfls : boolSat p .fls := hAllF p hp
        have htru : boolSat p .tru := hAllT p hp
        cases p <;> simp only [boolSat] at htru hfls
      · exact subset_of_entSet_mem A (hf hFlsU) hEntv

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem entSet_singleton_fls_of_ent_fls {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .fls) :
    boolSystem.EntSet ({BoolToken.fls} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have hfls : boolSat p .fls := hAll p hp
  cases p with
  | undef => simp only [boolSat] at hfls
  | isTrue => simp only [boolSat] at hfls
  | isFalse =>
    have hsat : boolSat .isFalse t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat.bot _⟩
    | fls =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .fls (Finset.mem_singleton_self _)⟩
    | tru => exact False.elim hsat

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem entSet_singleton_tru_of_ent_tru {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .tru) :
    boolSystem.EntSet ({BoolToken.tru} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have htru : boolSat p .tru := hAll p hp
  cases p with
  | undef => simp only [boolSat] at htru
  | isFalse => simp only [boolSat] at htru
  | isTrue =>
    have hsat : boolSat .isTrue t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat.bot _⟩
    | tru =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .tru (Finset.mem_singleton_self _)⟩
    | fls => exact False.elim hsat

end InfoSys
end DomainTheory.InformationSystems


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem not_emptyEntails_singleton_fls :
    ¬ EmptyEntails boolSystem ({BoolToken.fls} : Finset BoolToken) :=
  fun h => not_ent_empty_fls (h .fls (Finset.mem_singleton_self _))

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem not_emptyEntails_singleton_tru :
    ¬ EmptyEntails boolSystem ({BoolToken.tru} : Finset BoolToken) :=
  fun h => not_ent_empty_tru (h .tru (Finset.mem_singleton_self _))

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem not_ent_fls_tru : ¬ boolSystem.Ent {BoolToken.fls} BoolToken.tru := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have hfls : boolSat p .fls := hp .fls (Finset.mem_singleton_self _)
  have htru : boolSat p .tru := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem condMap_toElement_boolFalse (x y : A.Element) :
    (condMap A x y).toElement boolFalse = y := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, _, hf⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement.le A y)
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

alias condMap.toElement_boolFalse := condMap_toElement_boolFalse

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem not_ent_tru_fls : ¬ boolSystem.Ent {BoolToken.tru} BoolToken.fls := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have htru : boolSat p .tru := hp .tru (Finset.mem_singleton_self _)
  have hfls : boolSat p .fls := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


theorem condMap_toElement_boolTrue (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, ht, _⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement.le A x)
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

alias condMap.toElement_boolTrue := condMap_toElement_boolTrue

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


open ApproximableMap


/-- One direction of the conditional isomorphism on pairs. -/
theorem condMap.pair_roundtrip (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y :=
  ⟨condMap.toElement_boolTrue A x y, condMap.toElement_boolFalse A x y⟩

end InfoSys
end DomainTheory.InformationSystems
