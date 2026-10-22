/-ai
The strict function space from A to B is the information system on strict function tokens whose bottom is the strict bottom token and whose consistency and entailment are strict function consistency and strict function entailment. A subset of a strictly consistent set remains strictly consistent because the underlying function tokens do. A singleton is strictly consistent because any output union sits inside the token's output, and empty entailment of the input union passes to that output by strictness of the token. A strictly entailed token may be adjoined because the underlying function space allows it: if the token occurs in the tested subset it is split off by the filter identity and the union law for empty entailment, and otherwise the subset already lies in the original set. Entailment of the bottom token, reflexivity, and transitivity are the corresponding laws of the function space on underlying tokens.
ai-/
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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_subset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_singleton
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.insert_filter_ne_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.filter_ne_subset_of_subset_insert_strict

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- **Factoid 7.5.** The strict function-space information system `A →ₛ B`. -/
def strictFunctionSystem : InfoSys (StrictFunToken A B) where
  bot := strictBot A B
  Con := {w | StrictFunCon A B w}
  Ent := StrictFunEnt A B
  con_subset := by
    intro w w' ⟨hwFun, hwE⟩ hw'
    refine ⟨fun s hs hin =>
      hwFun s (fun q hq => (toFunFinset_subset A B hw') (hs hq)) hin, ?_⟩
    intro s hs hE
    exact hwE s (fun q hq => hw' (hs hq)) hE
  con_sing := by
    intro p
    refine ⟨?_, ?_⟩
    · intro s hs _hin
      have hs' : s ⊆ {p.val} := by
        intro q hq
        have : q ∈ toFunFinset A B ({p} : Finset (StrictFunToken A B)) := hs hq
        rwa [toFunFinset_singleton] at this
      have hsub : funOutputUnion A B s ⊆ p.val.val.2 := by
        intro y hy
        rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
        have : q = p.val := Finset.mem_singleton.mp (hs' hq)
        cases this
        exact hy'
      exact B.con_subset p.val.property.2 hsub
    · intro s hs hE y hy
      rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
      rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      have hr' : r = p := Finset.mem_singleton.mp (hs hr)
      cases hr'
      have hEp : EmptyEntails A p.val.val.1 := by
        intro x hx
        exact hE x ((mem_funInputUnion A B).2
          ⟨p.val, (mem_toFunFinset A B).2 ⟨p, hr, rfl⟩, hx⟩)
      exact p.property hEp y hy'
  ent_con := by
    intro w p ⟨⟨hwFun, hwE⟩, hFunEnt⟩
    have hFunInsert : FunCon A B (insert p.val (toFunFinset A B w)) :=
      (functionSystem A B).ent_con hFunEnt
    have hFunInsert' : FunCon A B (toFunFinset A B (insert p w)) :=
      (toFunFinset_insert A B w p).symm ▸ hFunInsert
    refine ⟨hFunInsert', ?_⟩
    intro t ht hE
    if hp : p ∈ t then
      let t' := t.filter (· ≠ p)
      have ht_eq : insert p t' = t := insert_filter_ne_strict A B hp
      have ht'sub : t' ⊆ w := filter_ne_subset_of_subset_insert_strict A B ht
      have hE' : EmptyEntails A (p.val.val.1 ∪' funInputUnion A B (toFunFinset A B t')) := by
        rwa [← ht_eq, toFunFinset_insert, funInputUnion_insert] at hE
      have ⟨hEp, hEt'⟩ := (emptyEntails_funion A).1 hE'
      have hOutp : EmptyEntails B p.val.val.2 := p.property hEp
      have hOutt' : EmptyEntails B (funOutputUnion A B (toFunFinset A B t')) :=
        hwE t' ht'sub hEt'
      have : EmptyEntails B (p.val.val.2 ∪' funOutputUnion A B (toFunFinset A B t')) :=
        (emptyEntails_funion B).2 ⟨hOutp, hOutt'⟩
      rwa [← ht_eq, toFunFinset_insert, funOutputUnion_insert]
    else
      have ht' : t ⊆ w := by
        intro q hq
        have : q ∈ insert p w := ht hq
        rcases Finset.mem_insert.mp this with rfl | hqW
        · exact False.elim (hp hq)
        · exact hqW
      exact hwE t ht' hE
  ent_bot := by
    intro w hw
    refine ⟨hw, (functionSystem A B).ent_bot hw.1⟩
  ent_refl := by
    intro w p hw hp
    have hpFun : p.val ∈ toFunFinset A B w :=
      (mem_toFunFinset A B).2 ⟨p, hp, rfl⟩
    exact ⟨hw, (functionSystem A B).ent_refl hw.1 hpFun⟩
  ent_trans := by
    intro u v c hv hu hEnts ⟨_, hFunEnt⟩
    have hFunEnts : ∀ y ∈ toFunFinset A B u,
        FunEnt A B (toFunFinset A B v) y := by
      intro y hy
      rcases (mem_toFunFinset A B).1 hy with ⟨q, hq, rfl⟩
      exact (hEnts q hq).2
    have hFun : FunEnt A B (toFunFinset A B v) c.val :=
      (functionSystem A B).ent_trans hv.1 hu.1 hFunEnts hFunEnt
    exact ⟨hv, hFun⟩

end InfoSys

end DomainTheory.InformationSystems
