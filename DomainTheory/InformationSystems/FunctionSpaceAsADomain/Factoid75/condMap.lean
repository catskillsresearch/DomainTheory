/-ai
The conditional map of elements x and y is the approximable map from the Boolean system that relates a consistent Boolean set u to a consistent set v when empty entailment of u implies empty entailment of v, entailment of true implies that v lies in x, and entailment of false implies that v lies in y. The empty relation holds because the empty set entails neither true nor false. Unions and monotonicity are checked by the trichotomy of a consistent Boolean set into the empty, true, and false cases, using that one Boolean point cannot satisfy both true and false.
ai-/
module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
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
          (botElement_le A x) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
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
          (botElement_le A y) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
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
