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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.approxMap_toStrictElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictifyElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.insert_filter_ne_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.filter_ne_subset_of_subset_insert_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrictToken_of_IsStrict
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


/-- Every strict BOOL-map is `cond` of its values at true and false. -/
theorem condMap.unique (f : ApproximableMap boolSystem A) (hf : IsStrict boolSystem A f) :
    f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · intro hrel
    refine ⟨f.rel_dom hrel, f.rel_cod hrel, ?_, ?_, ?_⟩
    · intro hEmp
      have hsub : ↑u ⊆ boolSystem.botElement.carrier := fun t ht =>
        emptyEntails_mem_botElement boolSystem (hEmp t (Finset.mem_coe.1 ht))
      have hout : ↑v ⊆ (f.toElement boolSystem.botElement).carrier := by
        intro y hy
        refine ⟨u, hsub, f.mono hrel (proposition_2_3_iii boolSystem (f.rel_dom hrel))
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (f.rel_dom hrel) (A.con_sing y)⟩
      rw [hf] at hout
      exact fun y hy => mem_botElement_emptyEntails A (hout (Finset.mem_coe.2 hy))
    · intro hTru y hy
      have hEntU : boolSystem.EntSet {BoolToken.tru} u :=
        entSet_singleton_tru_of_ent_tru (f.rel_dom hrel) hTru
      refine ⟨{BoolToken.tru}, ?_, ?_⟩
      · exact boolSystem.subset_closure (boolSystem.con_sing _)
      · exact f.mono hrel hEntU
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (boolSystem.con_sing _) (A.con_sing y)
    · intro hFls y hy
      have hEntU : boolSystem.EntSet {BoolToken.fls} u :=
        entSet_singleton_fls_of_ent_fls (f.rel_dom hrel) hFls
      refine ⟨{BoolToken.fls}, ?_, ?_⟩
      · exact boolSystem.subset_closure (boolSystem.con_sing _)
      · exact f.mono hrel hEntU
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (boolSystem.con_sing _) (A.con_sing y)
  · intro ⟨hu, hv, hE, ht, hfl⟩
    rcases boolCon_trichotomy hu with hEmp | hTru | hFls
    · have hrel0 : f.rel u ∅ :=
        f.mono f.empty_rel (boolSystem.entSet_empty u) (A.entSet_empty ∅) hu A.con_empty
      exact f.mono hrel0 (proposition_2_3_iii boolSystem hu) (hE hEmp) hu hv
    · have hsub : ↑v ⊆ (f.toElement boolTrue).carrier := ht hTru
      obtain ⟨w, hw, hrelw⟩ := exists_rel_of_subset_image f boolTrue v hsub
      have hEntW : boolSystem.EntSet {BoolToken.tru} w := fun t ht' =>
        hw (Finset.mem_coe.2 ht')
      have hrelTru : f.rel {BoolToken.tru} v :=
        f.mono hrelw hEntW (proposition_2_3_iii A (f.rel_cod hrelw))
          (boolSystem.con_sing _) (f.rel_cod hrelw)
      have hEntU : boolSystem.EntSet u {BoolToken.tru} := fun t ht' => by
        have : t = .tru := Finset.mem_singleton.mp ht'
        subst this; exact hTru
      exact f.mono hrelTru hEntU (proposition_2_3_iii A hv) hu hv
    · have hsub : ↑v ⊆ (f.toElement boolFalse).carrier := hfl hFls
      obtain ⟨w, hw, hrelw⟩ := exists_rel_of_subset_image f boolFalse v hsub
      have hEntW : boolSystem.EntSet {BoolToken.fls} w := fun t ht' =>
        hw (Finset.mem_coe.2 ht')
      have hrelFls : f.rel {BoolToken.fls} v :=
        f.mono hrelw hEntW (proposition_2_3_iii A (f.rel_cod hrelw))
          (boolSystem.con_sing _) (f.rel_cod hrelw)
      have hEntU : boolSystem.EntSet u {BoolToken.fls} := fun t ht' => by
        have : t = .fls := Finset.mem_singleton.mp ht'
        subst this; exact hFls
      exact f.mono hrelFls hEntU (proposition_2_3_iii A hv) hu hv

end InfoSys
end DomainTheory.InformationSystems
