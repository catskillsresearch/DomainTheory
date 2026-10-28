module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.funCon_of_approxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.rel_input_output_union

@[expose] public section

namespace DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem approxMap_toElement.closed (f : ApproximableMap A B)
    (Y : Finset (FunToken A B)) (p : FunToken A B)
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2})
    (hEnt : (functionSystem A B).Ent Y p) :
    p ∈ {q : FunToken A B | f.rel q.val.1 q.val.2} := by
  obtain ⟨_hCon, s, hs, hEntIn, hEntOut⟩ := hEnt
  have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
    hY (Finset.mem_coe.2 (hs hq))
  have hin_s : funInputUnion A B s ∈ A.Con :=
    A.con_subset
      (proposition_2_3_ii A p.property.1 (entSet_inputUnion_of_ent A B hEntIn))
      (subset_funion_right _ _)
  have hIO := rel_input_output_union A B f s hrel hin_s
  have hU : f.rel p.val.1 (funOutputUnion A B s) :=
    f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
      (proposition_2_3_iii B (f.rel_cod hIO)) p.property.1 (f.rel_cod hIO)
  exact f.mono hU (proposition_2_3_iii A p.property.1) hEntOut p.property.1 p.property.2

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem approxMap_toElement.consistent (f : ApproximableMap A B)
    (Y : Finset (FunToken A B))
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2}) :
    Y ∈ (functionSystem A B).Con :=
  funCon_of_approxMap A B f Y fun _ hp => hY (Finset.mem_coe.2 hp)

end InfoSys
end

section
namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := approxMap_toElement.consistent A B f
  closed := approxMap_toElement.closed A B f

end InfoSys
end

end DomainTheory.InformationSystems
