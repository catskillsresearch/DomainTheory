
module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrictToken_of_IsStrict

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

/-- Package a strict approximable map as an element of `|A →ₛ B|`. -/
def approxMap_toStrictElement (f : ApproximableMap A B) (hf : IsStrict A B f) :
    (strictFunctionSystem A B).Element where
  carrier := {p : StrictFunToken A B | f.rel p.val.val.1 p.val.val.2}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · exact funCon_of_approxMap A B f (toFunFinset A B Y) fun q hq => by
        rcases (mem_toFunFinset A B).1 hq with ⟨p, hp, rfl⟩
        exact hY (Finset.mem_coe.2 hp)
    · intro s hs hE
      have hrel : ∀ q ∈ toFunFinset A B s, f.rel q.val.1 q.val.2 := by
        intro q hq
        rcases (mem_toFunFinset A B).1 hq with ⟨p, hp, rfl⟩
        exact hY (Finset.mem_coe.2 (hs hp))
      have hin : funInputUnion A B (toFunFinset A B s) ∈ A.Con := by
        have hsub : ↑(funInputUnion A B (toFunFinset A B s)) ⊆ A.botElement.carrier :=
          fun x hx => emptyEntails_mem_botElement A (hE x (Finset.mem_coe.1 hx))
        exact A.botElement.consistent _ hsub
      have hIO := rel_input_output_union A B f (toFunFinset A B s) hrel hin
      exact (IsStrictToken_of_IsStrict A B f hf
        (p := mkFunToken A B (funInputUnion A B (toFunFinset A B s))
          (funOutputUnion A B (toFunFinset A B s)) hin (f.rel_cod hIO))
        hIO).out hE
  closed := by
    intro Y p hY hEnt
    obtain ⟨_, hFunEnt⟩ := hEnt
    obtain ⟨_, s, hs, hEntIn, hEntOut⟩ := hFunEnt
    have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := by
      intro q hq
      have hq' : q ∈ toFunFinset A B Y := hs hq
      rcases (mem_toFunFinset A B).1 hq' with ⟨r, hr, rfl⟩
      exact hY (Finset.mem_coe.2 hr)
    have hin_s : funInputUnion A B s ∈ A.Con :=
      A.con_subset
        (proposition_2_3_ii A p.val.property.1 (entSet_inputUnion_of_ent A B hEntIn))
        (subset_funion_right _ _)
    have hIO := rel_input_output_union A B f s hrel hin_s
    have hU : f.rel p.val.val.1 (funOutputUnion A B s) :=
      f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
        (proposition_2_3_iii B (f.rel_cod hIO)) p.val.property.1 (f.rel_cod hIO)
    exact f.mono hU (proposition_2_3_iii A p.val.property.1) hEntOut
      p.val.property.1 p.val.property.2

end InfoSys

end DomainTheory.InformationSystems
