module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}

/-- Relation recovered from a Scott-continuous map: `u f v ↔ ↑v ⊆ g(ū)`. -/
def ofScottContinuous (g : ScottContinuous A B) : ApproximableMap A B where
  rel u v := ∃ hu : u ∈ A.Con, v ∈ B.Con ∧ ↑v ⊆ (g.toFun (A.closure u hu)).carrier
  rel_dom := fun ⟨hu, _, _⟩ => hu
  rel_cod := fun ⟨_, hv, _⟩ => hv
  empty_rel := by
    refine ⟨A.con_empty, B.con_empty, ?_⟩
    intro b hb
    exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hb))
  union_right := by
    intro u v v' ⟨hu, hv, hsub⟩ ⟨_hu', hv', hsub'⟩
    refine ⟨hu, ?_, ?_⟩
    · have hsubUV : ↑(v ∪' v') ⊆ (g.toFun (A.closure u hu)).carrier := by
        intro b hb
        rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
        · exact hsub (Finset.mem_coe.2 h)
        · exact hsub' (Finset.mem_coe.2 h)
      exact (g.toFun (A.closure u hu)).consistent (v ∪' v') hsubUV
    · intro b hb
      rcases mem_funion.mp (Finset.mem_coe.1 hb) with h | h
      · exact hsub (Finset.mem_coe.2 h)
      · exact hsub' (Finset.mem_coe.2 h)
  mono := by
    intro u u' v v' ⟨hu, hv, hsub⟩ hEntUU' hEntVV' hu' hv'
    refine ⟨hu', hv', ?_⟩
    have hclos : A.closure u hu ≤ A.closure u' hu' :=
      A.closure_le_of_entSet hu hu' hEntUU'
    intro b hb
    have hEntb : B.Ent v b := hEntVV' b hb
    have hb_in : b ∈ (g.toFun (A.closure u hu)).carrier :=
      (g.toFun (A.closure u hu)).closed v b hsub hEntb
    exact g.mono hclos hb_in

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
