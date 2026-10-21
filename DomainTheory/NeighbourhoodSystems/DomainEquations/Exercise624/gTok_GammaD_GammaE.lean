/-ai
The second equation of the double fixed point holds: gTok of Gamma_D and Gamma_E equals Gamma_E.

A token of gTok of the two colimits lies, by single-stage additivity, in gTok of some stage, hence in the next second component of the iteration and so in Gamma_E. A token of Gamma_E lies at some stage. The zeroth stage is the empty string, which belongs to gTok. A later stage lies in gTok of the preceding components, and those components sit inside the colimits, so monotonicity places the token in gTok of the colimits.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_gTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.gTok_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.mem_gTok_iUnion
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter_fst_subset_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter_snd_subset_GammaE

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **Second equation of the double fixed point:** `gTok Γ_D Γ_E = Γ_E`, i.e. `tok(D + E) = Γ_E`. -/
theorem gTok_GammaD_GammaE : gTok GammaD GammaE = GammaE := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_gTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_gTok _ _
    | succ m =>
        exact gTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

end Exercise624
end DomainTheory.NeighbourhoodSystems
