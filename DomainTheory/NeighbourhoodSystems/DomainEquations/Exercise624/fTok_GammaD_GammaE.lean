module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_fTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.fTok_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.mem_fTok_iUnion
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter_fst_subset_GammaD
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter_snd_subset_GammaE

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624


/-- **First equation of the double fixed point:** `fTok Γ_D Γ_E = Γ_D`, i.e. `tok(D + (D×E)) = Γ_D`
for `D = {Γ_D}`, `E = {Γ_E}`. -/
theorem fTok_GammaD_GammaE : fTok GammaD GammaE = GammaD := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_fTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_fTok _ _
    | succ m =>
        exact fTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

end Exercise624
end DomainTheory.NeighbourhoodSystems
